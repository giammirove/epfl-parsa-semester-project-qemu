/*
 * Copyright (C) 2018, Emilio G. Cota <cota@braap.org>
 *
 * License: GNU GPL, version 2 or later.
 *   See the COPYING file in the top-level directory.
 */
#include <inttypes.h>
#include <assert.h>
#include <stdatomic.h>
#include <sys/time.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdio.h>
#include <glib.h>

#include <qemu-plugin.h>
#include "atomic.h"
#include "compiler.h"
#include "typedefs.h"
#include <pthread.h>

/* net related imports */
#include <netinet/tcp.h>
#include <netdb.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <sys/types.h>
#define SA struct sockaddr

QEMU_PLUGIN_EXPORT int qemu_plugin_version = QEMU_PLUGIN_VERSION;

static qemu_plugin_u64 insn_count;

static bool do_size;
static GArray *sizes;

/* quanta expressed in instruction number */
static uint64_t QUANTA = 0;
/* next quanta to reach expressed in instruction number */
static _Atomic uint64_t next_quanta = 0;
/* current quanta id : 0,1,2,3,4,... */
static int quanta_id = 0;
/* nodes that acked my quanta termination */
static bool *to_ack_quanta;
static bool *acked_quanta;
static int n_acked_quanta;
static int n_to_ack_quanta;

static uint64_t VCPUS = 0;
/* barrier counter, we can overshoot it */
static _Atomic uint64_t barrier_sum;
/* synchronized instruction counter, we can not overshoot it */
static _Atomic uint64_t atomic_sum;
static _Atomic uint64_t qflex_clock;
pthread_mutex_t barrier_lock = PTHREAD_MUTEX_INITIALIZER;
pthread_cond_t barrier_cond = PTHREAD_COND_INITIALIZER;
pthread_mutex_t pause_lock = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t ins_lock = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t sync_lock = PTHREAD_MUTEX_INITIALIZER;
static int64_t get_current_clock(void)
{
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1000000000LL + ts.tv_nsec;
}
static uint64_t get_qflex_clock(void) { return atomic_load(&barrier_sum); }
static uint64_t qflex_update_clock(void)
{
  return atomic_fetch_add(&barrier_sum, 1) + 1;
}
/* used to pass the instruction count to the main qemu program */
static uint64_t get_icount(void) { return atomic_load(&atomic_sum); }

static enum qemu_plugin_mem_rw rw = QEMU_PLUGIN_MEM_RW;

/* node struct */
typedef struct {
  int fd_out;
  int fd_in;
  char *ip;
  int port;
} qflex_node_t;
/* my node id */
static int node_id = -1;
/* number of nodes in the network */
/* using uint64_t gcc triggers an error */
static uint32_t n_nodes = 0;
/* number of nodes that reached the quanta */
static _Atomic int nodes_at_quanta = -1;
/* 1 = quanta reached */
static _Atomic int quanta_reached = 0;
static long long quanta_reached_time = 0;
static long long last_curr_time = 0;
static _Atomic int nodes_ready = 0;
/* node ready that went faster than me during the synchronization phase */
static _Atomic int buf_nodes_ready = 0;
static _Atomic int nodes_ack_ready = 0;
/* number of threads that are blocked waiting for synchronization barrier */
// static _Atomic int threads_blocked = 0;
static _Atomic int threads_blocked_cnt = 0;
/* path of the network config file */
static char *config_path = NULL;
static qflex_node_t *nodes;
static qflex_node_t server;
/* current qflex related variables state */
QflexPluginState *qflex_state;

enum HEADERS {
  RDY = 1,   /* node is ready */
  ARDY = 2,  /* ack node is ready */
  NC = 3,    /* new connection */
  BT = 4,    /* boot : DO NOT EDIT (used in afterboot script) */
  BBT = 5,   /* broadcast boot */
  PKT = 6,   /* ack packet */
  BEGIN = 7, /* ack packet */
  ABEGIN = 8 /* ack packet */
};

static void *qflex_server_connect_thread(void *args);
static void qflex_server_connect(void);
static void qflex_server_close(void);
static int qflex_send_ready(int n, int pkt_sent, bool is_ack);
static int qflex_send_begin(int n);
static int qflex_send_boot(void);
static int qflex_notify_packet(int dest_id);
static bool qflex_next_quanta(bool node_at_quanta, bool im_at_quanta, int src);
static bool qflex_check_ready(void);
static void qflex_move_to_next_quanta(void);
static void qflex_begin_of_quanta(void);
static void qflex_can_send(void);

/*
 * Initialise a new vcpu with reading the register list
 */
static void vcpu_init(qemu_plugin_id_t id, unsigned int vcpu_index)
{
  g_autoptr(GArray) reg_list = qemu_plugin_get_registers();
  g_autoptr(GByteArray) reg_value = g_byte_array_new();

  if (reg_list) {
    for (int i = 0; i < reg_list->len; i++) {
      qemu_plugin_reg_descriptor *rd =
          &g_array_index(reg_list, qemu_plugin_reg_descriptor, i);
      int count = qemu_plugin_read_register(rd->handle, reg_value);
      g_assert(count > 0);
    }
  }
}

/*
 *
 *
 */
static bool qflex_next_quanta(bool node_at_quanta, bool im_at_quanta, int src)
{
  pthread_mutex_lock(&sync_lock);
  int at_quanta = 0;
  if (node_at_quanta)
    at_quanta = atomic_fetch_add(&nodes_at_quanta, 1) + 1;
  else
    at_quanta = atomic_load(&nodes_at_quanta);

  printf("[%d] SITUA  %d -> %ld -> %ld : %ld\n", src, quanta_id,
         atomic_load(&next_quanta), atomic_load(&atomic_sum),
         atomic_load(&barrier_sum));

  uint64_t as = atomic_load(&atomic_sum);
  uint64_t nq = atomic_load(&next_quanta);
  /* check that we can move to next quanta */
  if (at_quanta < n_nodes
      /*atomic_load(&qflex_state->pkt_acked) !=
          atomic_load(&qflex_state->pkt_sent)  || */
  ) {
    pthread_mutex_unlock(&sync_lock);
    return false;
  }

  printf("[%d] SYNC COMPLETED %d -> %ld -> %ld\n", src, quanta_id, nq, as);
  // printf("MSG RECEIVED %d\n", g_list_length(qflex_state->pkt_list) - 1);
  // printf("MSG SENT %ld\n", qflex_state->pkt_sent);
  if (qflex_state->pkt_receive != NULL)
    qflex_state->pkt_receive(quanta_id);
  else {
    // printf("RECEIVE METHOD NOT SET\n");
  }
  /* the thread calling `qflex_next_quanta` is the only one allowed to be
   * blocked */
  // g_assert(atomic_load(&threads_blocked_cnt) == 1);

  /* reset */
  nodes_at_quanta = 0;
  n_acked_quanta = 0;
  for (int i = 0; i < n_nodes; ++i)
    acked_quanta[i] = false;
  /* move to next quanta */
  // printf("quanta updated -> %ld\n", (curr_quanta + 1) * QUANTA);
  pthread_cond_broadcast(&barrier_cond);
  // quanta_id++;
  atomic_fetch_add(&next_quanta, QUANTA);
  // pthread_mutex_lock(&barrier_lock);
  /* unlock all blocked threads */
  // atomic_store(&threads_blocked, 0);
  // pthread_mutex_unlock(&barrier_lock);
  // printf("UNPAUSED\n");
  // pthread_mutex_lock(&pause_lock);
  // qflex_state->vm_unpause(NULL);
  // pthread_mutex_unlock(&pause_lock);

  pthread_mutex_unlock(&sync_lock);
  return true;
}

static bool qflex_check_ready(void)
{
  // printf("CHECK READY %ld %ld\n", atomic_load(&qflex_state->pkt_acked),
  //        atomic_load(&qflex_state->pkt_sent));
  if (atomic_load(&quanta_reached) == 1 /* &&
      atomic_load(&qflex_state->pkt_acked) ==
          atomic_load(&qflex_state->pkt_sent) */) {
    // printf("SEND READY for %d\n", quanta_id);
    /* move to next quanta increments quanta_id */
    // qflex_move_to_next_quanta();
    qflex_send_ready(quanta_id, atomic_load(&qflex_state->pkt_sent), false);
    return true;
  }

  return false;
}

static void qflex_move_to_next_quanta(void)
{

  if (qflex_state->pkt_receive != NULL)
    qflex_state->pkt_receive(quanta_id);
  else {
    // printf("RECEIVE METHOD NOT SET\n");
  }
  atomic_store(&qflex_state->pkt_received, 0);
  atomic_store(&qflex_state->pkt_sent, 0);

  /* reset */
  nodes_at_quanta = 0;
  n_acked_quanta = 0;
  for (int i = 0; i < n_nodes; ++i)
    acked_quanta[i] = false;
  /* so that check_ready returns false */
  atomic_store(&quanta_reached, 0);
  // quanta_id++;
  // printf("[-] MOVE TO NEXT QUANTA -> %d\n", quanta_id);
  /* `next_quanta` has to be kept unchanged until the beginning of the nextinsn
   * quanta, since it works as barrier for my `vcpu_insn_exec_before`
   */
}

/* if this called has been called that means we reached the quanta and every
 * message has been received by everyone */
static void qflex_begin_of_quanta(void)
{
  pthread_mutex_lock(&qflex_state->lock2);
  long long curr_time = get_current_clock();
  qflex_move_to_next_quanta();
  // printf("[%d] SYNC COMPLETED at %lld\n", quanta_id - 1, curr_time);
  // printf("ELAPSED TIME %lld - %ld\n", (curr_time - last_curr_time),
  //        qflex_state->time_offset);
  // printf("-------------------------------------------\n\n");
  last_curr_time = curr_time;
  /* finalize update since from now on we cannot receive any more message from
   * previous quanta */
  quanta_id++;
  atomic_store(&nodes_ready, atomic_load(&buf_nodes_ready));
  atomic_store(&nodes_ack_ready, 0);
  atomic_store(&buf_nodes_ready, 0);
  pthread_mutex_unlock(&qflex_state->lock2);
  // qflex_state->vm_unpause(NULL);
  /* TODO: is it safe to send quanta_id with no protection? */
  qflex_send_begin(quanta_id);
}

/* from here on any kind of message can be sent (network packets, ready
 * messages, begin messages) */
static void qflex_can_send(void)
{
  pthread_mutex_lock(&qflex_state->lock1);
  atomic_store(&qflex_state->can_send, 1);
  pthread_mutex_unlock(&qflex_state->lock1);
  /*
   * unlock them now otherwise it could happend that:
   * all nodes already reach the next quanta, send the ready,
   * get aready, and send then begin, all that for quanta N+1,
   * without having received yet the abegin of quanta N
   */
  /* unlock threads */
  atomic_fetch_add(&next_quanta, QUANTA);
  pthread_mutex_lock(&barrier_lock);
  pthread_cond_broadcast(&barrier_cond);
  pthread_mutex_unlock(&barrier_lock);
}

/* blocking function */
static void qflex_check_quanta(void)
{
  uint64_t value = qflex_update_clock();
  uint64_t next = atomic_load(&next_quanta);
  if (value >= next) {
    if (value == next) {
      (void)quanta_reached_time;
      // quanta_reached_time = get_current_clock();
      pthread_mutex_lock(&qflex_state->lock1);
      atomic_store(&qflex_state->can_send, 0);
      atomic_store(&quanta_reached, 1);
      // qflex_state->vm_pause(NULL);
      // printf("QUANTA REACHED %ld at %lld\n", value, quanta_reached_time);
      // qflex_check_ready();
      (void)qflex_check_ready;
      int pkt_sent = atomic_load(&qflex_state->pkt_sent);
      pthread_mutex_unlock(&qflex_state->lock1);
      qflex_send_ready(quanta_id, pkt_sent, false);
    }

    pthread_mutex_lock(&barrier_lock);
    while (value > atomic_load(&next_quanta)) {
      pthread_cond_wait(&barrier_cond, &barrier_lock);
    }
    pthread_mutex_unlock(&barrier_lock);
  }
}

/* keeping this function as less as heavy as possible */
static void vcpu_insn_exec_before(unsigned int cpu_index, void *udata)
{
  /* update clock */

  if (atomic_load(&qflex_state->can_count) == 0)
    return;

  qflex_check_quanta();

  uint64_t s = atomic_fetch_add(&atomic_sum, 1) + 1;
  uint64_t n = atomic_load(&next_quanta);
  // printf("VALUE : %ld\n", s);
  if (s > n) {
    printf("BLOCK COUNT %d\n", atomic_load(&threads_blocked_cnt));
    printf("MORE THAN EXPECTED %ld - "
           "%ld\n\n----------------------------------------------\n\n",
           s, n);
    exit(EXIT_FAILURE);
  }
}

static void vcpu_mem(unsigned int cpu_index, qemu_plugin_meminfo_t meminfo,
                     uint64_t vaddr, void *udata)
{
  // if (do_haddr) {
  //     struct qemu_plugin_hwaddr *hwaddr;
  //     hwaddr = qemu_plugin_get_hwaddr(meminfo, vaddr);
  //     if (qemu_plugin_hwaddr_is_io(hwaddr)) {
  //         qemu_plugin_u64_add(io_count, cpu_index, 1);
  //     } else {
  //         qemu_plugin_u64_add(mem_count, cpu_index, 1);
  //     }
  // } else {
  // struct qemu_plugin_insn *insn = (udata);
  // uint32_t opcode = *((uint32_t *)qemu_plugin_insn_data(insn));
  // char *dis = qemu_plugin_insn_disas(insn);
  // printf("MEM READ %s\n", dis);
  // for (;;) {
  // }
  // qemu_plugin_u64_add(mem_count, cpu_index, 1);
  // }
}

static void vcpu_tb_trans(qemu_plugin_id_t id, struct qemu_plugin_tb *tb)
{
  size_t n = qemu_plugin_tb_n_insns(tb);
  size_t i;

  for (i = 0; i < n; i++) {
    struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);

    // uint64_t vaddr = qemu_plugin_insn_vaddr(insn);
    // qemu_plugin_register_vcpu_insn_exec_cb(insn, vcpu_insn_exec_before,
    //                                        QEMU_PLUGIN_CB_NO_REGS,
    //                                        GUINT_TO_POINTER(vaddr));
    qemu_plugin_register_vcpu_insn_exec_cb_qflex(
        insn, vcpu_insn_exec_before, QEMU_PLUGIN_CB_NO_REGS, insn, get_icount);

    (void)rw;
    (void)vcpu_mem;
    // qemu_plugin_register_vcpu_mem_cb(insn, vcpu_mem, QEMU_PLUGIN_CB_NO_REGS,
    // rw,
    //                                  insn);
  }
}

static pthread_t idle_thread;
static bool idle_created = false;
static _Atomic uint64_t cpu_in_idle = 0;
static _Atomic uint64_t idle_state = 0;
/* the "time" could faster while in idle, so it needs to be scaled somehow */
static void *qflex_idle_clock(void *args)
{
  printf("IDLE TRHREAD STARTED\n");
  for (;;) {
    if (atomic_load(&idle_state) == 1) {
      qflex_check_quanta();
      /* just to regulate time speed */
      // usleep(1);
    }

    /* we should stop updating the clock when quanta has been reached */
    // if (atomic_load(&quanta_reached) == 0) {
    //   qflex_update_clock();
    //   updated_during_idle++;
    //   usleep(1);
    // }
  }

  printf("IDLE TRHREAD STOPPED\n");
  pthread_exit(EXIT_SUCCESS);
  return NULL;
}
static void vcpu_idle(qemu_plugin_id_t id, unsigned int cpu_index)
{
  uint64_t in_idle = atomic_fetch_add(&cpu_in_idle, 1) + 1;
  (void)idle_state;
  (void)qflex_idle_clock;
  (void)idle_thread;
  if (in_idle == VCPUS) {
    // qflex_state->time_offset = get_current_clock() - get_qflex_clock();
    /* WARNING: we have delay in this operation, so we are not 100% precise */
    atomic_store(&idle_state, 1);
    if (!idle_created) {
      idle_created = true;
      int res = pthread_create(&idle_thread, NULL, qflex_idle_clock, NULL);
      if (res) {
        printf("error %d\n", res);
      }
    }
  }
}
static void vcpu_resume(qemu_plugin_id_t id, unsigned int cpu_index)
{
  atomic_store(&idle_state, 0);
  qflex_state->time_offset = 0;
  atomic_fetch_sub(&cpu_in_idle, 1);
}

static void qflex_config_load(char *path)
{
  FILE *fp;
  char *line = NULL;
  size_t len = 0;
  ssize_t read;

  fp = fopen(realpath(path, NULL), "r");
  if (fp == NULL) {
    printf("Config file does not exist\n");
    exit(-1);
  }

  /* number of nodes */
  n_nodes = 0;
  /* first cycle to get len */
  while ((read = getline(&line, &len, fp)) != -1) {
    n_nodes++;
  }
  n_nodes--;
  nodes = malloc(n_nodes * sizeof(qflex_node_t));
  printf("NODES: %d\n", n_nodes);
  printf("QUANTA: %ld\n", QUANTA);
  printf("MY ID: %d\n", node_id);
  fclose(fp);

  fp = fopen(realpath(path, NULL), "r");
  /* reset length, so starting to read file from BOF */
  len = 0;
  line = NULL;
  int c = 0;
  while ((read = getline(&line, &len, fp)) != -1) {
    char *ptr = strtok(line, ";");
    char *ip = malloc((strlen(ptr) - 1) * sizeof(char));
    strcpy(ip, ptr);
    ptr = strtok(NULL, ";");
    int port = atoi(ptr);
    /* first line is the server */
    if (c == 0) {
      server.ip = ip;
      server.port = port;
      printf("SERVER IP: %s - PORT: %d\n", server.ip, server.port);
    }
    else {
      nodes[c - 1].ip = ip;
      nodes[c - 1].port = port;
      printf("NODE IP: %s - PORT: %d\n", nodes[c - 1].ip, nodes[c - 1].port);
    }
    c++;
  }

  fclose(fp);
}

static void *qflex_server_connect_thread(void *args)
{
  int opt = true;
  struct sockaddr_in servaddr;
  int valread;
  int buf;

  // socket create and verification
  server.fd_out = socket(AF_INET, SOCK_STREAM, 0);
  if (server.fd_out == -1) {
    printf("socket creation failed...\n");
    exit(0);
  }
  else
    printf("Socket successfully created..\n");
  bzero(&servaddr, sizeof(servaddr));

  if (setsockopt(server.fd_out, SOL_SOCKET, SO_REUSEADDR, (char *)&opt,
                 sizeof(opt)) < 0) {
    exit(EXIT_FAILURE);
  }

  servaddr.sin_family = AF_INET;
  servaddr.sin_addr.s_addr = inet_addr(server.ip);
  servaddr.sin_port = htons(server.port);

  if (connect(server.fd_out, (SA *)&servaddr, sizeof(servaddr)) != 0) {
    printf("Connection with the server failed\n");
    exit(EXIT_FAILURE);
  }
  /* sending my id */
  int msg[] = {NC, htonl(node_id)};
  write(server.fd_out, &msg, 2 * sizeof(int));

  for (;;) {

    if ((valread = read(server.fd_out, &buf, sizeof(buf))) == 0) {
      exit(EXIT_FAILURE);
    }
    else if (valread > 0) {
      int remote = 0;
      switch (buf) {
        /* I will get back ARDY when all messages sent are received */
      case ARDY:
        read(server.fd_out, &buf, sizeof(buf));
        remote = htonl(buf);
        g_assert(remote == quanta_id);
        /* now we are sure that everyone is at the same quanta */
        qflex_begin_of_quanta();
        break;
      case BBT:
        printf("EMULATION STARTS\n");
        atomic_store(&qflex_state->can_count, 1);
        break;
      case ABEGIN:
        read(server.fd_out, &buf, sizeof(buf));
        remote = htonl(buf);
        g_assert(remote == quanta_id);
        qflex_can_send();
        break;

      default:
        printf("UNK %d\n", valread);
      }
    }
    else {
      printf("[x] ERROR READING\n");
      exit(EXIT_FAILURE);
    }
  }
  close(server.fd_out);
  printf("exited");
  pthread_exit(NULL);
}
static void qflex_server_connect(void)
{
  pthread_t t1;
  int res = pthread_create(&t1, NULL, qflex_server_connect_thread, NULL);
  if (res) {
    printf("error %d\n", res);
  }
}

static void qflex_server_close(void) { close(server.fd_out); }

static int qflex_send_ready(int n, int pkt_sent, bool is_ack)
{
  int type = is_ack ? ARDY : RDY;

  int arr[] = {type, htonl(n), htonl(pkt_sent)};
  // printf("PKT SENT %d IN %d\n", pkt_sent, quanta_id);
  if (write(server.fd_out, &arr, 3 * sizeof(int)) == -1) {
    printf("Can not send number to server\n");
    exit(EXIT_FAILURE);
  }

  return 0;
}
static int qflex_send_begin(int n)
{
  int type = BEGIN;

  int arr[] = {type, htonl(n)};
  if (write(server.fd_out, &arr, 2 * sizeof(int)) == -1) {
    printf("Can not send number to server\n");
    exit(EXIT_FAILURE);
  }

  return 0;
}

static int qflex_send_boot(void)
{
  int type = BT;

  int arr[] = {type};
  if (write(server.fd_out, &arr, 1 * sizeof(int)) == -1) {
    printf("Can not send boot to server\n");
    exit(EXIT_FAILURE);
  }

  return 0;
}

static int qflex_notify_packet(int dest_id)
{
  printf("NOTIFY %d\n", n_nodes);
  // g_assert(dest_id >= -1 && dest_id < n_nodes);

  /* I could receive a packet either before or after having reached my quanta
   * so I send a backup value of the quanta id */
  int msg[] = {PKT, htonl(quanta_id)};
  if (write(server.fd_out, &msg, 2 * sizeof(int)) == -1) {
    printf("Can not send number to %d\n", dest_id);
    exit(EXIT_FAILURE);
  }
  return 0;
}

static void plugin_exit(qemu_plugin_id_t id, void *p)
{
  // g_autoptr(GString) out = g_string_new(NULL);
  // int i;

  // if (do_size) {
  //   for (i = 0; i <= sizes->len; i++) {
  //     unsigned long *cnt = &g_array_index(sizes, unsigned long, i);
  //     if (*cnt) {
  //       g_string_append_printf(out, "len %d bytes: %ld insns\n", i, *cnt);
  //     }
  //   }
  // }
  // else {
  //   for (i = 0; i < qemu_plugin_num_vcpus(); i++) {
  //     g_string_append_printf(out, "cpu %d insns: %" PRIu64 "\n", i,
  //                            qemu_plugin_u64_get(insn_count, i));
  //   }
  //   g_string_append_printf(out, "total insns: %" PRIu64 " - %" PRIu64 "\n",
  //                          qemu_plugin_u64_sum(insn_count),
  //                          atomic_load(&atomic_sum));
  // }
  // qemu_plugin_outs(out->str);

  qemu_plugin_scoreboard_free(insn_count.score);
  g_array_free(sizes, TRUE);

  qflex_server_close();
}

QEMU_PLUGIN_EXPORT int qemu_plugin_install(qemu_plugin_id_t id,
                                           const qemu_info_t *info, int argc,
                                           char **argv)
{
  /* null terminated so 0 is not a special case */
  sizes = g_array_new(true, true, sizeof(unsigned long));
  VCPUS = info->system.max_vcpus;
  node_id = -1;

  for (int i = 0; i < argc; i++) {
    char *opt = argv[i];
    g_auto(GStrv) tokens = g_strsplit(opt, "=", 2);
    if (g_strcmp0(tokens[0], "sizes") == 0) {
      if (!qemu_plugin_bool_parse(tokens[0], tokens[1], &do_size)) {
        fprintf(stderr, "boolean argument parsing failed: %s\n", opt);
        return -1;
      }
    }
    else if (g_strcmp0(tokens[0], "quanta") == 0) {
      QUANTA = atoi((char *)tokens[1]);
    }
    else if (g_strcmp0(tokens[0], "node_id") == 0) {
      node_id = atoi((char *)tokens[1]);
    }
    else if (g_strcmp0(tokens[0], "config") == 0) {
      config_path = malloc(strlen((char *)tokens[1]) * sizeof(char));
      strcpy(config_path, (char *)tokens[1]);
    }
    else {
      fprintf(stderr, "option parsing failed: %s\n", opt);
      return -1;
    }
  }

  if (node_id == -1) {
    fprintf(stderr, "%s\n", "Node's id is missing --id");
    return -1;
  }
  if (config_path == NULL) {
    fprintf(stderr, "%s\n", "Config path is invalid");
    return -1;
  }

  atomic_init(&barrier_sum, 0);

  insn_count =
      qemu_plugin_scoreboard_u64(qemu_plugin_scoreboard_new(sizeof(uint64_t)));

  qflex_state = malloc(sizeof(QflexPluginState));
  atomic_store(&qflex_state->pkt_sent, 0);
  atomic_store(&qflex_state->pkt_received, 0);
  atomic_store(&qflex_state->pkt_acked, 0);
  qflex_state->pkt_receive = NULL;
  qflex_state->pkt_list_received = g_list_alloc();
  qflex_state->pkt_list_send = g_list_alloc();
  /* should be 0 at the beginning */
  qflex_state->can_count = 1;
  qflex_state->can_send = 1;
  qflex_state->time_offset = 0;
  qflex_state->pkt_notify = qflex_notify_packet;
  qflex_state->get_qflex_clock = get_qflex_clock;
  qflex_state->get_qflex_icount = get_icount;
  qflex_state->send_boot = qflex_send_boot;
  pthread_mutex_init(&qflex_state->lock1, NULL);
  pthread_mutex_init(&qflex_state->lock2, NULL);
  pthread_mutex_init(&qflex_state->lock3, NULL);
  last_curr_time = quanta_reached_time = 0;

  /* Register init, translation block and exit callbacks */
  qemu_plugin_register_qflex_state_cb(id, qflex_state);
  qemu_plugin_register_vcpu_init_cb(id, vcpu_init);
  qemu_plugin_register_vcpu_tb_trans_cb(id, vcpu_tb_trans);
  qemu_plugin_register_atexit_cb(id, plugin_exit, NULL);
  qemu_plugin_register_vcpu_idle_cb(id, vcpu_idle);
  qemu_plugin_register_vcpu_resume_cb(id, vcpu_resume);

  nodes_at_quanta = 0;
  next_quanta = QUANTA;
  quanta_id = 0;
  qflex_state->dummy = &quanta_id;
  qflex_config_load(config_path);

  to_ack_quanta = (bool *)malloc(n_nodes * sizeof(bool));
  acked_quanta = (bool *)malloc(n_nodes * sizeof(bool));
  for (int i = 0; i < n_nodes; ++i) {
    acked_quanta[i] = false;
    to_ack_quanta[i] = false;
  }
  n_acked_quanta = 0;
  n_to_ack_quanta = 0;

  // qflex_server_connect_thread(NULL);
  qflex_server_connect();
  (void)qflex_next_quanta;
  (void)qflex_clock;
  return 0;
}
