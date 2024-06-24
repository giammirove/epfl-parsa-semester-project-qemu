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
#include <omp.h>

/* net related imports */
#include <netinet/tcp.h>
#include <netdb.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <sys/types.h>
#define SA struct sockaddr

QEMU_PLUGIN_EXPORT int qemu_plugin_version = QEMU_PLUGIN_VERSION;
#define myprintf(...) /*printf(__VA_ARGS__)*/

static qemu_plugin_u64 insn_count;

static bool do_size;
static GArray *sizes;

/* quanta expressed in instruction number */
static uint64_t QUANTA = 0;
/* next quanta to reach expressed in instruction number */
/* current quanta id : 0,1,2,3,4,... */
// static int quanta_id = 0;
/* nodes that acked my quanta termination */
static bool *to_ack_quanta;
static bool *acked_quanta;
static int n_acked_quanta;
static int n_to_ack_quanta;
static int boot_sent = 0; /* already sent the message that we booted */

static int qmp_socket_fd = -1;
static int qmp_cap = 0;

static qemu_plugin_id_t qemu_plugin_id;

static uint64_t VCPUS = 0;
/* barrier counter, we can overshoot it */
static /*_Atomic*/ uint64_t barrier_sum;

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
static _Atomic int nodes_ready = 0;
/* node ready that went faster than me during the synchronization phase */
static _Atomic int nodes_ack_ready = 0;
/* number of threads that are blocked waiting for synchronization barrier */
/* path of the network config file */
static char *config_path = NULL;
static qflex_node_t *nodes;
static qflex_node_t server;
/* current qflex related variables state */
QflexPluginState *qflex_state;

enum HEADERS {
  RDY = 1,    /* node is ready */
  ARDY = 2,   /* ack node is ready */
  NC = 3,     /* new connection */
  BT = 4,     /* boot : DO NOT EDIT (used in afterboot script) */
  BBT = 5,    /* broadcast boot */
  PKT = 6,    /* ack packet */
  BEGIN = 7,  /* begin packet */
  ABEGIN = 8, /* ack begin packet */
  SN = 9,     /* snapshot packet */
  ASN = 10,   /* ack snapshot packet */
  DEL = 11,   /* start delivering packet */
  SNT = 12,   /* num sent packets */
};
#define NCPU 64
typedef struct {
  uint64_t next_quanta;
  uint64_t quanta_id;

  bool ready_sent;

  uint64_t counters[NCPU];
  uint64_t idle_counter;
  _Atomic uint64_t gcounter;

  // pthread_mutex_t idle_lock;
  // pthread_mutex_t barrier_lock;
  // pthread_cond_t barrier_cond;

  // pthread_mutex_t thread_lock;
  // pthread_cond_t thread_cond;
} qflex_lstate_t;

static qflex_lstate_t *qflex_lstate;

static void *qflex_server_connect_thread(void *args);
static void qflex_server_connect(QflexPluginState *state);
static void qflex_server_close(void);
static int qflex_send_ready(int n, int pkt_sent, bool is_ack);
static int qflex_send_snapshot(int n);
static int qflex_send_boot(void);
static int qflex_notify_packet(int dest_id);
static void qflex_begin_of_quanta(QflexPluginState *state);
static void qflex_start_simulation(QflexPluginState *state);
static void qflex_snapshot_init(void);
static void qflex_save_snapshot(qflex_lstate_t *lstate);
static int qflex_send_num_packet(int n, int pkt_sent);
static void *qflex_periodic_check(void *args);
static void *qflex_mips_counter(void *args);
static uint64_t qflex_compute_icount(qflex_lstate_t *lstate);

static inline int64_t qflex_get_clock(void *arg)
{
  QflexPluginState *state = arg;
  int64_t act = state->offset_time + (atomic_load(&state->clock) >> 10);
  if (act < 0) {
    printf("NOT GOOD%ld\n", act);
    printf("%ld\n", atomic_load(&state->clock));
    exit(5);
  }
  return act;
}
static inline int64_t qflex_update_clock(QflexPluginState *state) { return 0; }
#define MIN_INC 100000000
#define MAX_INC 1000000000
#define min(a, b) (a < b ? a : b)
#define max(a, b) (a < b ? b : a)
static inline void qflex_update_clock_by(QflexPluginState *state, int inc)
{
  int64_t cinc = inc >> 2;
  // cinc = max(min(cinc, MIN_INC), MAX_INC);
  cinc = min(cinc, MIN_INC);
  cinc = atomic_fetch_add(&state->clock, cinc);
}
/* used to pass the instruction count to the main qemu program */
static int64_t qflex_get_icount(void *state) { return 0; }

static int64_t qflex_can_send(void *arg)
{
  QflexPluginState *state = arg;
  qflex_lstate_t *lstate = state->lstate;
  if (state->can_count == 0 || state->stop != ST_F)
    return 0;
  if (qflex_compute_icount(lstate) >= lstate->next_quanta)
    return 0;

  return 1;
}

static void plugin_exit(qemu_plugin_id_t id, void *p) { qflex_server_close(); }

static void qflex_start_delivering(QflexPluginState *state)
{
  qflex_lstate_t *lstate = state->lstate;
  printf("START DELIVERING %ld\n", lstate->quanta_id);
  pthread_mutex_lock(&state->lock1);
  int pkt_sent = state->pkt_sent;
  state->is_delivering = true;
  pthread_mutex_unlock(&state->lock1);
  printf("sending %d\n", pkt_sent);
  qflex_send_num_packet(lstate->quanta_id, pkt_sent);
  if (state->pkt_receive != NULL) {
    state->pkt_receive(0);
  }
  printf("STOP DELIVERING %ld\n", lstate->quanta_id);
}
/* if this called has been called that means we reached the quanta and every
 * message has been received by everyone */
static void qflex_begin_of_quanta(QflexPluginState *state)
{
  qflex_lstate_t *lstate = state->lstate;
  myprintf("[%ld] SYNC %ld\n", lstate->quanta_id, state->pkt_sent);

  myprintf("ACQ BEG\n");
  /* unlock since pkt_receive could call mutex again */
  // pthread_mutex_unlock(&state->lock1);
  pthread_mutex_lock(&state->lock1);
  state->is_delivering = false;
  // printf("LOCK 4\n");
  // pthread_mutex_lock(&state->lock1);
  /* TODO: should it be atomic here ? */
  state->pkt_sent = 0;
  lstate->ready_sent = false;

  if (state->pkt_receive != NULL) {
    state->pkt_receive(0);
  }
  pthread_cond_broadcast(&state->cond1);

  /* reset */
  nodes_at_quanta = 0;
  n_acked_quanta = 0;
  for (int i = 0; i < n_nodes; ++i)
    acked_quanta[i] = false;
  // myprintf("-------------------------------------------\n\n");
  /* finalize update since from now on we cannot receive any more message from
   * previous quanta */
  ++lstate->quanta_id;
  nodes_ready = 0;
  nodes_ack_ready = 0;
  state->stop = ST_F;
  lstate->next_quanta = lstate->gcounter + QUANTA;
  pthread_mutex_unlock(&state->lock1);
  // printf("UNLOCK 9\n");
  myprintf("REL SEND\n");
}

static bool qflex_check_quanta_imprecise(QflexPluginState *state, int inc)
{
  qflex_lstate_t *lstate = state->lstate;
  uint64_t value = lstate->gcounter + lstate->idle_counter;
  qflex_update_clock_by(state, inc);
  if ((int64_t)(value) < 0) {
    printf("DAM BRO %ld\n", value);
  }
  uint64_t next = lstate->next_quanta;
  if (unlikely(value >= next) && !lstate->ready_sent) {
    state->stop = ST_N;
    // if (!lstate->ready_sent) {
    lstate->ready_sent = true;
    int pkt_sent = state->pkt_sent;
    int q_id = lstate->quanta_id;
    pthread_mutex_unlock(&state->lock1);
    // printf("UNLOCK 7\n");
    qflex_send_ready(q_id, pkt_sent, false);
    // }
    // else {
    //   pthread_mutex_unlock(&state->lock1);
    //   printf("UNLOCK 8\n");
    // }

    // pthread_mutex_lock(&lstate->barrier_lock);
    // /* next_quanta is only changed inside barrier_lock's mutex */
    // while (value >= lstate->next_quanta)
    //   pthread_cond_wait(&lstate->barrier_cond, &lstate->barrier_lock);
    //
    // pthread_mutex_unlock(&lstate->barrier_lock);
    return true;
  }
  pthread_mutex_unlock(&state->lock1);
  return false;
}

/* keeping this function as less as heavy as possible */
static void vcpu_insn_exec_before(unsigned int cpu_index, void *udata)
{
  QflexPluginState *state = udata;
  qflex_lstate_t *lstate = state->lstate;
  /* next_quanta is only changed inside barrier_lock's mutex */
  while (state->stop == ST_B) {
  }
  lstate->counters[cpu_index]++;
  // pthread_cond_broadcast(&lstate->thread_cond);
}

static void vcpu_tb_trans(qemu_plugin_id_t id, struct qemu_plugin_tb *tb)
{
  size_t n = qemu_plugin_tb_n_insns(tb);
  size_t i;

  for (i = 0; i < n; i++) {
    struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);

    qemu_plugin_register_vcpu_insn_exec_cb_qflex(insn, vcpu_insn_exec_before,
                                                 QEMU_PLUGIN_CB_NO_REGS,
                                                 (void *)qflex_state, NULL);
  }
}

static pthread_t idle_thread;
/* the "time" could faster while in idle, so it needs to be scaled somehow */
static void *qflex_idle_clock(void *args)
{
  QflexPluginState *state = args;
  qflex_lstate_t *lstate = state->lstate;
  // qflex_lstate_t *lstate = state->lstate;
  myprintf("IDLE TRHREAD STARTED\n");
  for (;;) {
    if (__sync_fetch_and_add(&state->idle_cpus, 0) == VCPUS) {
      // pthread_cond_broadcast(&lstate->thread_cond);
      ++lstate->idle_counter;
    }
  }

  myprintf("IDLE TRHREAD STOPPED\n");
  pthread_exit(EXIT_SUCCESS);
  return NULL;
}
/*
 * the problem seems to be that __sync_add_and_fetch does not atomically
 * increment idle_state (based on comparison with the main thread)
 *
 * UPDATE:
 * checking the source code and after some tests it seems that qemu not always
 * call vcpu_resume when we would expect it to be called,
 * therefore (at least for our usage) it is not fully reliable
 *
 * function that should call the callback
 *
 * void qemu_plugin_vcpu_resume_cb(CPUState *cpu)
 *  {
 *    if (cpu->cpu_index < plugin.num_vcpus) {
 *      plugin_vcpu_cb__simple(cpu, QEMU_PLUGIN_EV_VCPU_RESUME);
 *    }
 *  }
 *
 *  it seems that the condition is not satisfied always (during the boot in
 *  particular) and therefore resume is called fewer times that idle
 *
 *
 * QEMU emulator version 8.2.90 (v9.0.0-rc0-3-gf1ad3b43d1-dirty)
 *
 */
// static void vcpu_idle(qemu_plugin_id_t id, unsigned int cpu_index)
// {
//   (void)idle_lock;
// pthread_mutex_lock(&idle_lock);
// uint64_t in_idle = atomic_fetch_add(&cpu_in_idle, 1) + 1;
/* TODO: ideally you should stop only in that case, BUT it happens (probably
 * due to a faulty implementation by my side), that no CPU is either in idle
 * or running an instruction, therefore blocking indefinetely */
// if (++cpu_in_idle == VCPUS) {
// qflex_state->time_offset = get_current_clock() - get_qflex_clock();
/* WARNING: we have delay in this operation, so we are not 100% precise */
// idle_state = 1;
// int64_t i = __sync_add_and_fetch(&idle_state, 1);
// int64_t i2 = atomic_fetch_add(&idle_state2, 1) + 1;
// int64_t d = *(int *)qflex_state->dummy;
// // if (i != d)
// printf("[%d] IDLE %ld (%ld) (%d) - %ld - %ld\n", quanta_id, i, i2, n_nodes,
//        __sync_fetch_and_add(&blocked, 0), d);
// assert(i <= VCPUS);
// pthread_mutex_unlock(&idle_lock);
// }
// else {
//   pthread_mutex_unlock(&idle_lock);
// }
// }
// static int t = 0;
// static void vcpu_resume(qemu_plugin_id_t id, unsigned int cpu_index)
// {
//   printf("RES\n");
// pthread_mutex_lock(&idle_lock);
// __sync_fetch_and_sub(&idle_state, 1);
// int64_t i = __sync_sub_and_fetch(&idle_state, 1);
// int64_t i2 = atomic_fetch_sub(&idle_state2, 1) - 1;
// int64_t d = *(int *)qflex_state->dummy;
// if (i != d)
// printf("RESUME %ld (%ld) - %ld\n", i, i2, d);
// assert(i >= 0);
// if (i != d)
//   t++;
// assert(t < 1);
// pthread_mutex_unlock(&idle_lock);
// atomic_store(&idle_state, 0);
// atomic_fetch_sub(&cpu_in_idle, 1);
// if (--cpu_in_idle == 0) {
//   myprintf("RESUME\n");
//   idle_state = 0;
//   qflex_state->time_offset = 0;
// }
// pthread_mutex_unlock(&idle_lock);
// }

static void qflex_config_load(char *path)
{
  FILE *fp;
  char *line = NULL;
  size_t len = 0;
  ssize_t read;

  fp = fopen(realpath(path, NULL), "r");
  if (fp == NULL) {
    myprintf("Config file does not exist\n");
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
  myprintf("NODES: %d\n", n_nodes);
  myprintf("QUANTA: %ld\n", QUANTA);
  myprintf("MY ID: %d\n", node_id);
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
      myprintf("SERVER IP: %s - PORT: %d\n", server.ip, server.port);
    }
    else {
      nodes[c - 1].ip = ip;
      nodes[c - 1].port = port;
      myprintf("NODE IP: %s - PORT: %d\n", nodes[c - 1].ip, nodes[c - 1].port);
    }
    c++;
  }

  fclose(fp);
}

static void qflex_start_simulation(QflexPluginState *state)
{
  if (__sync_fetch_and_add(&state->can_count, 0) > 0)
    return;

  /*
   * it should be 0 at this time and even if it is not,
   * every time can_count is checked is done as (can_count == 0)
   * so it is not a problem
   */
  __sync_fetch_and_add(&state->can_count, 1);

  /* Register init, translation block and exit callbacks */
  qemu_plugin_register_vcpu_tb_trans_cb(qemu_plugin_id, vcpu_tb_trans);
  qemu_plugin_register_atexit_cb(qemu_plugin_id, plugin_exit, NULL);

  pthread_t t1, t2;
  pthread_create(&t1, NULL, qflex_periodic_check, qflex_state);
  pthread_create(&t2, NULL, qflex_mips_counter, qflex_state);
  /* disable due to the fact that resume_cb seems not to be reliable */
  // qemu_plugin_register_vcpu_idle_cb(qemu_plugin_id, vcpu_idle);
  // qemu_plugin_register_vcpu_resume_cb(qemu_plugin_id, vcpu_resume);

  int res = pthread_create(&idle_thread, NULL, qflex_idle_clock, state);
  /* no errors in creating the thread */
  assert(res == 0);
}

static void *qflex_server_connect_thread(void *args)
{
  QflexPluginState *state = args;
  qflex_lstate_t *lstate = state->lstate;
  int opt = true;
  struct sockaddr_in servaddr;
  int valread;
  int buf;

  // socket create and verification
  server.fd_out = socket(AF_INET, SOCK_STREAM, 0);
  if (server.fd_out == -1) {
    myprintf("socket creation failed...\n");
    exit(0);
  }
  myprintf("Socket successfully created..\n");
  bzero(&servaddr, sizeof(servaddr));

  if (setsockopt(server.fd_out, SOL_SOCKET, SO_REUSEADDR, (char *)&opt,
                 sizeof(opt)) < 0) {
    exit(EXIT_FAILURE);
  }

  servaddr.sin_family = AF_INET;
  servaddr.sin_addr.s_addr = inet_addr(server.ip);
  servaddr.sin_port = htons(server.port);

  if (connect(server.fd_out, (SA *)&servaddr, sizeof(servaddr)) != 0) {
    myprintf("Connection with the server failed\n");
    exit(EXIT_FAILURE);
  }
  /* sending my id */
  int msg[] = {NC, htonl(node_id)};
  int res = write(server.fd_out, &msg, 2 * sizeof(int));
  (void)res;

  for (;;) {

    if ((valread = read(server.fd_out, &buf, sizeof(buf))) == 0) {
      exit(EXIT_FAILURE);
    }
    else if (valread > 0) {
      int remote = 0;
      switch (buf) {
        /* I will get back ARDY when all messages sent are received */
      case ARDY:
        res = read(server.fd_out, &buf, sizeof(buf));
        (void)res;
        remote = htonl(buf);
        g_assert(remote == lstate->quanta_id);
        /* now we are sure that everyone is at the same quanta */
        qflex_begin_of_quanta(state);
        break;
      case DEL:
        res = read(server.fd_out, &buf, sizeof(buf));
        (void)res;
        remote = htonl(buf);
        g_assert(remote == lstate->quanta_id);
        qflex_start_delivering(state);
        break;
      case BBT:
        printf("EMULATION STARTS\n");
        // qflex_save_snapshot();
        qflex_start_simulation(state);
        break;
      case SN:
        res = read(server.fd_out, &buf, sizeof(buf));
        (void)res;
        remote = htonl(buf);
        // g_assert(remote == quanta_id);
        printf("SNAPSHOT %d\n", remote);
        qflex_save_snapshot(lstate);
        break;

      default:
        myprintf("UNK %d\n", valread);
      }
    }
    else {
      myprintf("[x] ERROR READING\n");
      exit(EXIT_FAILURE);
    }
  }
  close(server.fd_out);
  myprintf("exited");
  pthread_exit(NULL);
}
static void qflex_server_connect(QflexPluginState *state)
{
  pthread_t t1;
  int res = pthread_create(&t1, NULL, qflex_server_connect_thread, state);
  if (res) {
    myprintf("error %d\n", res);
    exit(EXIT_FAILURE);
  }
}

static void qflex_server_close(void)
{
  close(server.fd_out);
  close(qmp_socket_fd);
}

static int qflex_send_ready(int n, int pkt_sent, bool is_ack)
{
  printf("[%d] SENT READY\n", n);
  int type = is_ack ? ARDY : RDY;

  int arr[] = {type, htonl(n), htonl(pkt_sent)};
  // myprintf("PKT SENT %d IN %d\n", pkt_sent, quanta_id);
  if (write(server.fd_out, &arr, 3 * sizeof(int)) == -1) {
    myprintf("Can not send number to server\n");
    exit(EXIT_FAILURE);
  }

  return 0;
}
static int qflex_send_snapshot(int n)
{
  int type = ASN;

  int arr[] = {type, htonl(n)};
  if (write(server.fd_out, &arr, 2 * sizeof(int)) == -1) {
    myprintf("Can not send number to server\n");
    exit(EXIT_FAILURE);
  }

  return 0;
}

static int qflex_send_boot(void)
{
  if (boot_sent == 1)
    return 0;
  boot_sent = 1;
  myprintf("SEND BOOT\n");
  int type = BT;

  int arr[] = {type};
  if (write(server.fd_out, &arr, 1 * sizeof(int)) == -1) {
    myprintf("Can not send boot to server\n");
    exit(EXIT_FAILURE);
  }

  return 0;
}
static int qflex_send_num_packet(int n, int pkt_sent)
{
  int type = SNT;

  int arr[] = {type, htonl(n), htonl(pkt_sent)};
  // myprintf("PKT SENT %d IN %d\n", pkt_sent, quanta_id);
  if (write(server.fd_out, &arr, 3 * sizeof(int)) == -1) {
    myprintf("Can not send number to server\n");
    exit(EXIT_FAILURE);
  }

  return 0;
}

static int qflex_notify_packet(int pkt_size)
{

  /* I could receive a packet either before or after having reached my quanta
   * so I send a backup value of the quanta id */
  /* TODO: use param state */
  assert(qflex_lstate != NULL);
  int msg[] = {PKT, htonl(qflex_lstate->quanta_id), htonl(pkt_size)};
  if (write(server.fd_out, &msg, 3 * sizeof(int)) == -1) {
    myprintf("Can not send number to %d\n", dest_id);
    exit(EXIT_FAILURE);
  }
  return 0;
}

static void qflex_snapshot_init(void)
{
  if (qmp_socket_fd == -1) {
    struct sockaddr_in servaddr;

    // socket create and verification
    qmp_socket_fd = socket(AF_INET, SOCK_STREAM, 0);
    if (qmp_socket_fd == -1) {
      printf("socket creation failed...\n");
      exit(0);
    }
    else
      printf("Socket successfully created..\n");
    bzero(&servaddr, sizeof(servaddr));

    // assign IP, PORT
    servaddr.sin_family = AF_INET;
    servaddr.sin_addr.s_addr = inet_addr("127.0.0.1");
    servaddr.sin_port = htons(8000 + node_id);

    // connect the client socket to server socket
    if (connect(qmp_socket_fd, (SA *)&servaddr, sizeof(servaddr)) != 0) {
      printf("connection with the server failed...\n");
      exit(0);
    }
    else
      printf("connected to the server..\n");

    char cap[150];
    int res = read(qmp_socket_fd, cap, sizeof(cap));
    (void)res;
  }
}

static uint64_t qflex_compute_icount(qflex_lstate_t *lstate)
{
  uint64_t curr = 0;
  for (volatile int i = 0; i < NCPU; i++) {
    curr += lstate->counters[i];
  }
  lstate->gcounter = curr;
  return curr;
}

static void *qflex_periodic_check(void *args)
{
  QflexPluginState *state = args;
  qflex_lstate_t *lstate = state->lstate;
  uint64_t curr = 0, prev = 0;
  for (;;) {
    usleep(1);
    // pthread_mutex_lock(&lstate->thread_lock);
    // pthread_cond_wait(&lstate->thread_cond, &lstate->thread_lock);
    // pthread_mutex_unlock(&lstate->thread_lock);
    pthread_mutex_lock(&state->lock1);
    curr = (qflex_compute_icount(lstate) + lstate->idle_counter) - prev;
    prev = curr;
    qflex_check_quanta_imprecise(state, curr);
  }
  return NULL;
}
static void *qflex_mips_counter(void *args)
{
  QflexPluginState *state = args;
  qflex_lstate_t *lstate = state->lstate;
  uint64_t prev = 0;
  uint64_t max = 0;
  uint64_t prev_quanta = 0;
  (void)prev_quanta;
  for (;;) {
    sleep(1);
    // uint64_t curr = *counter;
    uint64_t curr = qflex_compute_icount(lstate);
    uint64_t m = curr - prev;
    if (m > max) {
      max = m;
    }
    // printf("%ld - %ld - %ld\n", (max / 1000000), (m / 1000000),
    //        lstate->quanta_id - prev_quanta);
    prev = curr;
    prev_quanta = lstate->quanta_id;
  }
  return NULL;
}

/*
 *  Assumption:
 *  qmp can be used only by qflex plugin
 *
 */
static void qflex_save_snapshot(qflex_lstate_t *lstate)
{

  printf("SAVE SNAPSHOT\n");
  char ress[1024];
  if (qmp_cap == 0) {
    qmp_cap = 1;
    char cap[500] = "{ \"execute\": \"qmp_capabilities\", \"arguments\": { "
                    "\"enable\": [ \"oob\" ] } }\0";
    int res = write(qmp_socket_fd, cap, strlen(cap));
    bzero(cap, sizeof(cap));
    res = read(qmp_socket_fd, ress, sizeof(ress));
    (void)res;
  }

  bzero(ress, sizeof(ress));
  char cap2[2048] =
      "{ \"execute\": \"snapshot-save\",\"arguments\": {\"job-id\": "
      "\"snapsave0\",\"tag\": \"my-snap\",\"vmstate\": \"disk0\",\"devices\": "
      "[\"disk0\", \"disk1\"]}}\0";
  int res = write(qmp_socket_fd, cap2, strlen(cap2));
  (void)res;
  res = read(qmp_socket_fd, ress, sizeof(ress));
  (void)res;

  for (;;) {
    bzero(ress, sizeof(ress));
    bzero(cap2, sizeof(cap2));
    strcpy(cap2, "{ \"execute\": \"query-jobs\"} \0");
    res = write(qmp_socket_fd, cap2, strlen(cap2));
    res = read(qmp_socket_fd, ress, sizeof(ress));
    (void)res;
    if (strstr(ress, "\"concluded\"") && strstr(ress, "\"snapsave0\"")) {
      break;
    }
    sleep(1);
  }

  qflex_send_snapshot(lstate->quanta_id);
  printf("TASK COMPLETED\n");
}

QEMU_PLUGIN_EXPORT int qemu_plugin_install(qemu_plugin_id_t id,
                                           const qemu_info_t *info, int argc,
                                           char **argv)
{
  qemu_plugin_id = id;
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

  qflex_config_load(config_path);

  // atomic_init(&barrier_sum, 0);
  barrier_sum = 0;

  insn_count =
      qemu_plugin_scoreboard_u64(qemu_plugin_scoreboard_new(sizeof(uint64_t)));

  qflex_state = malloc(sizeof(QflexPluginState));
  qflex_state->pkt_sent = 0;
  qflex_state->pkt_received = 0;
  qflex_state->pkt_receive = NULL;
  qflex_state->pkt_list_received = g_list_alloc();
  qflex_state->pkt_list_send = g_list_alloc();
  /* should be 0 at the beginning */
  qflex_state->n_nodes = n_nodes;
  qflex_state->can_count = 0;
  qflex_state->stop = ST_F;
  qflex_state->clock = 0;
  qflex_state->idle_cpus = 0;
  qflex_state->offset_time = 0;
  qflex_state->pkt_notify = qflex_notify_packet;
  qflex_state->get_clock = qflex_get_clock;
  qflex_state->get_icount = qflex_get_icount;
  qflex_state->send_boot = qflex_send_boot;
  qflex_state->can_send = qflex_can_send;

  qflex_lstate = malloc(sizeof(qflex_lstate_t));
  for (int i = 0; i < NCPU; i++) {
    qflex_lstate->counters[i] = 0;
  }

  qflex_state->lstate = qflex_lstate;
  pthread_mutexattr_t attr, attr_thread;
  pthread_mutexattr_init(&attr);
  pthread_mutexattr_init(&attr_thread);
  pthread_condattr_t attr_cond, attr_cond_thread;
  pthread_condattr_init(&attr_cond);
  pthread_condattr_init(&attr_cond_thread);
  /* so that a thread can lock a mutex multiple times (i.e. tap receive with a
   * retry could) */
  // pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_RECURSIVE);
  pthread_mutex_init(&qflex_state->lock1, &attr);
  pthread_mutex_init(&qflex_state->lock2, &attr);
  pthread_mutex_init(&qflex_state->lock3, &attr);

  pthread_cond_init(&qflex_state->cond1, &attr_cond);

  nodes_at_quanta = 0;
  qflex_lstate->next_quanta = QUANTA;

  // pthread_mutex_init(&qflex_lstate->idle_lock, &attr);
  // pthread_mutex_init(&qflex_lstate->barrier_lock, &attr);
  // pthread_cond_init(&qflex_lstate->barrier_cond, &attr_cond);

  // pthread_mutex_init(&qflex_lstate->thread_lock, &attr_thread);
  // pthread_cond_init(&qflex_lstate->thread_cond, &attr_cond_thread);

  qflex_lstate->quanta_id = 0;
  qflex_state->dummy = &node_id;
  /* see qflex_check_quanta */
  assert(VCPUS < QUANTA);

  to_ack_quanta = (bool *)malloc(n_nodes * sizeof(bool));
  acked_quanta = (bool *)malloc(n_nodes * sizeof(bool));
  for (int i = 0; i < n_nodes; ++i) {
    acked_quanta[i] = false;
    to_ack_quanta[i] = false;
  }
  n_acked_quanta = 0;
  n_to_ack_quanta = 0;

  qemu_plugin_register_qflex_state_cb(qemu_plugin_id, qflex_state);
  qflex_start_simulation(qflex_state);

  // qflex_snapshot_init();
  (void)qflex_snapshot_init;
  qflex_server_connect(qflex_state);
  return 0;
}
