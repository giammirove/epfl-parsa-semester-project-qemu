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

#define NCPU 64
/* adjust based on what you want */
#define IDLE_INCREMENT 32

static bool do_size;
static GArray *sizes;

/* quanta expressed in instruction number */
static uint64_t QUANTA = 0;
/* next quanta to reach expressed in instruction number */
/* current quanta id : 0,1,2,3,4,... */
// static int quanta_id = 0;
/* nodes that acked my quanta termination */
static int boot_sent = 0; /* already sent the message that we booted */

static int qmp_socket_fd = -1;
static int qmp_cap = 0;

static qemu_plugin_id_t qemu_plugin_id;

static uint64_t VCPUS = 0;
/* barrier counter, we can overshoot it */
static uint64_t barrier_sum;

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
static  int nodes_at_quanta = -1;
/* 1 = quanta reached */
static int nodes_ready = 0;
/* node ready that went faster than me during the synchronization phase */
static int nodes_ack_ready = 0;
/* number of threads that are blocked waiting for synchronization barrier */
/* path of the network config file */
static char *config_path = NULL;
static qflex_node_t *nodes;
static qflex_node_t server;
/* current qflex related variables state */
QflexPluginState *qflex_state;
FILE *fptr;


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
typedef struct {
  uint64_t next_quanta;
  uint64_t quanta_id;

  bool ready_sent;

  uint64_t counters[NCPU];
  uint64_t idle_counters[NCPU];
  _Atomic uint64_t is_idle[NCPU];
  uint64_t idle_counter;
  bool vcpu_done[NCPU];
  uint64_t gcounter;

  int64_t start_sync; 
  int64_t vtime;
  int64_t vtime_ns;

  pthread_mutex_t idle_lock;
  pthread_mutex_t barrier_lock;
  pthread_cond_t barrier_cond;

  int64_t blocked_time; /* ts when synchronization begins */
  int64_t cost_time; /* synchronization cost in time */
} qflex_lstate_t;

pthread_barrier_t       barrier;
pthread_barrierattr_t   barrier_attr;
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
static void qflex_save_snapshot(QflexPluginState *state);
static int qflex_send_num_packet(int n, int pkt_sent, int pkt_recv);
static void *qflex_mips_counter(void *args);
/* icount + idle time */
static uint64_t qflex_compute_time(qflex_lstate_t *lstate);
/* only icount */
static uint64_t qflex_compute_icount(qflex_lstate_t *lstate);
static int64_t qflex_get_real_clock(void);

static int64_t qflex_get_real_clock(void){
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1000000000LL + ts.tv_nsec;
}

static int64_t qflex_get_clock(void *arg){
  QflexPluginState *state = arg;
  qflex_lstate_t *lstate = state->lstate;
  lstate->vtime_ns++;
  int64_t t = lstate->vtime + state->offset_time + lstate->vtime_ns;
  if (t < 0) {
	  lstate->vtime = 0;
	  return state->offset_time + lstate->vtime_ns;
  }
  return t;
}
static void qflex_inc_clock(void *arg, int64_t inc){
  qflex_lstate_t *lstate = arg;
  inc <<= 6;
  int64_t v = lstate->vtime;
  lstate->vtime_ns  = 0;
  if (v + inc < 0) {
	printf("OVERFLOW\n");
	lstate->vtime = inc;
  } else {
	lstate->vtime += inc;
  }
}

static int qflex_can_send(void *arg)
{
  QflexPluginState *state = arg;
  qflex_lstate_t *lstate = state->lstate;
  if (state->stop != ST_F || qflex_compute_time(lstate) >= lstate->next_quanta)
    return 0;

  return 1;
}

static void plugin_exit(qemu_plugin_id_t id, void *p) { 
   fclose(fptr);
   printf("COST TIME %ld\n", qflex_lstate->cost_time);
   qflex_server_close();
}

static void qflex_start_delivering(QflexPluginState *state)
{
  qflex_lstate_t *lstate = state->lstate;
  pthread_mutex_lock(&state->lock1);
  state->is_delivering = true;
  pthread_mutex_unlock(&state->lock1);
  /* pkt_receive all flush everything so the number of packet sent could change
   */
  int recv = 0;
  if (state->pkt_receive != NULL) {
    state->pkt_receive(0);
    recv = state->pkt_received;
  }
  qflex_send_num_packet(lstate->quanta_id, state->pkt_sent, recv);
}
/* if this called has been called that means we reached the quanta and every
 * message has been received by everyone */
static void qflex_begin_of_quanta(QflexPluginState *state)
{
  qflex_lstate_t *lstate = state->lstate;

  pthread_mutex_lock(&state->lock1);
  state->is_delivering = false;
  // pthread_mutex_lock(&state->lock1);
  state->pkt_sent = 0;
  state->pkt_received = 0;
  lstate->ready_sent = false;

  /* reset */
  nodes_at_quanta = 0;
  /* finalize update since from now on we cannot receive any more message from
   * previous quanta */
  ++lstate->quanta_id;
  nodes_ready = 0;
  nodes_ack_ready = 0;

  for (int i = 0; i < VCPUS; ++i)
	lstate->vcpu_done[i] = false;

  lstate->cost_time += qflex_get_real_clock() - lstate->blocked_time;
  state->stop = ST_F;
  //pthread_mutex_lock(&lstate->barrier_lock);
  lstate->next_quanta += QUANTA;
  pthread_cond_broadcast(&lstate->barrier_cond);
  pthread_mutex_unlock(&state->lock1);
}

static void qflex_reached_quanta(QflexPluginState *state, uint64_t id, bool from_idle)
{
  if (state->synchro == 0)
	  return;
  pthread_mutex_lock(&state->lock1);
  qflex_lstate_t *lstate = state->lstate;
  lstate->vcpu_done[id] = true;
  if (state->stop != ST_F) {
    goto waiting;
  }
state->stop = ST_N;
lstate->ready_sent = true;
int pkt_sent = state->pkt_sent;
int q_id = lstate->quanta_id;
qflex_send_ready(q_id, pkt_sent, false);

waiting: 
  /* next_quanta is only changed inside barrier_lock's mutex */
  if (!from_idle && (lstate->counters[id] + lstate->idle_counters[id]) >=
         lstate->next_quanta && state->snap == 0)
    pthread_cond_wait(&lstate->barrier_cond, &state->lock1);

  pthread_mutex_unlock(&state->lock1);
}

/* keeping this function as less as heavy as possible */
static void vcpu_insn_exec_before(unsigned int cpu_index, void *udata)
{
  QflexPluginState *state = udata;
  if (state->can_count == 0) {
    return;
  }
  qflex_lstate_t *lstate = state->lstate;
  int64_t sum =
      (++lstate->counters[cpu_index]) + lstate->idle_counters[cpu_index];
  qflex_inc_clock(lstate, 1);
  if (sum >= lstate->next_quanta) {
    qflex_reached_quanta(state, cpu_index, false);
  }
}

static void vcpu_tb_trans(qemu_plugin_id_t id, struct qemu_plugin_tb *tb)
{
  size_t n = qemu_plugin_tb_n_insns(tb);
  size_t i;

  for (i = 0; i < n; i++) {
    struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);

    qemu_plugin_register_vcpu_insn_exec_cb(insn, vcpu_insn_exec_before,
                                                 QEMU_PLUGIN_CB_NO_REGS,
                                                 (void*)qflex_state);
  }
}

static pthread_t idle_thread;
/* the "time" could faster while in idle, so it needs to be scaled somehow */
static void *qflex_idle_clock(void *args)
{
  QflexPluginState *state = args;
  qflex_lstate_t *lstate = state->lstate;
  // qflex_lstate_t *lstate = state->lstate;
  int i = 0;
  for (;;) {
    for (i = 0; i < VCPUS; ++i) {
      if (lstate->is_idle[i] == true) {
	      /* 
	       * if one node is in idle and the other(s) not, we need to be careful that being in idle do not impact the performances, since the counter now is based on thread (it could be put to sleep, I could be slow, etc.)
	       */
	if (lstate->vcpu_done[i] == false) {
	  lstate->idle_counters[i] += IDLE_INCREMENT;
	  qflex_inc_clock(lstate, IDLE_INCREMENT);
	}
        int64_t sum = lstate->counters[i] + lstate->idle_counters[i];
        if (sum >= lstate->next_quanta) {
          qflex_reached_quanta(state, i, true);
	}
      }
    }
  }

  myprintf("IDLE TRHREAD STOPPED\n");
  pthread_exit(EXIT_SUCCESS);
  return NULL;
}

static void vcpu_idle(qemu_plugin_id_t id, unsigned int cpu_index)
{
  if (qflex_state == NULL || qflex_state->lstate == NULL)
	  return;
  qflex_lstate_t *lstate = qflex_state->lstate;
  lstate->is_idle[cpu_index] = true;
}
static void vcpu_resume(qemu_plugin_id_t id, unsigned int cpu_index)
{
  if (qflex_state == NULL || qflex_state->lstate == NULL)
	  return;
  qflex_lstate_t *lstate = qflex_state->lstate;
  lstate->is_idle[cpu_index] = false;
}

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
  if (state->can_count > 0)
    return;

  /*
   * it should be 0 at this time and even if it is not,
   * every time can_count is checked is done as (can_count == 0)
   * so it is not a problem
   */
  state->can_count = 1;


  pthread_t t1;
  pthread_create(&t1, NULL, qflex_mips_counter, qflex_state);
  (void)vcpu_idle;
  (void)vcpu_resume;
  (void)idle_thread;

  int res = pthread_create(&idle_thread, NULL, qflex_idle_clock, state);
  /* no errors in creating the thread */
  assert(res == 0);
}

static void *qflex_server_connect_thread(void *args)
{
  QflexPluginState *state = args;
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
        /* now we are sure that everyone is at the same quanta */
        qflex_begin_of_quanta(state);
        break;
      case DEL:
        res = read(server.fd_out, &buf, sizeof(buf));
        (void)res;
        remote = htonl(buf);
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
        printf("SNAPSHOT %d\n", remote);
        qflex_save_snapshot(state);
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
    printf("error %d\n", res);
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
  int type = is_ack ? ARDY : RDY;

  int arr[] = {type, htonl(n), htonl(pkt_sent)};
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
static int qflex_send_num_packet(int n, int pkt_sent, int pkt_recv)
{
  int type = SNT;

  int arr[] = {type, htonl(n), htonl(pkt_sent), htonl(pkt_recv)};
  if (write(server.fd_out, &arr, 4 * sizeof(int)) == -1) {
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

static uint64_t qflex_compute_time(qflex_lstate_t *lstate)
{
  uint64_t curr = 0;
  for (int i = 0; i < VCPUS; i++) {
    curr += lstate->counters[i] + lstate->idle_counters[i];
  }
  return curr;
}
static uint64_t qflex_compute_icount(qflex_lstate_t *lstate)
{
  uint64_t curr = 0;
  for (volatile int i = 0; i < VCPUS; i++) {
    curr += lstate->counters[i];
  }
  return curr;
}

static void *qflex_mips_counter(void *args)
{
  QflexPluginState *state = args;
  qflex_lstate_t *lstate = state->lstate;
  uint64_t prev = 0;
  uint64_t max = 0;
  uint64_t prev_quanta = 0;
  (void)prev_quanta;
  (void)qflex_compute_icount;
  int t = 0;
  for (;;) {
    sleep(1);
    t++;
    uint64_t curr = qflex_compute_icount(lstate);
    uint64_t m = curr - prev;
    if (m > max) {
      max = m;
    }
    printf("%d - %ld - %ld - %ld\n", t, (max / 1000000), (m / 1000000), lstate->cost_time);
    fprintf(fptr, "%ld\n", m);
    prev = curr;
  }
  return NULL;
}

/*
 *  Assumption:
 *  qmp can be used only by qflex plugin
 *
 */
static void qflex_save_snapshot(QflexPluginState *state)
{
  state->snap = 1;
  qflex_lstate_t *lstate = state->lstate;
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
  char cap2[2048];
  sprintf(cap2, "{ \"execute\": \"snapshot-save-qflex\",\"arguments\": {\"job-id\": \"snapsave-%ld\", \"tag\": \"snap-%ld\"}}",lstate->quanta_id, lstate->quanta_id);
  int res = write(qmp_socket_fd, cap2, strlen(cap2));
  (void)res;
  res = read(qmp_socket_fd, ress, sizeof(ress));
    printf("%s\n", ress);
  (void)res;


  for (;;) {
    bzero(ress, sizeof(ress));
    bzero(cap2, sizeof(cap2));
    strcpy(cap2, "{ \"execute\": \"query-jobs\"} \0");
    res = write(qmp_socket_fd, cap2, strlen(cap2));
  pthread_mutex_lock(&state->lock1);
  pthread_cond_broadcast(&lstate->barrier_cond);
  pthread_mutex_unlock(&state->lock1);
    printf("send req %d\n", res);
    res = read(qmp_socket_fd, ress, sizeof(ress));
    (void)res;
    printf("%s\n", ress);
    /* assumption one job at time */
    if (strstr(ress, "\"concluded\"")) {
      break;
    }
    sleep(1);
  }
  state->snap = 0;

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
  int synchro = 1;

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
    else if (g_strcmp0(tokens[0], "synchro") == 0) {
      synchro = atoi((char *)tokens[1]);
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


  fptr = fopen("mips.txt", "w");
  qflex_config_load(config_path);

  barrier_sum = 0;

  qflex_state = malloc(sizeof(QflexPluginState));
  qflex_state->pkt_sent = 0;
  qflex_state->pkt_received = 0;
  qflex_state->pkt_receive = NULL;
  qflex_state->pkt_list_received = g_list_alloc();
  qflex_state->pkt_list_send = g_list_alloc();
  /* should be 0 at the beginning */
  qflex_state->n_nodes = n_nodes;
  qflex_state->can_count = 0;
  qflex_state->snap = 0;
  qflex_state->stop = ST_F;
  qflex_state->clock = 0;
  qflex_state->idle_cpus = 0;
  qflex_state->offset_time = 0;
  qflex_state->synchro = synchro;
  qflex_state->pkt_notify = qflex_notify_packet;
  qflex_state->get_clock = qflex_get_clock;
  qflex_state->get_icount = NULL;
  qflex_state->send_boot = qflex_send_boot;
  qflex_state->can_send = qflex_can_send;

  qflex_lstate = malloc(sizeof(qflex_lstate_t));
  for (int i = 0; i < VCPUS; i++) {
    qflex_lstate->counters[i] = 0;
    qflex_lstate->idle_counters[i] = 0;
    qflex_lstate->vcpu_done[i] = false;
  }
  qflex_lstate->vtime = 0;
  qflex_lstate->vtime_ns = 0;
  qflex_lstate->cost_time = 0;

  qflex_state->lstate = qflex_lstate;
  pthread_mutexattr_t attr, attr_thread;
  pthread_mutexattr_init(&attr);
  pthread_mutexattr_init(&attr_thread);
  pthread_condattr_t attr_cond, attr_cond_thread;
  pthread_condattr_init(&attr_cond);
  pthread_condattr_init(&attr_cond_thread);

  pthread_mutex_init(&qflex_lstate->idle_lock, &attr);
  pthread_mutex_init(&qflex_lstate->barrier_lock, &attr);
  pthread_cond_init(&qflex_lstate->barrier_cond, &attr_cond);

  int ret, pshared;
    ret = pthread_barrierattr_init(&barrier_attr);
    (void)ret;
    pthread_barrierattr_getpshared(&barrier_attr, &pshared);
    pthread_barrier_init(&barrier, &barrier_attr, VCPUS+1);

  /* so that a thread can lock a mutex multiple times (i.e. tap receive with a
   * retry could) */
  // pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_RECURSIVE);
  pthread_mutex_init(&qflex_state->lock1, &attr);
  pthread_mutex_init(&qflex_state->lock2, &attr);
  pthread_mutex_init(&qflex_state->lock3, &attr);

  pthread_cond_init(&qflex_state->cond1, &attr_cond);

  nodes_at_quanta = 0;
  qflex_lstate->next_quanta = QUANTA;

  qflex_lstate->quanta_id = 0;
  qflex_state->dummy = &node_id;
  /* see qflex_check_quanta */
  assert(VCPUS < QUANTA);

  qemu_plugin_register_qflex_state_cb(qemu_plugin_id, qflex_state);
  /* Register init, translation block and exit callbacks */
  qemu_plugin_register_vcpu_tb_trans_cb(qemu_plugin_id, vcpu_tb_trans);
  qemu_plugin_register_atexit_cb(qemu_plugin_id, plugin_exit, NULL);
  qemu_plugin_register_vcpu_idle_cb(qemu_plugin_id, vcpu_idle);
  qemu_plugin_register_vcpu_resume_cb(qemu_plugin_id, vcpu_resume);

  qflex_snapshot_init();
  (void)qflex_snapshot_init;
  (void)qflex_server_connect;
  qflex_server_connect(qflex_state);
  return 0;
}
