/*
 * Copyright (C) 2018, Emilio G. Cota <cota@braap.org>
 *
 * License: GNU GPL, version 2 or later.
 *   See the COPYING file in the top-level directory.
 */
#include <inttypes.h>
#include <assert.h>
#include <stdatomic.h>
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

/* server related imports */
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
/* current quanta */
static int curr_quanta = 0;
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
pthread_mutex_t barrier_lock = PTHREAD_MUTEX_INITIALIZER;
pthread_cond_t barrier_cond = PTHREAD_COND_INITIALIZER;
pthread_mutex_t pause_lock = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t ins_lock = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t sync_lock = PTHREAD_MUTEX_INITIALIZER;
/* used to pass the instruction count to the main qemu program */
static uint64_t test_fun(void) { return atomic_load(&barrier_sum); }

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
/* number of threads that are blocked waiting for synchronization barrier */
// static _Atomic int threads_blocked = 0;
static _Atomic int threads_blocked_cnt = 0;
/* path of the network config file */
static char *config_path = NULL;
/* fd of the server I host */
static int serverfd;
static qflex_node_t *nodes;
/* number of active incoming connections, used as barrier before qemu starts */
static int incoming_connections = 0;
/* current qflex related variables state */
QflexPluginState *qflex_state;

/* count number of nodes that finished to boot */
static int nodes_at_boot = 0;

enum HEADERS {
  QT = 1,  /* quanta termination */
  AQT = 2, /* ack quanta termination */
  NC = 3,  /* new connection */
  BT = 4,  /* boot : DO NOT EDIT (used in afterboot script) */
  BBT = 5, /* broadcast boot */
  ACK = 6  /* ack packet */
};

static void *qflex_server_open_thread(void *args);
static void qflex_server_open(void);
static void qflex_clients_open(void);
static void qflex_server_close(void);
static void qflex_clients_close(void);
static int qflex_send_message(char *msg);
static int qflex_send_self(int msg);
static int qflex_send_ack(int dest_id);
static int qflex_send_quanta_termination(int n);
static int qflex_notify_packet(int dest_id);
static bool qflex_next_quanta(bool node_at_quanta, bool im_at_quanta, int src);

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

  printf("[%d] SITUA  %d -> %ld -> %ld : %ld\n", src, curr_quanta,
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

  printf("[%d] SYNC COMPLETED %d -> %ld -> %ld\n", src, curr_quanta, nq, as);
  // printf("MSG RECEIVED %d\n", g_list_length(qflex_state->pkt_list) - 1);
  // printf("MSG SENT %ld\n", qflex_state->pkt_sent);
  if (qflex_state->pkt_receive != NULL)
    qflex_state->pkt_receive(curr_quanta);
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
  curr_quanta++;
  atomic_fetch_add(&next_quanta, QUANTA);
  // pthread_mutex_lock(&barrier_lock);
  /* unlock all blocked threads */
  // atomic_store(&threads_blocked, 0);
  // pthread_mutex_unlock(&barrier_lock);
  // printf("UNPAUSED\n");
  // pthread_mutex_lock(&pause_lock);
  qflex_state->vm_unpause(NULL);
  // pthread_mutex_unlock(&pause_lock);

  pthread_mutex_unlock(&sync_lock);
  return true;
}

/* keeping this function as less as heavy as possible */
static void vcpu_insn_exec_before(unsigned int cpu_index, void *udata)
{
  if (atomic_load(&qflex_state->can_count) == 0)
    return;

  uint64_t value = atomic_fetch_add(&barrier_sum, 1) + 1;
  uint64_t next = atomic_load(&next_quanta);
  if (unlikely(value >= next)) {
    // if (pthread_mutex_lock(&ins_lock) != 0) {
    //   exit(EXIT_FAILURE);
    // }

    /* increment before because `qflex_next_quanta` will reset it */
    atomic_fetch_add(&threads_blocked_cnt, 1);
    bool stop = true;
    /* I am the thread triggering the quanta */
    if (unlikely(value == next)) {
      /* here you should stop sending packets */
      atomic_store(&qflex_state->can_send, 0);
      uint64_t s = atomic_fetch_add(&atomic_sum, 1) + 1;
      stop = false;

      // printf("INC TO %ld\n", atomic_fetch_add(&atomic_sum, 1) + 1);
      printf("SENDING %d - %d - %ld -> %ld (%ld)\n", curr_quanta,
             nodes_at_quanta, value, atomic_load(&atomic_sum), s);
      pthread_mutex_lock(&sync_lock);
      qflex_send_quanta_termination(curr_quanta);
      pthread_mutex_unlock(&sync_lock);
      if (!qflex_next_quanta(false, true, -1)) {
        // printf("PAUSED %ld\n", value);
        // pthread_mutex_lock(&pause_lock);
        qflex_state->vm_pause(NULL);
        // pthread_mutex_unlock(&pause_lock);
      }
      else {
        // printf("NOT BLOCKED\n");
      }
    }
    // printf("VALUE: %ld - %ld - %ld\n", value, atomic_load(&atomic_sum),
    //        atomic_load(&next_quanta));
    /* stop here waiting for synchronization */
    /* cond wait should not be busy waiting */
    // pthread_mutex_lock(&barrier_lock);
    while (stop && value > atomic_load(&next_quanta)) {
      // pthread_cond_wait(&barrier_cond, &barrier_lock);
    }
    // atomic_fetch_sub(&threads_blocked_cnt, 1);
    // pthread_mutex_unlock(&barrier_lock);
    // printf("BLOCKED %ld - %ld\n", value, atomic_load(&atomic_sum));
    // if (pthread_mutex_unlock(&ins_lock) != 0) {
    //   exit(EXIT_FAILURE);
    // }
  }
  // qemu_plugin_u64_add(insn_count, cpu_index, 1);
  // printf("INC %d\n", value != next ? 1 : 0);
  uint64_t s = atomic_fetch_add(&atomic_sum, value != next ? 1 : 0) +
               (value != next ? 1 : 0);
  if (s == next) {
    printf("BINGO\n");
    (void)qflex_send_self;
  }

  uint64_t n = atomic_load(&next_quanta);
  // printf("VALUE : %ld\n", s);
  if (s > n) {
    printf("BLOCK COUNT %d\n", atomic_load(&threads_blocked_cnt));
    printf("MORE THAN EXPECTED %ld - "
           "%ld\n\n----------------------------------------------\n\n",
           s, n);
    printf("PREV %ld - %ld\n", value, next);
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
        insn, vcpu_insn_exec_before, QEMU_PLUGIN_CB_NO_REGS, insn, test_fun);

    (void)rw;
    (void)vcpu_mem;
    // qemu_plugin_register_vcpu_mem_cb(insn, vcpu_mem, QEMU_PLUGIN_CB_NO_REGS,
    // rw,
    //                                  insn);
  }
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
  nodes = malloc(n_nodes * sizeof(qflex_node_t));
  printf("NODES: %d\n", n_nodes);
  printf("MY NODE: %d\n", node_id);
  printf("QUANTA: %ld\n", QUANTA);
  fclose(fp);

  fp = fopen(realpath(path, NULL), "r");
  /* reset length, so starting to read file from BOF */
  len = 0;
  line = NULL;
  int c = 0;
  while ((read = getline(&line, &len, fp)) != -1) {
    char *ptr = strtok(line, ";");
    nodes[c].ip = malloc(strlen(ptr) * sizeof(char));
    strcpy(nodes[c].ip, ptr);
    ptr = strtok(NULL, ";");
    nodes[c].port = atoi(ptr);
    printf("IP: %s - PORT: %d\n", nodes[c].ip, nodes[c].port);
    c++;
  }

  fclose(fp);
}

static void *qflex_server_open_thread(void *args)
{
  int opt = TRUE;
  struct sockaddr_in servaddr;
  int port = nodes[node_id].port;
  fd_set readfds;
  int activity, valread, sd;
  int max_sd, addrlen, incoming_socket;
  struct sockaddr_in address;
  // char buffer[1025]; // data buffer of 1K
  int buf;

  for (int i = 0; i < n_nodes; i++)
    nodes[i].fd_in = 0;

  // socket create and verification
  serverfd = socket(AF_INET, SOCK_STREAM, 0);
  if (serverfd == -1) {
    printf("socket creation failed...\n");
    exit(0);
  }
  else
    printf("Socket successfully created..\n");
  bzero(&servaddr, sizeof(servaddr));

  if (setsockopt(serverfd, SOL_SOCKET, SO_REUSEADDR, (char *)&opt,
                 sizeof(opt)) < 0) {
    exit(EXIT_FAILURE);
  }

  servaddr.sin_family = AF_INET;
  servaddr.sin_addr.s_addr = htonl(INADDR_ANY);
  servaddr.sin_port = htons(port);

  if ((bind(serverfd, (SA *)&servaddr, sizeof(servaddr))) != 0) {
    printf("socket bind failed...\n");
    exit(EXIT_FAILURE);
  }
  printf("Socket successfully binded..\n");

  if ((listen(serverfd, n_nodes * 2)) != 0) {
    printf("Listen failed...\n");
    exit(EXIT_FAILURE);
  }
  printf("Server listening..\n");

  // Accept the data packet from client and verification
  // connserverfd = accept(serverfd, (SA *)&cli, &len);
  // if (connserverfd < 0) {
  //   printf("server accept failed...\n");
  //   exit(EXIT_FAILURE);
  // }
  // printf("server accept the client...\n");

  for (;;) {
    // clear the socket set
    FD_ZERO(&readfds);

    // add master socket to set
    FD_SET(serverfd, &readfds);
    max_sd = serverfd;

    // add child sockets to set
    for (int i = 0; i < n_nodes; ++i) {
      // if (i == node_id)
      //   continue;
      // socket descriptor
      sd = nodes[i].fd_in;

      // if valid socket descriptor then add to read list
      if (sd > 0) {
        FD_SET(sd, &readfds);
        // highest file descriptor number, need it for the select function
        if (sd > max_sd)
          max_sd = sd;
      }
    }

    // wait for an activity on one of the sockets , timeout is NULL , so wait
    // indefinitely
    activity = select(max_sd + 1, &readfds, NULL, NULL, NULL);

    if ((activity < 0) && (errno != EINTR)) {
      printf("select error");
    }

    // If something happened on the master socket , then its an incoming
    // connection
    if (FD_ISSET(serverfd, &readfds)) {
      if ((incoming_socket = accept(serverfd, (struct sockaddr *)&address,
                                    (socklen_t *)&addrlen)) < 0) {
        perror("accept");
        exit(EXIT_FAILURE);
      }
      /* read the header */
      while ((valread = read(incoming_socket, &buf, sizeof(buf))) <= 0) {
      }

      /* if we can count, accept new connections */
      if (buf == NC) {
        /* immediately read the node id */
        int recv_node_id;
        while ((valread = read(incoming_socket, &recv_node_id,
                               sizeof(recv_node_id))) <= 0) {
          // inform user of socket number - used in send and receive commands
        }
        recv_node_id = ntohl(recv_node_id);
        printf("New connection , socket fd is %d , ip is : %s , port : %d , id "
               ": %d\n",
               incoming_socket, inet_ntoa(address.sin_addr),
               ntohs(address.sin_port), recv_node_id);
        nodes[recv_node_id].fd_in = incoming_socket;
        ++incoming_connections;
      }
      else if (buf == BT) {
        /* node 0 is the server */
        g_assert(node_id == 0);
        if (++nodes_at_boot == n_nodes - 1) {
          atomic_store(&qflex_state->can_count, 1);
          int v = BBT;
          printf("EMULATION STARTS\n");
          for (int j = 0; j < n_nodes; ++j) {
            write(nodes[j].fd_out, &v, sizeof(v));
          }
        }
      }
      else {
        printf("unknown %d\n", buf);
      }
    }

    // else its some IO operation on some other socket :)
    for (int i = 0; i < n_nodes; ++i) {
      // if (i == node_id)
      //   continue;
      sd = nodes[i].fd_in;

      if (FD_ISSET(sd, &readfds)) {
        // memset(buffer, 0, 1024);
        // Check if it was for closing , and also read the incoming message
        if ((valread = read(sd, &buf, sizeof(buf))) == 0) {
          // Somebody disconnected , get his details and print
          getpeername(sd, (struct sockaddr *)&address, (socklen_t *)&addrlen);
          printf("Host disconnected , ip %s , port %d \n",
                 inet_ntoa(address.sin_addr), ntohs(address.sin_port));

          close(sd);
          nodes[i].fd_in = 0;
          --incoming_connections;
          /* TODO: close all fds */
          exit(EXIT_FAILURE);
        }
        else if (valread > 0) {
          switch (buf) {
          /* is it quanta termination message ? */
          case QT:
            /* read the sent value */
            read(sd, &buf, sizeof(buf));
            int remote_quanta = ntohl(buf);
            printf("RECV %d from %d\n", remote_quanta, i);
            pthread_mutex_lock(&sync_lock);
            if (remote_quanta != curr_quanta) {
              uint64_t bar = atomic_load(&barrier_sum);
              uint64_t sum = atomic_load(&atomic_sum);
              printf("GOT A PROBLEM HERE %d - %d -> %ld - %ld\n", remote_quanta,
                     curr_quanta, bar, sum);
            }
            g_assert(remote_quanta == curr_quanta);
            pthread_mutex_unlock(&sync_lock);
            if (i == node_id) {
              for (int j = 0; j < n_nodes; j++) {
                if (j == node_id)
                  continue;
                /* to accept you I need to reach the end of my quanta */
                if (to_ack_quanta[j])
                  qflex_send_ack(j);
              }
            }
            else if (atomic_load(&atomic_sum) < atomic_load(&next_quanta)) {
              to_ack_quanta[i] = true;
            }
            else {
              qflex_send_ack(i);
            }
            if (i != node_id)
              /* the nodes faced the barrier */
              qflex_next_quanta(true, false, QT);
            break;
            /* my quanta termination is completed only when I receive the ACK
             * from all the other nodes */
          case AQT:
            pthread_mutex_lock(&sync_lock);
            if (acked_quanta[i] == false)
              n_acked_quanta++;
            acked_quanta[i] = true;
            printf("RECV AQT %d\n", i);
            /* I received the ack from everyone */
            if (n_acked_quanta == n_nodes - 1) {
              pthread_mutex_unlock(&sync_lock);
              qflex_next_quanta(true, false, AQT);
            }
            else
              pthread_mutex_unlock(&sync_lock);
            break;
          case BBT:
            printf("EMULATION STARTS\n");
            atomic_store(&qflex_state->can_count, 1);
            break;
          case ACK:
            printf("ACK\n");
            atomic_fetch_add(&qflex_state->pkt_acked, 1);
            // qflex_next_quanta(false);
            break;

          default:
            printf("UNK %d\n", valread);
          }
        }
      }
    }
  }
  printf("exited");
  pthread_exit(NULL);
}
static void qflex_server_open(void)
{
  pthread_t t1;
  int res = pthread_create(&t1, NULL, qflex_server_open_thread, NULL);
  if (res) {
    printf("error %d\n", res);
  }
}

static void qflex_clients_open(void)
{
  /* connect to all the remote nodes */
  for (int i = 0; i < n_nodes; i++) {
    /* i want to connect to myself to send messages to the main thread */
    // if (i == node_id)
    //   continue;
    struct sockaddr_in servaddr;
    bzero(&servaddr, sizeof(servaddr));

    servaddr.sin_family = AF_INET;
    servaddr.sin_addr.s_addr = inet_addr(nodes[i].ip);
    servaddr.sin_port = htons(nodes[i].port);

    do {
      nodes[i].fd_out = socket(AF_INET, SOCK_STREAM, 0);
      if (nodes[i].fd_out == -1) {
        printf("socket creation failed...\n");
        exit(EXIT_FAILURE);
      }
      if (connect(nodes[i].fd_out, (SA *)&servaddr, sizeof(servaddr)) == 0) {
        break;
      }
      usleep(100);
    } while (true);
    /* send header */
    int msg = NC;
    write(nodes[i].fd_out, &msg, sizeof(msg));
    /* sending my node id */
    msg = htonl(node_id);
    write(nodes[i].fd_out, &msg, sizeof(msg));
    printf("connected to the server..\n");
  }
  /* wait for all nodes to connect to my server */
  while (incoming_connections < n_nodes - 1) {
    usleep(100);
  }
}

static void qflex_server_close(void) { close(serverfd); }
static void qflex_clients_close(void)
{
  for (int i = 0; i < n_nodes; i++) {
    close(nodes[i].fd_out);
    close(nodes[i].fd_in);
  }
}

static int qflex_send_message(char *msg)
{
  for (int i = 0; i < n_nodes; i++) {
    if (i == node_id)
      continue;
    write(nodes[i].fd_out, msg, strlen(msg) * sizeof(char));
  }

  return 0;
}
static int qflex_send_self(int msg)
{
  if (write(nodes[node_id].fd_out, &msg, sizeof(msg)) == -1) {
    printf("Can not send number to %d\n", node_id);
    exit(EXIT_FAILURE);
  }
  return 0;
}
static int qflex_send_quanta_termination(int n)
{
  int conv = htonl(n);
  int type = QT;
  for (int i = 0; i < n_nodes; i++) {
    // if (i == node_id)
    //   continue;
    int arr[] = {type, conv};
    if (write(nodes[i].fd_out, &arr, 2 * sizeof(int)) == -1) {
      printf("Can not send number to %d\n", i);
      exit(EXIT_FAILURE);
    }
  }
  return 0;
}
static int qflex_send_ack(int dest_id)
{
  int type = AQT;
  write(nodes[dest_id].fd_out, &type, sizeof(type));
  return 0;
}
static int qflex_notify_packet(int dest_id)
{
  g_assert(dest_id >= -1 && dest_id < n_nodes);
  return 0;
  int msg = ACK;
  /* broadcast */
  if (dest_id == -1) {
    for (int i = 0; i < n_nodes; i++) {
      if (write(nodes[i].fd_out, &msg, sizeof(msg)) == -1) {
        printf("Can not send number to %d\n", i);
        exit(EXIT_FAILURE);
      }
    }
  }
  else {
    if (write(nodes[dest_id].fd_out, &msg, sizeof(msg)) == -1) {
      printf("Can not send number to %d\n", dest_id);
      exit(EXIT_FAILURE);
    }
  }
  return 0;
}

static void plugin_exit(qemu_plugin_id_t id, void *p)
{
  g_autoptr(GString) out = g_string_new(NULL);
  int i;

  if (do_size) {
    for (i = 0; i <= sizes->len; i++) {
      unsigned long *cnt = &g_array_index(sizes, unsigned long, i);
      if (*cnt) {
        g_string_append_printf(out, "len %d bytes: %ld insns\n", i, *cnt);
      }
    }
  }
  else {
    for (i = 0; i < qemu_plugin_num_vcpus(); i++) {
      g_string_append_printf(out, "cpu %d insns: %" PRIu64 "\n", i,
                             qemu_plugin_u64_get(insn_count, i));
    }
    g_string_append_printf(out, "total insns: %" PRIu64 " - %" PRIu64 "\n",
                           qemu_plugin_u64_sum(insn_count),
                           atomic_load(&atomic_sum));
  }
  qemu_plugin_outs(out->str);

  qemu_plugin_scoreboard_free(insn_count.score);
  g_array_free(sizes, TRUE);

  qflex_server_close();
  qflex_clients_close();
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
  qflex_state->get_qflex_icount = test_fun;
  atomic_store(&qflex_state->pkt_sent, 0);
  atomic_store(&qflex_state->pkt_received, 0);
  atomic_store(&qflex_state->pkt_acked, 0);
  qflex_state->pkt_receive = NULL;
  qflex_state->pkt_list_received = g_list_alloc();
  qflex_state->pkt_list_send = g_list_alloc();
  /* should be 0 at the beginning */
  qflex_state->can_count = 1;
  qflex_state->can_send = 1;
  qflex_state->pkt_notify = qflex_notify_packet;

  /* Register init, translation block and exit callbacks */
  qemu_plugin_register_qflex_state_cb(id, qflex_state);
  qemu_plugin_register_vcpu_init_cb(id, vcpu_init);
  qemu_plugin_register_vcpu_tb_trans_cb(id, vcpu_tb_trans);
  qemu_plugin_register_atexit_cb(id, plugin_exit, NULL);

  nodes_at_quanta = 0;
  next_quanta = QUANTA;
  qflex_config_load(config_path);
  qflex_server_open();
  qflex_clients_open();
  (void)qflex_send_message;

  to_ack_quanta = (bool *)malloc(n_nodes * sizeof(bool));
  acked_quanta = (bool *)malloc(n_nodes * sizeof(bool));
  for (int i = 0; i < n_nodes; ++i) {
    acked_quanta[i] = false;
    to_ack_quanta[i] = false;
  }
  n_acked_quanta = 0;
  n_to_ack_quanta = 0;
  // int c = 0;
  // for (;;) {
  //   // char *c1 = (char *)"ciao";
  //   // char *c2 = (char *)"ciao2";
  //   // (void)qflex_send_message(c1);
  //   (void)qflex_send_number(c++);
  //   sleep(3);
  // }
  // (void)qflex_send_message(c2);
  // sleep(10);
  // (void)qflex_send_message(c1);
  return 0;
}
