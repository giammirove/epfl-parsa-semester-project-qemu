/*
 * Copyright (C) 2018, Emilio G. Cota <cota@braap.org>
 *
 * License: GNU GPL, version 2 or later.
 *   See the COPYING file in the top-level directory.
 */
#include <inttypes.h>
#include <assert.h>
#include <netinet/tcp.h>
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
/* 1 = quanta reached */
static _Atomic int quanta_reached = 0;
static _Atomic int nodes_ready = 0;
/* node ready that went faster than me during the synchronization phase */
static _Atomic int buf_nodes_ready = 0;
static _Atomic int nodes_ack_ready = 0;
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
  RDY = 1,  /* node is ready */
  ARDY = 2, /* ack node is ready */
  NC = 3,   /* new connection */
  BT = 4,   /* boot : DO NOT EDIT (used in afterboot script) */
  BBT = 5,  /* broadcast boot */
  ACK = 6   /* ack packet */
};

static void *qflex_server_open_thread(void *args);
static void qflex_server_open(void);
static void qflex_clients_open(void);
static void qflex_server_close(void);
static void qflex_clients_close(void);
static int qflex_send_message(char *msg);
static int qflex_send_ready(int n, bool is_ack);
static int qflex_notify_packet(int dest_id);
static bool qflex_next_quanta(bool node_at_quanta, bool im_at_quanta, int src);
static bool qflex_check_ready(void);
static void qflex_move_to_next_quanta(void);
static void qflex_begin_of_quanta(void);

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
  quanta_id++;
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

static bool qflex_check_ready(void)
{
  printf("CHECK READY %ld %ld\n", atomic_load(&qflex_state->pkt_acked),
         atomic_load(&qflex_state->pkt_sent));
  if (atomic_load(&quanta_reached) == 1 &&
      atomic_load(&qflex_state->pkt_acked) ==
          atomic_load(&qflex_state->pkt_sent)) {
    printf("SEND READY for %d\n", quanta_id);
    qflex_send_ready(quanta_id, false);
    return true;
  }

  return false;
}

static void qflex_move_to_next_quanta(void)
{

  if (qflex_state->pkt_receive != NULL)
    qflex_state->pkt_receive(quanta_id);
  else {
    printf("RECEIVE METHOD NOT SET\n");
  }

  /* reset */
  nodes_at_quanta = 0;
  n_acked_quanta = 0;
  for (int i = 0; i < n_nodes; ++i)
    acked_quanta[i] = false;
  /* move to next quanta */
  // pthread_cond_broadcast(&barrier_cond);
  qflex_state->vm_unpause(NULL);
  /* so that check_ready returns false */
  atomic_store(&quanta_reached, 0);
  quanta_id++;
  printf("[-] MOVE TO NEXT QUANTA -> %d\n", quanta_id);
  /* `next_quanta` has to be kept unchanged until the beginning of the nextinsn
   * quanta, since it works as barrier for my `vcpu_insn_exec_before`
   */
}
static void qflex_begin_of_quanta(void)
{
  printf("[%d] SYNC COMPLETED\n", quanta_id);
  printf("-------------------------------------------\n\n");
  atomic_store(&qflex_state->can_send, 1);
  atomic_store(&nodes_ready, atomic_load(&buf_nodes_ready));
  atomic_store(&nodes_ack_ready, 0);
  atomic_store(&buf_nodes_ready, 0);
  /* unlock threads */
  // pthread_mutex_lock(&barrier_lock);
  // pthread_cond_broadcast(&barrier_cond);
  atomic_fetch_add(&next_quanta, QUANTA);
  // pthread_mutex_unlock(&barrier_lock);
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
    /* I am the thread triggering the quanta */
    if (unlikely(value == next)) {
      /* here you should stop sending packets */
      atomic_store(&qflex_state->can_send, 0);
      atomic_store(&quanta_reached, 1);
      printf("QUANTA REACHED %ld\n", value);
      qflex_check_ready();

      // printf("SENDING %d - %d - %ld -> %ld (%ld)\n", curr_quanta,
      //        nodes_at_quanta, value, atomic_load(&atomic_sum), s);
    }
    // printf("VALUE: %ld - %ld - %ld\n", value, atomic_load(&atomic_sum),
    //        atomic_load(&next_quanta));
    /* stop here waiting for synchronization */
    /* cond wait should not be busy waiting */
    // pthread_mutex_lock(&barrier_lock);
    uint64_t c = 0;
    while (value > atomic_load(&next_quanta)) {
      // pthread_cond_wait(&barrier_cond, &barrier_lock);
      usleep(1);
      c++;
      if (c > 100000000000000) {
        printf("IM STUCKED\n");
        usleep(100);
      }
    }
    // atomic_fetch_sub(&threads_blocked_cnt, 1);
    // pthread_mutex_unlock(&barrier_lock);
    // printf("BLOCKED %ld - %ld\n", value, atomic_load(&atomic_sum));
    // if (pthread_mutex_unlock(&ins_lock) != 0) {
    //   exit(EXIT_FAILURE);
    // }
  }
  // qemu_plugin_u64_add(insn_count, cpu_index, 1);
  uint64_t s = atomic_fetch_add(&atomic_sum, 1) + 1;

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

    /* there is probably an error with the handling of my self when it comes to
     * master server */
    if (FD_ISSET(serverfd, &readfds)) {
      printf("SOMETHING SERVER\n");
      /* if the server completed its job, stop here avoiding possible errors */
      if (atomic_load(&qflex_state->can_count) == 1)
        continue;
      if ((incoming_socket = accept(serverfd, (struct sockaddr *)&address,
                                    (socklen_t *)&addrlen)) < 0) {
        perror("accept");
        exit(EXIT_FAILURE);
      }
      /* read the header */
      if ((valread = read(incoming_socket, &buf, sizeof(buf))) <= 0) {
        continue;
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
        if (++nodes_at_boot == n_nodes) {
          atomic_store(&qflex_state->can_count, 1);
          int v = BBT;
          printf("EMULATION STARTS\n");
          for (int j = 0; j < n_nodes; ++j) {
            if (j != node_id)
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
        printf("SOMETHING NODES\n");
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
          int remote = 0;
          switch (buf) {
          case RDY:
            read(sd, &buf, sizeof(buf));
            remote = htonl(buf);
            /*
             * situation when
             * all the ARDY messages have been sent, but one of them
             * is delay, so proc A receives them all, completes the
             * synchronization, starts a new quanta and sends a RDY message with
             * quanta_id+1;
             * on the other hand proc B has not yet received all the ARDY, but
             * receives the RDY with quanta_id + 1 from A
             * we decide to bufferize the message since it is a faulty situation
             */
            /* atomic_load(&nodes_ready) == n_nodes -> so we already moved to
             * the next quantum */
            /* remote == quanta_id -> if we already moved to the next quantum
             * then so it does the remote node */
            if (remote == quanta_id && atomic_load(&nodes_ready) == n_nodes) {
              printf("BUFF\n");
              atomic_fetch_add(&buf_nodes_ready, 1);
              /* early stop */
              break;
            }
            printf("RDY %d - %d from %d\n", remote, quanta_id, i);
            g_assert(remote == quanta_id);
            /* all nodes are ready */
            if (atomic_fetch_add(&nodes_ready, 1) + 1 == n_nodes) {
              /* ack */
              qflex_send_ready(quanta_id, true);
              qflex_move_to_next_quanta();
            }
            break;
          case ARDY:
            read(sd, &buf, sizeof(buf));
            remote = htonl(buf);
            printf("ARDY for %d - %d from %d\n", remote, quanta_id, i);
            if (atomic_load(&nodes_ready) == n_nodes)
              g_assert(remote == quanta_id - 1);
            else
              g_assert(remote == quanta_id);
            /* now we are sure that everyone is at the same quanta */
            if (atomic_fetch_add(&nodes_ack_ready, 1) + 1 == n_nodes) {
              qflex_begin_of_quanta();
            }
            break;
          case BBT:
            printf("EMULATION STARTS\n");
            atomic_store(&qflex_state->can_count, 1);
            break;
          case ACK:
            printf("ACK\n");
            atomic_fetch_add(&qflex_state->pkt_acked, 1);
            qflex_check_ready();
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
static int qflex_send_ready(int n, bool is_ack)
{
  int conv = htonl(n);
  int type = is_ack ? ARDY : RDY;

  for (int i = 0; i < n_nodes; i++) {
    // if (i == node_id)
    //   continue;
    /* see
     * https://stackoverflow.com/questions/855544/is-there-a-way-to-flush-a-posix-socket
     */
    int flag = 1;
    setsockopt(nodes[i].fd_out, IPPROTO_TCP, TCP_NODELAY, (char *)&flag,
               sizeof(int));
    int arr[] = {type, conv};
    if (write(nodes[i].fd_out, &arr, 2 * sizeof(int)) == -1) {
      printf("Can not send number to %d\n", i);
      exit(EXIT_FAILURE);
    }
    flag = 0;
    setsockopt(nodes[i].fd_out, IPPROTO_TCP, TCP_NODELAY, (char *)&flag,
               sizeof(int));
  }

  return 0;
}
static int qflex_notify_packet(int dest_id)
{
  g_assert(dest_id >= -1 && dest_id < n_nodes);
  /* broadcast */
  if (dest_id == -1) {
    for (int i = 0; i < n_nodes; i++) {
      int msg = ACK;
      if (write(nodes[i].fd_out, &msg, sizeof(msg)) == -1) {
        printf("Can not send number to %d\n", i);
        exit(EXIT_FAILURE);
      }
    }
  }
  else {
    int msg = ACK;
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
  qflex_state->can_count = 0;
  qflex_state->can_send = 1;
  qflex_state->pkt_notify = qflex_notify_packet;

  /* Register init, translation block and exit callbacks */
  qemu_plugin_register_qflex_state_cb(id, qflex_state);
  qemu_plugin_register_vcpu_init_cb(id, vcpu_init);
  qemu_plugin_register_vcpu_tb_trans_cb(id, vcpu_tb_trans);
  qemu_plugin_register_atexit_cb(id, plugin_exit, NULL);

  nodes_at_quanta = 0;
  next_quanta = QUANTA;
  quanta_id = 0;
  qflex_config_load(config_path);

  to_ack_quanta = (bool *)malloc(n_nodes * sizeof(bool));
  acked_quanta = (bool *)malloc(n_nodes * sizeof(bool));
  for (int i = 0; i < n_nodes; ++i) {
    acked_quanta[i] = false;
    to_ack_quanta[i] = false;
  }
  n_acked_quanta = 0;
  n_to_ack_quanta = 0;

  qflex_server_open();
  qflex_clients_open();
  (void)qflex_send_message;
  (void)qflex_next_quanta;
  return 0;
}
