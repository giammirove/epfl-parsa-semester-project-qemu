/*
 * Copyright (C) 2018, Emilio G. Cota <cota@braap.org>
 *
 * License: GNU GPL, version 2 or later.
 *   See the COPYING file in the top-level directory.
 */
#include "typedefs.h"
#include <pthread.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdio.h>

#include <qemu-plugin.h>

#define NCPU 32

QEMU_PLUGIN_EXPORT int qemu_plugin_version = QEMU_PLUGIN_VERSION;
static uint64_t counter = 0;
static uint64_t counters[NCPU];
QflexPluginState *qflex_state;

static void vcpu_insn_exec_before_no_plug(unsigned int cpu_index, void *udata)
{
  counters[cpu_index]++;
}
static void vcpu_tb_trans_no_plug(qemu_plugin_id_t id,
                                  struct qemu_plugin_tb *tb)
{
  size_t n = qemu_plugin_tb_n_insns(tb);
  size_t i;

  for (i = 0; i < n; i++) {
    struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);

    (void)vcpu_insn_exec_before_no_plug;
    // qemu_plugin_register_vcpu_insn_exec_inline_per_vcpu(
    //     insn, QEMU_PLUGIN_INLINE_ADD_U64, qcounter, 1);
    qemu_plugin_register_vcpu_insn_exec_cb(insn, vcpu_insn_exec_before_no_plug,
                                           QEMU_PLUGIN_CB_NO_REGS, NULL);
  }
}

static void *timer(void *args)
{
  // QflexPluginState *state = args;
  // uint64_t *counter = args;
  FILE *ptr;
  ptr = fopen("prova.txt", "w");
  uint64_t prev = 0;
  uint64_t max = 0;
  for (;;) {
    sleep(1);
    // uint64_t curr = *counter;
    uint64_t curr = 0;
    for (int i = 0; i < NCPU; i++) {
      curr += counters[i];
    }
    // curr = __atomic_load_n(counter, __ATOMIC_RELAXED);
    // curr = *counter;
    // curr = qemu_plugin_u64_sum(qcounter);
    uint64_t m = curr - prev;
    if (m > max) {
      max = m;
      fprintf(ptr, "%ld\n", max);
    }
    printf("%ld - %ld\n", max / 1000000, m / 1000000);
    prev = curr;
  }
  fclose(ptr);
  return NULL;
}

QEMU_PLUGIN_EXPORT int qemu_plugin_install(qemu_plugin_id_t id,
                                           const qemu_info_t *info, int argc,
                                           char **argv)
{
  qflex_state = malloc(sizeof(QflexPluginState));
  qflex_state->pkt_sent = 0;
  qflex_state->pkt_received = 0;
  qflex_state->pkt_receive = NULL;
  qflex_state->pkt_list_received = g_list_alloc();
  qflex_state->pkt_list_send = g_list_alloc();
  /* should be 0 at the beginning */
  qflex_state->n_nodes = 2;
  qflex_state->can_count = 0;
  qflex_state->stop = ST_F;
  qflex_state->clock = 0;
  qflex_state->idle_cpus = 0;
  qflex_state->offset_time = 0;
  // qflex_state->pkt_notify = qflex_notify_packet;
  // qflex_state->get_clock = qflex_get_clock;
  // qflex_state->get_icount = qflex_get_icount;
  // qflex_state->send_boot = qflex_send_boot;
  // qflex_state->can_send = qflex_can_send;

  // qflex_state->lstate = qflex_lstate;
  pthread_mutexattr_t attr, attr_thread;
  pthread_mutexattr_init(&attr);
  pthread_mutexattr_init(&attr_thread);
  pthread_condattr_t attr_cond, attr_cond_thread;
  pthread_condattr_init(&attr_cond);
  pthread_condattr_init(&attr_cond_thread);

  // pthread_mutex_init(&qflex_lstate->idle_lock, &attr);
  // pthread_mutex_init(&qflex_lstate->barrier_lock, &attr);
  // pthread_cond_init(&qflex_lstate->barrier_cond, &attr_cond);

  /* so that a thread can lock a mutex multiple times (i.e. tap receive with a
   * retry could) */
  // pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_RECURSIVE);
  pthread_mutex_init(&qflex_state->lock1, &attr);
  pthread_mutex_init(&qflex_state->lock2, &attr);
  pthread_mutex_init(&qflex_state->lock3, &attr);

  pthread_cond_init(&qflex_state->cond1, &attr_cond);

  for (int i = 0; i < NCPU; i++) {
    counters[i] = 0;
  }
  qemu_plugin_register_vcpu_tb_trans_cb(id, vcpu_tb_trans_no_plug);
  (void)vcpu_tb_trans_no_plug;
  pthread_t t1;
  pthread_create(&t1, NULL, timer, &counter);
  (void)vcpu_tb_trans_no_plug;
  return 0;
}
