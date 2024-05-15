/*
 * Copyright (C) 2018, Emilio G. Cota <cota@braap.org>
 *
 * License: GNU GPL, version 2 or later.
 *   See the COPYING file in the top-level directory.
 */
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
static bool ackread[NCPU];
static bool stop[NCPU];
static _Atomic bool stopall;
pthread_mutex_t counter_lock = PTHREAD_MUTEX_INITIALIZER;
static struct qemu_plugin_scoreboard *counts;
static qemu_plugin_u64 qcounter;

static uint64_t QUANTA = 10000;
static uint64_t next = 10000;

typedef struct {
  uint64_t qcounter;
} CPUCount;

static void vcpu_insn_exec_before_no_plug(unsigned int cpu_index, void *udata)
{
  // while (stop[cpu_index]) {
  while (stopall) {
    usleep(1);
  }
  ackread[cpu_index] = 0;
  counters[cpu_index]++;
  // counter++;
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
static void *check(void *args)
{
  uint64_t curr = 0;
  uint64_t max = 0;
  for (;;) {
    usleep(1);
    curr = 0;
    for (volatile int i = 0; i < NCPU; i++) {
      curr += counters[i];
    }
    if (curr >= next) {
      if (curr - next > max) {
        max = curr - next;
        printf("QUANTA %ld\n", max);
      }
      // for (volatile int i = 0; i < NCPU; i++) {
      //   stop[i] = true;
      // }
      stopall = true;
      next += QUANTA;
      stopall = false;
      // while (true) {
      //   sleep(1);
      // }
      // sleep(1);
    }
  }
  return NULL;
}

QEMU_PLUGIN_EXPORT int qemu_plugin_install(qemu_plugin_id_t id,
                                           const qemu_info_t *info, int argc,
                                           char **argv)
{
  for (int i = 0; i < NCPU; i++) {
    counters[i] = 0;
    stop[i] = false;
  }
  counts = qemu_plugin_scoreboard_new(sizeof(CPUCount));
  qcounter = qemu_plugin_scoreboard_u64_in_struct(counts, CPUCount, qcounter);
  qemu_plugin_register_vcpu_tb_trans_cb(id, vcpu_tb_trans_no_plug);
  (void)vcpu_tb_trans_no_plug;
  pthread_t t1, t2;
  pthread_create(&t1, NULL, timer, &counter);
  pthread_create(&t2, NULL, check, &counter);
  (void)vcpu_tb_trans_no_plug;
  return 0;
}
