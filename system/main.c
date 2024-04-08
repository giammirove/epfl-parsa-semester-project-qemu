/*
 * QEMU System Emulator
 *
 * Copyright (c) 2003-2020 Fabrice Bellard
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

#include "qemu/osdep.h"
#include "qemu-main.h"
#include "qemu/plugin-event.h"
#include "qemu/timer.h"
#include "sysemu/sysemu.h"
#include "../accel/tcg/internal-common.h"
#include "tcg/tcg.h"

#ifdef CONFIG_SDL
#include <SDL.h>
#endif

static QEMUTimer *exit_trigger;
static QEMUTimer *test_insn_trigger;
static int64_t now, now_500;
// a second
static int64_t insn_cycles = 500000000;
// static int64_t cycles = 1000000000;
static int64_t cycles = 2000000000;
// static int64_t cycles = 500000000;
// static int64_t cycles = 20000000;
static int64_t times = 0;

struct timeval t1, t2, t1_500;
static double elapsedTime;

uint64_t qflex_icount;
uint64_t qflex_icount_500;
uint64_t qflex_icount_1000;

// QEMUClockType type = QEMU_CLOCK_REALTIME;
QEMUClockType type = QEMU_CLOCK_VIRTUAL;

// static FILE *fptr;

static void exit_trigger_cb(void *opaque)
{
  (void)times;
  uint64_t tot = 0, icount = 0;
  CPUState *cpu;
  CPU_FOREACH(cpu)
  {
    if (cpu->qflex_state->get_qflex_icount) {
      tot += cpu->qflex_state->get_qflex_icount();
      break;
    }
  }
  // CPU_FOREACH(cpu)
  // {
  //   icount += (cpu->icount_budget -
  //              (cpu->neg.icount_decr.u16.low + cpu->icount_extra));
  // }
  qflex_icount_1000 = tot - qflex_icount_1000;

  if (tot > 0)
    printf("%ld - %ld - %ld\n", tot, icount, myicount);

  int64_t end = qemu_clock_get_ms(type);
  gettimeofday(&t2, NULL);
  // printf("[%ld - %ld] - %ld: %ld - perc %f %% (%ld - %ld)\n", tot, mycounter,
  //        times++, end - now, (qflex_icount_500 * 1.0) / qflex_icount_1000,
  //        qflex_icount_500, qflex_icount_1000);
  // printf("%ld\n", end - now);
  // Write some text to the file
  // if (fptr)
  //   fprintf(fptr, "%ld\n", end - now);
  now = end;

  elapsedTime = (t2.tv_sec - t1.tv_sec) * 1000.0;    // sec to ms
  elapsedTime += (t2.tv_usec - t1.tv_usec) / 1000.0; // us to ms
  // printf("%f ms.\n", elapsedTime);
  gettimeofday(&t1, NULL);
  timer_mod(exit_trigger, qemu_clock_get_ns(type) + cycles);
  (void)insn_cycles;
  // timer_mod(test_insn_trigger, qemu_clock_get_ns(type) + insn_cycles);
}

static void test_insn_trigger_cb(void *opaque)
{
  int64_t end = qemu_clock_get_ms(type);
  gettimeofday(&t2, NULL);

  uint64_t tot = 0;
  CPUState *cpu;
  CPU_FOREACH(cpu)
  {
    if (cpu->qflex_state->get_qflex_icount) {
      tot += cpu->qflex_state->get_qflex_icount();
      break;
    }
  }

  // printf("[%ld - %ld] insn - %ld: %ld - elaps %ld \n", tot, mycounter,
  //        times++, end - now_500, tot-qflex_icount_1000);
  qflex_icount_500 = tot - qflex_icount_1000;
  // printf("[%ld - %ld] %ld - %ld (%ld - %ld)\n", tot, mycounter, end -
  // now_500,
  //        qflex_icount_500, tot, qflex_icount_1000);
  now_500 = end;

  elapsedTime = (t2.tv_sec - t1.tv_sec) * 1000.0;    // sec to ms
  elapsedTime += (t2.tv_usec - t1.tv_usec) / 1000.0; // us to ms
  // printf("%f ms.\n", elapsedTime);
  gettimeofday(&t1_500, NULL);
}

int qemu_default_main(void)
{
  gettimeofday(&t1, NULL);
  gettimeofday(&t1_500, NULL);
  //
  // // Open a file in writing mode
  // fptr = fopen("log.txt", "a");
  //
  // now = qemu_clock_get_ms(type);
  // now_500 = qemu_clock_get_ms(type);
  exit_trigger = timer_new_ns(type, exit_trigger_cb, NULL);
  timer_mod(exit_trigger, qemu_clock_get_ns(type) + cycles);
  //
  // test_insn_trigger = timer_new_ns(type, test_insn_trigger_cb, NULL);
  // timer_mod(test_insn_trigger, qemu_clock_get_ns(type) + insn_cycles);
  (void)now;
  // (void)fptr;
  (void)now_500;
  (void)exit_trigger;
  (void)exit_trigger_cb;
  (void)type;
  (void)test_insn_trigger;
  (void)test_insn_trigger_cb;

  int status;
  status = qemu_main_loop();
  qemu_cleanup(status);

  // Close the file
  // fclose(fptr);

  return status;
}

int (*qemu_main)(void) = qemu_default_main;

int main(int argc, char **argv)
{
  qemu_init(argc, argv);
  return qemu_main();
}
