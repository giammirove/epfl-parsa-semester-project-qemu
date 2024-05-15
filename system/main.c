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

static QEMUTimer *mips_timer;
static int64_t now;
// a second
static int64_t cycles = 1000000000;

struct timeval t1, t2, t1_500;
static double elapsedTime;

uint64_t qflex_icount = 0;

QEMUClockType type = QEMU_CLOCK_REALTIME;

FILE *fptr;

static void exit_trigger_cb(void *opaque)
{
  uint64_t tot = 0;
  CPUState *cpu;
  CPU_FOREACH(cpu)
  {
    if (cpu->qflex_state && cpu->qflex_state->get_icount) {
      tot += cpu->qflex_state->get_icount(cpu->qflex_state);
      break;
    }
  }
  if (cpu == NULL || cpu->qflex_state == NULL /*||
      cpu->qflex_state->can_count == 0*/) {
    timer_mod(mips_timer, qemu_clock_get_ns(type) + cycles);
    return;
  }
  uint64_t curr = tot - qflex_icount;
  qflex_icount = tot;

  int64_t end = qemu_clock_get_ms(type);
  gettimeofday(&t2, NULL);
  now = end;

  elapsedTime = (t2.tv_sec - t1.tv_sec) * 1000.0;    // sec to ms
  elapsedTime += (t2.tv_usec - t1.tv_usec) / 1000.0; // us to ms
  printf("%ld in %f ms\n", curr, elapsedTime);
  fprintf(fptr, "%ld in %f ms\n", curr, elapsedTime);

  gettimeofday(&t1, NULL);
  timer_mod(mips_timer, qemu_clock_get_ns(type) + cycles);
}

int qemu_default_main(void)
{
  gettimeofday(&t1, NULL);
  CPUState *cpu;
  CPU_FOREACH(cpu)
  {
    if (cpu != NULL)
      break;
  }

  if (cpu != NULL && cpu->qflex_state != NULL) {
    // Open a file in writing mode
    char name[1024];
    sprintf(name, "log_%d.txt", *(int *)cpu->qflex_state->dummy);
    fptr = fopen(name, "a");

    (void)exit_trigger_cb;
    // now = qemu_clock_get_ms(type);
    // mips_timer = timer_new_ns(type, exit_trigger_cb, NULL);
    // timer_mod(mips_timer, qemu_clock_get_ns(type) + cycles);
  }

  int status;
  status = qemu_main_loop();
  qemu_cleanup(status);

  if (cpu != NULL && cpu->qflex_state != NULL) {
    // Close the file
    fclose(fptr);
  }

  return status;
}

int (*qemu_main)(void) = qemu_default_main;

int main(int argc, char **argv)
{
  qemu_init(argc, argv);
  return qemu_main();
}
