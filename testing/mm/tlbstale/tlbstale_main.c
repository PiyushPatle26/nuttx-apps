/****************************************************************************
 * apps/testing/mm/tlbstale/tlbstale_main.c
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.  The
 * ASF licenses this file to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance with the
 * License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
 * License for the specific language governing permissions and limitations
 * under the License.
 *
 ****************************************************************************/

/****************************************************************************
 * Included Files
 ****************************************************************************/

#include <nuttx/config.h>

#include <sys/ipc.h>
#include <sys/shm.h>
#include <sys/wait.h>

#include <errno.h>
#include <inttypes.h>
#include <pthread.h>
#include <sched.h>
#include <signal.h>
#include <spawn.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/****************************************************************************
 * Pre-processor Definitions
 ****************************************************************************/

#define TLBSTALE_KEY        0x544c4253  /* "TLBS"; NuttX lacks IPC_PRIVATE */
#define TLBSTALE_WKEY       0x544c4257  /* "TLBW": the writer's segment */
#define TLBSTALE_PATTERN    0x5a5aa5a5u
#define TLBSTALE_MARKER     0xb0b0b0b0u
#define TLBSTALE_MAIN_CPU   0
#define TLBSTALE_READ_CPU   1
#define TLBSTALE_WARMUP_US  100000
#define TLBSTALE_WATCH_US   500000
#define TLBSTALE_WRITER_US  200000
#define TLBSTALE_NVALUES    8
#define TLBSTALE_NWRITERS   3    /* Writer processes spawned by -x */
#define TLBSTALE_HEAPPAGES  256  /* Upper bound on heap pages per writer */
#define TLBSTALE_NWORDS     (CONFIG_MM_PGSIZE / sizeof(uint32_t))

/****************************************************************************
 * Private Data
 ****************************************************************************/

static FAR volatile uint32_t *g_shm;

static int g_started;
static int g_detached;
static int g_stop;

/* Written by the reader only after the detach, read by main after join */

static unsigned long g_reads_after;
static uint32_t g_values[TLBSTALE_NVALUES];
static unsigned long g_value_at[TLBSTALE_NVALUES];
static unsigned int g_value_word[TLBSTALE_NVALUES];
static int g_nvalues;
static int g_reader_cpu = -1;

/* Last value the reader saw in each word of the page, and how many words
 * ever held something other than our pattern or held the writer's marker.
 */

static uint32_t g_last[TLBSTALE_NWORDS];
static unsigned int g_nchanged;
static unsigned int g_nmarker;

/****************************************************************************
 * Private Functions
 ****************************************************************************/

static int pin_thread(pthread_t thread, int cpu)
{
  cpu_set_t cpuset;

  CPU_ZERO(&cpuset);
  CPU_SET(cpu, &cpuset);
  return pthread_setaffinity_np(thread, sizeof(cpuset), &cpuset);
}

static FAR void *reader(FAR void *arg)
{
  unsigned long count = 0;
  unsigned int word = 0;
  unsigned int i;

  for (i = 0; i < TLBSTALE_NWORDS; i++)
    {
      g_last[i] = TLBSTALE_PATTERN;
    }

  __atomic_store_n(&g_started, 1, __ATOMIC_RELEASE);

  while (!__atomic_load_n(&g_stop, __ATOMIC_ACQUIRE))
    {
      /* The acquire load orders the shared memory load below after it.
       * Once g_detached reads as 1, shmdt() has already returned on the
       * main CPU, so the mapping is gone and the next load must fault.
       * Every load goes through the same page translation; cycling over
       * all words catches a new owner that writes anywhere in the page.
       */

      int detached = __atomic_load_n(&g_detached, __ATOMIC_ACQUIRE);
      uint32_t value = g_shm[word];

      if (detached)
        {
          if (count == 0)
            {
              g_reader_cpu = sched_getcpu();
            }

          /* Record each change in what the stale translation returns */

          if (value != g_last[word])
            {
              if (g_last[word] == TLBSTALE_PATTERN)
                {
                  g_nchanged++;
                }

              if (value == TLBSTALE_MARKER)
                {
                  g_nmarker++;
                }

              if (g_nvalues < TLBSTALE_NVALUES)
                {
                  g_values[g_nvalues]     = value;
                  g_value_at[g_nvalues]   = count;
                  g_value_word[g_nvalues] = word;
                  g_nvalues++;
                }

              g_last[word] = value;
            }

          count++;
        }

      word = (word + 1) % TLBSTALE_NWORDS;
    }

  g_reads_after = count;
  return NULL;
}

static void fill_marker(FAR void *mem, size_t size)
{
  FAR volatile uint32_t *word = mem;
  size_t i;

  for (i = 0; i < size / sizeof(uint32_t); i++)
    {
      word[i] = TLBSTALE_MARKER;
    }
}

/* Child process for -x.  The page allocator is first-fit from the lowest
 * address, so the page freed by the parent goes to the next allocation in
 * the system unless a lower page is free.  The writers are spawned before
 * the free, so that creating them does not consume the page, and wait for
 * SIGUSR1 (blocked from birth by spawn_writer()).  Then they grab many
 * pages, through shared memory (writer 0 only, since the regions are
 * system-wide) and through the heap, and fill all of them with the marker.
 */

static int writer(int index)
{
  static FAR void *heap[TLBSTALE_HEAPPAGES];
  static FAR void *shm[CONFIG_ARCH_SHM_MAXREGIONS];
  static int shmids[CONFIG_ARCH_SHM_MAXREGIONS];
  size_t segsz = (size_t)CONFIG_ARCH_SHM_NPAGES * CONFIG_MM_PGSIZE;
  sigset_t set;
  int nshm = 0;
  int nheap = 0;
  int i;

  pin_thread(pthread_self(), TLBSTALE_MAIN_CPU);

  /* Wait until the parent has freed its page */

  sigemptyset(&set);
  sigaddset(&set, SIGUSR1);
  sigwaitinfo(&set, NULL);

  if (index == 0)
    {
      for (i = 0; i < CONFIG_ARCH_SHM_MAXREGIONS; i++)
        {
          shmids[nshm] = shmget(TLBSTALE_WKEY + i, segsz,
                                IPC_CREAT | 0600);
          if (shmids[nshm] < 0)
            {
              break;
            }

          shm[nshm] = shmat(shmids[nshm], NULL, 0);
          if (shm[nshm] == (FAR void *)-1)
            {
              shmctl(shmids[nshm], IPC_RMID, NULL);
              break;
            }

          fill_marker(shm[nshm], segsz);
          nshm++;
        }
    }

  while (nheap < TLBSTALE_HEAPPAGES)
    {
      heap[nheap] = malloc(CONFIG_MM_PGSIZE);
      if (heap[nheap] == NULL)
        {
          break;
        }

      fill_marker(heap[nheap], CONFIG_MM_PGSIZE);
      nheap++;
    }

  printf("tlbstale -w%d: filled %d shm pages and %d heap blocks with "
         "0x%08" PRIx32 "\n", index, nshm * CONFIG_ARCH_SHM_NPAGES, nheap,
         TLBSTALE_MARKER);

  /* Hold the pages while the reader watches.  Freed pages keep their
   * contents, so the marker stays visible after this process exits too.
   */

  usleep(TLBSTALE_WRITER_US);

  while (nheap > 0)
    {
      free(heap[--nheap]);
    }

  while (nshm > 0)
    {
      nshm--;
      shmdt(shm[nshm]);
      shmctl(shmids[nshm], IPC_RMID, NULL);
    }

  return EXIT_SUCCESS;
}

static int spawn_writer(FAR char *self, int priority, int index,
                        FAR pid_t *pid)
{
  FAR char *args[4];
  char indexstr[12];
  posix_spawnattr_t attr;
  struct sched_param param;
  sigset_t set;
  int ret;

  snprintf(indexstr, sizeof(indexstr), "%d", index);
  args[0] = self;
  args[1] = "-w";
  args[2] = indexstr;
  args[3] = NULL;

  /* Below the reader's priority, so it never preempts the reader and
   * flushes the reader CPU's TLB with a context switch.
   */

  param.sched_priority = priority;
  posix_spawnattr_init(&attr);
  posix_spawnattr_setschedparam(&attr, &param);

  /* Block SIGUSR1 from birth, so the parent's wake-up signal is never lost
   * or delivered with its default action before writer() waits for it.
   */

  sigemptyset(&set);
  sigaddset(&set, SIGUSR1);
  posix_spawnattr_setsigmask(&attr, &set);
  posix_spawnattr_setflags(&attr, POSIX_SPAWN_SETSCHEDPARAM |
                                  POSIX_SPAWN_SETSIGMASK);

  ret = posix_spawn(pid, self, NULL, &attr, args, environ);
  posix_spawnattr_destroy(&attr);
  return ret;
}

static void show_usage(FAR const char *progname)
{
  printf("Usage: %s [-l] [-c <cpu>] [-x]\n"
         "  -l        control case: reader on the main CPU, must fault\n"
         "  -c <cpu>  run the reader on <cpu> (default %d)\n"
         "  -x        after the free, %d child processes take many pages\n"
         "            and fill them with 0x%08" PRIx32 "; report what the\n"
         "            reader sees\n",
         progname, TLBSTALE_READ_CPU, TLBSTALE_NWRITERS, TLBSTALE_MARKER);
}

/****************************************************************************
 * Public Functions
 ****************************************************************************/

int main(int argc, FAR char *argv[])
{
  struct sched_param param;
  pthread_attr_t attr;
  pthread_t thread;
  unsigned long reads;
  FAR void *addr;
  bool reused = false;
  bool marker = false;
  bool cross = false;
  int readcpu = TLBSTALE_READ_CPU;
  pid_t pids[TLBSTALE_NWRITERS];
  int nwriters = 0;
  int status = 0;
  unsigned int nold = 0;
  unsigned int nmark = 0;
  unsigned int nzero = 0;
  int policy;
  int shmid;
  int ret;
  int i;

  for (i = 1; i < argc; i++)
    {
      if (strcmp(argv[i], "-w") == 0)
        {
          return writer(i + 1 < argc ? atoi(argv[i + 1]) : 0);
        }
      else if (strcmp(argv[i], "-l") == 0)
        {
          readcpu = TLBSTALE_MAIN_CPU;
        }
      else if (strcmp(argv[i], "-c") == 0 && i + 1 < argc)
        {
          readcpu = atoi(argv[++i]);
        }
      else if (strcmp(argv[i], "-x") == 0)
        {
          cross = true;
        }
      else
        {
          show_usage(argv[0]);
          return EXIT_FAILURE;
        }
    }

  if (readcpu < 0 || readcpu >= CONFIG_SMP_NCPUS)
    {
      printf("tlbstale: CPU%d out of range (0..%d)\n", readcpu,
             CONFIG_SMP_NCPUS - 1);
      return EXIT_FAILURE;
    }

  printf("tlbstale: reader on CPU%d, main on CPU%d (%s%s)\n", readcpu,
         TLBSTALE_MAIN_CPU,
         readcpu == TLBSTALE_MAIN_CPU ? "control: same CPU" :
                                        "cross-CPU unmap",
         cross ? ", cross-process reuse" : "");

  ret = pin_thread(pthread_self(), TLBSTALE_MAIN_CPU);
  if (ret != 0)
    {
      printf("tlbstale: pin main to CPU%d failed: %d\n",
             TLBSTALE_MAIN_CPU, ret);
      return EXIT_FAILURE;
    }

  shmid = shmget(TLBSTALE_KEY, CONFIG_MM_PGSIZE, IPC_CREAT | 0600);
  if (shmid < 0)
    {
      printf("tlbstale: shmget failed: %d\n", errno);
      return EXIT_FAILURE;
    }

  addr = shmat(shmid, NULL, 0);
  if (addr == (FAR void *)-1)
    {
      printf("tlbstale: shmat failed: %d\n", errno);
      shmctl(shmid, IPC_RMID, NULL);
      return EXIT_FAILURE;
    }

  g_shm = addr;
  for (i = 0; i < TLBSTALE_NWORDS; i++)
    {
      g_shm[i] = TLBSTALE_PATTERN;
    }

  /* Run the busy-looping reader one priority below main, so main still
   * gets its CPU back after sleeping when both share a CPU.
   */

  pthread_getschedparam(pthread_self(), &policy, &param);
  param.sched_priority--;

  pthread_attr_init(&attr);
  pthread_attr_setinheritsched(&attr, PTHREAD_EXPLICIT_SCHED);
  pthread_attr_setschedpolicy(&attr, policy);
  pthread_attr_setschedparam(&attr, &param);

  ret = pthread_create(&thread, &attr, reader, NULL);
  pthread_attr_destroy(&attr);
  if (ret != 0)
    {
      printf("tlbstale: pthread_create failed: %d\n", ret);
      shmdt(addr);
      shmctl(shmid, IPC_RMID, NULL);
      return EXIT_FAILURE;
    }

  ret = pin_thread(thread, readcpu);
  if (ret != 0)
    {
      printf("tlbstale: pin reader to CPU%d failed: %d\n", readcpu, ret);
    }

  while (!__atomic_load_n(&g_started, __ATOMIC_ACQUIRE))
    {
      usleep(1000);
    }

  /* For -x, create the writers now: creating a process allocates page
   * tables, stack and data pages, and those must not take the page we are
   * about to free.  The writers block until they get SIGUSR1.
   */

  if (cross)
    {
      for (i = 0; i < TLBSTALE_NWRITERS; i++)
        {
          ret = spawn_writer(argv[0], param.sched_priority - 9, i,
                             &pids[nwriters]);
          if (ret != 0)
            {
              printf("tlbstale: spawning writer %d failed: %d\n", i, ret);
              break;
            }

          nwriters++;
        }
    }

  /* Let the reader run on its CPU long enough to cache the translation,
   * and the writers finish starting up.
   */

  usleep(TLBSTALE_WARMUP_US);

  printf("tlbstale: main on CPU%d, shared page at %p; "
         "detaching while the reader runs\n", sched_getcpu(), addr);

  /* Remove the mapping and free the physical page.  On a TLB-coherent
   * system the reader faults on its next load and the process is killed
   * with SIGSEGV, so nothing below this point is printed.
   */

  ret = shmdt(addr);
  if (ret < 0)
    {
      printf("tlbstale: shmdt failed: %d\n", errno);
    }

  ret = shmctl(shmid, IPC_RMID, NULL);
  if (ret < 0)
    {
      printf("tlbstale: shmctl(IPC_RMID) failed: %d\n", errno);
    }

  __atomic_store_n(&g_detached, 1, __ATOMIC_RELEASE);

  if (cross)
    {
      /* The page is free: let the writers allocate */

      for (i = 0; i < nwriters; i++)
        {
          kill(pids[i], SIGUSR1);
        }

      for (i = 0; i < nwriters; i++)
        {
          waitpid(pids[i], &status, 0);
        }
    }

  usleep(TLBSTALE_WATCH_US);

  __atomic_store_n(&g_stop, 1, __ATOMIC_RELEASE);
  pthread_join(thread, NULL);

  reads = g_reads_after;
  if (reads == 0)
    {
      printf("tlbstale: no loads after shmdt(); the reader never ran after "
             "the detach, so the result is inconclusive\n");
      return EXIT_SUCCESS;
    }

  printf("tlbstale: FAIL: the reader on CPU%d made %lu loads after "
         "shmdt() returned.\n"
         "tlbstale: the page was unmapped and freed, so a coherent TLB "
         "would have faulted on the first load.\n",
         g_reader_cpu, reads);

  printf("tlbstale: scanned the page %lu times: %u of %u words changed "
         "after the free, %u held the writer's marker 0x%08" PRIx32 "\n",
         reads / TLBSTALE_NWORDS, g_nchanged,
         (unsigned int)TLBSTALE_NWORDS, g_nmarker, TLBSTALE_MARKER);

  for (i = 0; i < g_nvalues; i++)
    {
      printf("tlbstale:   load #%lu word %u read 0x%08" PRIx32 "%s\n",
             g_value_at[i], g_value_word[i], g_values[i],
             g_values[i] == TLBSTALE_MARKER ? " (the writer's marker)" :
                                              " (unknown owner's data)");
    }

  for (i = 0; i < TLBSTALE_NWORDS; i++)
    {
      if (g_last[i] == TLBSTALE_PATTERN)
        {
          nold++;
        }
      else if (g_last[i] == TLBSTALE_MARKER)
        {
          nmark++;
        }
      else if (g_last[i] == 0)
        {
          nzero++;
        }
    }

  printf("tlbstale: last view of the page: %u words our old data, %u the "
         "writer's marker, %u zero, %u other\n", nold, nmark, nzero,
         (unsigned int)TLBSTALE_NWORDS - nold - nmark - nzero);

  reused = g_nchanged > 0;
  marker = g_nmarker > 0;

  if (cross)
    {
      printf("tlbstale: %d writer process(es) ran\n", nwriters);
    }

  if (marker)
    {
      printf("tlbstale: LEAK: the freed page was reallocated to a writer "
             "process, and this process read the writer's data\n");
    }
  else if (reused)
    {
      printf("tlbstale: the freed page was reallocated and overwritten by "
             "an unknown owner; this process read that data\n");
    }
  else
    {
      printf("tlbstale: the page still held only our old data\n");
    }

  return EXIT_FAILURE;
}
