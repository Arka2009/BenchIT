/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id$
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* Kernel: measures throughput of memory bound SIMD instructions for cache levels and main memory.
 *******************************************************************/

#ifndef __WORK_H
#define __WORK_H

#include <mm_malloc.h>
#include <pthread.h>
#include <numa.h>
#include "arch.h"

#define KERNEL_DESCRIPTION  "throughput of SIMD instructions"
#define CODE_SEQUENCE       "scalar and packed SIMD instructions"
#define X_AXIS_TEXT         "data set size [Byte]"
#define Y_AXIS_TEXT_1       "bandwidth [GB/s]"
#define Y_AXIS_TEXT_2       "counter value/ memory accesses"

/* serialization method */
#if defined(FORCE_CPUID)
#define SERIALIZE "push %%rax; push %%rbx; push %%rcx; push %%rdx;" \
                "mov $0, %%rax;" \
                "cpuid;" \
                "pop %%rdx; pop %%rcx; pop %%rbx; pop %%rax;"
#elif defined(FORCE_MFENCE)
#define SERIALIZE "mfence;"
#else
#define SERIALIZE ""
#endif

/* read timestamp counter */
#define TIMESTAMP "rdtsc;shl $32,%%rdx;add %%rdx,%%rax;"


/** 2 phase synchronization
 * phase 1: compxchg barrier ensures that all threads reached the barrier
 *          however, the last thread runs right through, thus starts earlier while the others still wait for 
 *          it to arrive
 * phase 2: if a power management invariant TSC is available it is used to make all threads leave the barrier
 *          almost concurrently
 * Input:   r8:  Pointer to synch[2] (part of mydata_t)
 *               synch[0] has to be 0, synch[1] indicates if invariant TSC is available (0|1), must not be >1
 *          r11: Number of Threads
 *          r12: Thread ID
 * rax, rbx, rdx, and r13 are destoid during Synchronization
 */
#define SYNC(X) /* Synchronisation Phase 1: Barrier (cmpxchg) */ \
                "mov 8(%%r8),%%r13;" /* load TSC feature flag for Phase 2 */ \
                "mov %%r12,%%rbx;add $1,%%rbx;" /* r12: ID, rbx: ID+1 */ \
                "_sync0_"#X":" \
                  "mov %%r12,%%rax;" \
                  "lock cmpxchg %%bl,(%%r8);" /* atomically replace thread_id (r12) with thread_id+1 (rbx) */ \
                "jnz _sync0_"#X";" \
                "_sync1_"#X":" \
                  "cmp %%r11,(%%r8);" \
                "jne _sync1_"#X";" /* wait untill all threads completed their cmpxchg */ \
                /* Synchronisation Phase 2: TSC (optimization for concurrent start of all threads) */ \
                "cmp $0,%%r13;" \
                "je _skip_tsc_sync_"#X";" /* skip if invariant TSC is not available */ \
                "cmp $0,%%r12;" \
                "jne _wait_"#X";" \
                "rdtsc;shl $32,%%rdx;add %%rdx,%%rax;" \
                "add $50000,%%rax;" /* thread with ID 0 selects start time in future */ \
                "mov %%rax,8(%%r8);mov %%rax,%%r13;" \
                SERIALIZE \
                "jmp _sync2_"#X";" \
                "_wait_"#X":" \
                  "mov 8(%%r8),%%r13;" \
                  "cmp $1,%%r13;" /*  threads with ID >0 wait until start time is defined */ \
                "je _wait_"#X";" \
                "_sync2_"#X":" \
                  "rdtsc;shl $32,%%rdx;add %%rdx,%%rax;" \
                  "cmp %%rax,%%r13;" /* all threads wait until starting time is reached */ \
                "jg _sync2_"#X";" \
                "_skip_tsc_sync_"#X":"

#define LOOP_OVERHEAD_COMP 0x100
#define FLUSH(X)  (1<<(X-1))

#define HUGEPAGES_OFF  0x01
#define HUGEPAGES_ON   0x02

#define LIFO           0x01
#define FIFO           0x02

/* coherency states */
#define MODE_EXCLUSIVE 0x01
#define MODE_MODIFIED  0x02
#define MODE_INVALID   0x04
#define MODE_SHARED    0x08
#define MODE_OWNED     0x10
#define MODE_FORWARD   0x20
#define MODE_RDONLY    0x40
#define MODE_MUW       0x80
#define MODE_DISABLED  0x00

/* thread functions */
#define THREAD_INIT            1
#define THREAD_STOP            2
#define THREAD_USE_MEMORY      3
#define THREAD_WAIT            4
#define THREAD_WORK            7

/* default value for accessing each cacheline - updated with hw_detect information if available */
#define STRIDE        64


#define REGION_L1 1
#define REGION_L2 2
#define REGION_L3 3
#define REGION_RAM 4

/* definitions to add the selected number of "nop" instructions (BENCHIT_KERNEL_NOPCOUNT) into the assembler code */
#ifndef NOPCOUNT
#define NOPCOUNT 0
#endif
#define _nop0 ""
#define _nop1 "nop;"_nop0
#define _nop2 "nop;"_nop1
#define _nop3 "nop;"_nop2
#define _nop4 "nop;"_nop3
#define _nop5 "nop;"_nop4
#define _nop6 "nop;"_nop5
#define _nop7 "nop;"_nop6
#define _nop8 "nop;"_nop7
#define _nop9 "nop;"_nop8
#define _nop10 "nop;"_nop9
#define _donop(x) _nop ## x       //_donop(n)     -> _nopn
#define NOP(x) _donop(x)          //NOP(NOPCOUNT) -> _donop(n)

/* definitions to add prefetch instructions according to BENCHIT_KERNEL_LINE_PREFETCH setting */
#ifndef LINE_PREFETCH
#define LINE_PREFETCH 0
#endif
#if LINE_PREFETCH == 0
#define PREFETCH(lines,offset,reg) ""
#else
#define _doprefetch(lines,offset,reg) "prefetcht0 "#offset"+64*"#lines"(%%"#reg");"
#define PREFETCH(lines,offset,reg) _doprefetch(lines,offset,reg)       //PREFETCH(LINE_PREFETCH,offset,reg) -> _doprefetch(n,offset,reg)
#endif


/** The data structure that holds all the global data.
 */
typedef struct mydata
{
   char* buffer;
   char* cache_flush_area;
   pthread_t *threads;
   struct threaddata *threaddata;
   cpu_info_t *cpuinfo;                                 //40  
   int *threads_per_package;
   long long *INT_INIT;
   double *FP_INIT;                                     //+24 
   unsigned int settings;
   unsigned int loop_overhead;
   unsigned short num_threads;
   unsigned short num_results;
   unsigned char hugepages;
   unsigned char extra_clflush;                         
   unsigned char flush_share_cpu;                       //+15  
   unsigned char padding1[49];                          //+49 = 128
   unsigned long long dummy_cachelines1[16];            // separate exclusive data from shared data
   #ifdef USE_PAPI
   long long *values;
   double *papi_results;
   int Eventset;
   int num_events;                                      //(24) 
   #endif
   int *thread_comm;                                    //+8   
   volatile unsigned long long synch[2];
   volatile unsigned int running_threads;               //+20  
   volatile unsigned short ack;
   volatile unsigned short done;                        //+4 
   #ifdef USE_PAPI
   unsigned char padding2[8];                           //24+8+20+4+8  = 64
   #else
   unsigned char padding2[32];                          //   8+20+4+32 = 64
   #endif
   #ifdef USE_VTRACE
   unsigned int *cid_pfm;
   unsigned int *gid_pfm;   
   unsigned int *cid_papi;
   unsigned int *gid_papi;
   #endif
   //TODO unsigned char padding3[]
   unsigned long long end_dummy_cachelines[16];         // avoid prefetching other memory when accessing mydata_t structure
} mydata_t;

/* data needed by each thread */
typedef struct threaddata
{
   volatile mydata_t *data;
   char* buffer;
   char* cache_flush_area;
   cpu_info_t *cpuinfo;                                 //32  
   volatile unsigned long long aligned_addr;  
   unsigned long long start_ts;     
   unsigned long long end_ts;                           //+24  
   unsigned long long buffersize;
   unsigned long long memsize;				//+16  
   unsigned long long length;
   unsigned int package;                                //+12   
   unsigned int thread_id;
   unsigned int accesses;
   unsigned int settings;
   unsigned int alignment;
   unsigned int offset;
   unsigned int cpu_id;                                 
   unsigned int mem_bind;                               //+28 
   unsigned int thread_offset;
   unsigned char FUNCTION;
   unsigned char BURST_LENGTH;                          //+8  
   #ifdef USE_PAPI
   long long *values;
   double *papi_results;
   int Eventset;
   int num_events;                                      //(+24)
   #endif
   #ifdef USE_PAPI
   unsigned char padding1[48];                          //120+24+48 = 192
   #else
   unsigned char padding1[8];                          //120+8 = 128
   #endif
   #ifdef USE_VTRACE
   int region;
   #endif
   //TODO unsigned char padding2[]
   unsigned long long end_dummy_cachelines[16];         //avoid prefetching following data 
} threaddata_t;

/** Initializes the random number generator with the values given to the function.
 *  formula: r(n+1) = (a*r(n)+b)%m
 *  sequence generated by calls of _random() is a permutation of values from 0 to max-1
 */
void _random_init(int start,int max);
/** returns a pseudo random number
 *  do not use this function without a prior call to _random_init()
 */
unsigned long long _random(void);

/* measure overhead of empty loop */
int asm_loop_overhead(int n);

 
/* function that performs the measurement */
void _work(unsigned long long memsize, int offset, int function, int burst_length,volatile mydata_t* data, double **results);

/* loop executed by all threads, except the master thread */
void *thread(void *threaddata);

#endif
