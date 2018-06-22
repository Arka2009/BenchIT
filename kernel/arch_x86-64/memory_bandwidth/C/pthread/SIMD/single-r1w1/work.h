/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id$
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* Kernel: measures combined bandwidth of one read and one write stream located in different cache levels or memory of certain CPUs.
 *******************************************************************/

#ifndef __WORK_H
#define __WORK_H

#include <mm_malloc.h>
#include <pthread.h>
#include <numa.h>
#include "arch.h"

#define KERNEL_DESCRIPTION  "single threaded memory bandwidth (load-store 1:1)"
#define CODE_SEQUENCE       "mov mem -> reg; mov reg -> mem"
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


#define LOOP_OVERHEAD_COMP 0x100
#define OPT_FLUSH_CPU0  0x200
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
#define THREAD_PREFETCH_CODE   5
#define THREAD_FLUSH           6

/* default value for accessing each cacheline - updated with hw_detect information if available */
#define STRIDE        64

/* memory layout options */
#define LAYOUT_CONT        0x01
#define LAYOUT_FIXED       0x02
#define LAYOUT_ALT1        0x04
#define LAYOUT_ALT2        0x08

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

#ifndef AVX_STARTUP_REG_OPS
#define AVX_STARTUP_REG_OPS 0
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
   double factor;
   double init_value;
   unsigned long long buffersize;                       //+24 
   unsigned int FRST_SHARE_CPU;
   unsigned int NUM_SHARED_CPUS;
   unsigned int alignment;                              //+12  
   unsigned int settings;
   unsigned int loop_overhead;
   unsigned short num_threads;
   unsigned short num_results;
   unsigned char hugepages;
   unsigned char extra_clflush;                         
   unsigned char flush_share_cpu;                       //+15  
   unsigned char offset;
   unsigned char burst_length;
   unsigned char function;
   unsigned char runs;                                  //+4  
   unsigned char NUM_FLUSHES;
   unsigned char NUM_USES;
   unsigned char FLUSH_MODE;
   unsigned char USE_DIRECTION;                         //+4
   unsigned char USE_MODE_R;
   unsigned char USE_MODE_W;
   unsigned char method;
   unsigned char layout;
   unsigned char read_local;
   unsigned char write_local;
   unsigned char ENABLE_CODE_PREFETCH;                  //+7
   unsigned char padding1[22];                          //+22 = 128
   unsigned long long dummy_cachelines1[16];            // separate exclusive data from shared data
   #ifdef USE_PAPI
   long long *values;
   double *papi_results;
   int Eventset;
   int num_events;                                      //(24) 
   #endif
   int *thread_comm;                                    //+8   
   volatile unsigned short ack;
   volatile unsigned short done;                        //+4 
   #ifdef USE_PAPI
   unsigned char padding2[28];                          //24+8+4+28 = 64
   #else
   unsigned char padding2[52];                          //   8+4+52 = 64
   #endif
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
   unsigned int thread_id;
   unsigned int accesses;
   unsigned int settings;
   unsigned int alignment;
   unsigned int offset;
   unsigned int cpu_id;                                 
   unsigned int mem_bind;                               //+28 
   unsigned char NUM_FLUSHES;
   unsigned char NUM_USES;
   unsigned char FLUSH_MODE;
   unsigned char USE_DIRECTION;                         //+4
   unsigned char USE_MODE_R;
   unsigned char USE_MODE_W;                            //+2
   unsigned char padding1[22];                          //+30 = 128
   unsigned long long end_dummy_cachelines[16];         //avoid prefetching following data 
} threaddata_t;

typedef struct parameters param_t;
struct parameters
{
  void *flushaddr;
  param_t *thread_params;                               // 16 byte
  param_t *share_cpu_params;
  unsigned long long addr_1;                            // 32 byte
  unsigned long long addr_2;
  unsigned long long rax;                               // 48 byte
  unsigned long long passes;
  unsigned long long memsize;                           // 64 byte
  double value;
  unsigned long long tmax;                              // 80 byte
  double factor;
  int thread_id;
  int i;                                                // 92 byte
  int j;
  unsigned int runs;                                    // 104 byte
  unsigned int iter;
  unsigned int alignment;
  unsigned int flushsize;                               // 116 byte
  unsigned char use_mode_1;
  unsigned char use_mode_2;
  unsigned char default_use_mode_1;
  unsigned char default_use_mode_2;                     // 120 byte
  unsigned char use_direction;
  unsigned char num_uses;
  unsigned char layout;
  unsigned char accesses_per_loop;                      // 124 byte
  unsigned char num_flushes;
  unsigned char flush_mode;
  unsigned char read_local;
  unsigned char write_local;                            // 128 byte
  #ifdef USE_PAPI
  long long* values;
  int Eventset;
  int num_events;                                       // 16 byte
  char padding1[48];                                    // 64 byte
  #endif
  unsigned long long end_dummy_cachelines[16]; 	        //avoid prefetching following data 
};

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
void _work(unsigned long long memsize,volatile mydata_t* data, double **results);

/* loop executed by all threads, except the master thread */
void *thread(void *threaddata);

#endif
