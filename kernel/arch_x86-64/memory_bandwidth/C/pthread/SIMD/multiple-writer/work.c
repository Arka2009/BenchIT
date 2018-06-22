/******************************************************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id$
 * For license details see COPYING in the package base directory
 ******************************************************************************************************/
/* Kernel: measures aggregate write bandwidth of multiple parallel threads for cache levels and main memory.
 ******************************************************************************************************/
 
/*
 * TODO  - check malloc and mmap return values for errors and abort if alocation of buffers fails
 *       - adopt cache and TLB parameters to refer to identifiers returned by 
 *         the hardware detection
 *       - optional global or local alloc of flush buffer
 *       - add manual instrumentation for VampirTracce
 *       - improve cacheflush algorithm to take the minimal cachesize per core into acount
 *         (e.g. 2 Threads on 1 Package have 8 MB in Nehalem, 2 Threads on 2 Packages 16 MB,
 *          Shanghai has 8 MB for 4 Threads, 7 MB for 2 Threads in one package)
 *       - share data between threads (modified and unmodified)
 *       - memory layout improvements (as for single-r1w1)
 */

#include "interface.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <time.h>
#include <math.h>
#include <pthread.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <assert.h>
#include <errno.h>
#include <unistd.h>
#include <limits.h>

#include "work.h"

#ifdef USE_PAPI
#include <papi.h>
#endif


/* user defined maximum value of random numbers returned by _random() */
static unsigned long long random_max=0;

/* parameters for random number generator 
 *  formula: random_value(n+1) = (rand_a*random_value(n)+rand_b)%rand_m
 *  rand_fix: rand_fix=(rand_a*rand_fix+rand_b)%rand_m
 *        - won't be used as start_value
 *        - can't be reached by random_value, however special care is taken that rand_fix will also be returned by _random()
 */
static unsigned long long random_value=0;
static unsigned long long rand_a=0;
static unsigned long long rand_b=0;
static unsigned long long rand_m=1;
static unsigned long long rand_fix=0;

/* table of prime numbers needed to generate parameters for random number generator */
int *p_list=NULL;
int p_list_max=0;
int pos=0;

/* variables for prime factorization needed to generate parameters for random number generator */
long long parts [64];
int part_count;
long long number;
int max_factor;

/** checks if value is prime
 *  has to be called with all prime numbers < sqrt(value)+1 prior to the call with value
 */
static int isprime(unsigned long long value)
{
  int i;
  int limit = (int) trunc(sqrt((double) value)) +1;
  for (i=0;i<=pos;i++){
      if (p_list[i]>limit) break;
      if (value==(unsigned long long)p_list[i]) return 1;
      if (value%p_list[i]==0) return 0;
  }
  if (pos < p_list_max -1){
     pos++;
     p_list[pos]=value;
  }
  else
   if (p_list[pos]<limit) 
      for (i=p_list[pos];i<=limit;i+=2){
        if (value%i==0) return 0;
      }
  return 1;
}

/** checks if value is a prime factor of global variable number
 *  has to be called with all prime numbers < sqrt(value)+1 prior to the call with value
 */
static int isfactor(int value)
{
  if (value<p_list[p_list_max-1]) if (!isprime(value)) return 0;
  if (number%value==0){
     parts[part_count]=value;
     while (number%value==0){
       number=number/value;
     }
     part_count++;
     max_factor = (int) trunc(sqrt((double) number))+1;
  }
  return 1;
}

/** calculates (x^y)%m
 */
static unsigned long long potenz(long long x, long long y, long long m)
{
   unsigned long long res=1,mask=1;

   if (y==0) return 1;if (y==1) return x%m;

   assert(y==(y&0x00000000ffffffffULL));
   assert(x==(x&0x00000000ffffffffULL));
   assert(m==(m&0x00000000ffffffffULL));
   
   mask = mask<<63;
   while ((y&mask)==0) mask= mask >> 1;
   do{
        if (y&mask){
            res=(res*x)%m;
            res=(res*res)%m;
        }
        else res=(res*res)%m;
        mask = mask >> 1;
   }
   while (mask>1);
   if (y&mask) res=(res*x)%m;

   return res;
}

/** checks if value is a primitive root of rand_m
 */
static int isprimitiveroot(long long value)
{
  long long i,x,y;
  for (i=0;i<part_count;i++){
      x = value;
      y = (rand_m-1)/parts[i];     
      if (potenz(x,y,rand_m)==1) return 0;
  }
  return 1;
}

/** returns a pseudo random number
 *  do not use this function without a prior call to _random_init()
 */
unsigned long long _random(void)
{
  if (random_max==0) return -1;
  do{
    random_value = (random_value * rand_a + rand_b)%rand_m;
  }
  while (((random_value>random_max)&&(rand_fix<random_max))||((random_value>=random_max)&&(rand_fix>=random_max)));
  /* hide fixpoint to ensure that each number < random_max is eventually returned (generate permutation of 0..random_max-1) */
  if (random_value<rand_fix) return random_value;
  else return random_value-1;
}

/** Initializes the random number generator with the values given to the function.
 *  formula: r(n+1) = (a*r(n)+b)%m
 *  sequence generated by calls of _random() is a permutation of values from 0 to max-1
 */
void _random_init(int start,int max)
{
  int i;
  unsigned long long x,f1,f2;

  random_max = (unsigned long long) max;
  if (random_max==0) return;
  /* allocate memory for prime number table */
  if ((((int) trunc(sqrt((double) random_max)) +1)/2+1)>p_list_max){
    p_list_max=((int) trunc(sqrt((double) random_max)) +1)/2+1;
    p_list=realloc(p_list,p_list_max*sizeof(int));
    if (p_list==NULL){
      while(p_list==NULL){
        p_list_max=p_list_max/2;
        p_list=calloc(p_list_max,sizeof(int));
        assert(p_list_max>2);
      }
      pos=0;
    }
    if (pos==0){
      p_list[0]=2;
      p_list[1]=3;
      pos++;
    }
  }

  /* setup parameters rand_m, rand_a, rand_b, and rand_fix*/
  rand_m=1;
  do{
    rand_m+=2;
    rand_a=0;

    /* find a prime number for rand_m, larger than random_max*/
    while ((pos<p_list_max-1)){rand_m+=2;isprime(rand_m);} /* fill prime number table */
    if (rand_m<=random_max) {rand_m=random_max+1;if(rand_m%2==0)rand_m++;}
    while (!isprime(rand_m)) rand_m+=2;
  
    /* set rand_b to a value between rand_m/4 and 3*rand_m/4 */
    rand_b=start%(rand_m/2)+rand_m/4;
    rand_b|=1; // avoid b=0 for m=3, ensures b is odd
  
    /* prime factorize rand_m-1, as those are good candidates for primitive roots of rand_m */
    number=rand_m-1;
    max_factor = (int) trunc(sqrt((double) number))+1;
    part_count=0;
    for(i=0;i<p_list_max;i++) isfactor(p_list[i]);
    i=p_list[p_list_max-1];
    while (i<max_factor){
       isfactor(i);
       i+=2;
    }
    if (number>1){
       parts[part_count]=number;
       part_count++;
    }
  
    /* find a value for rand_a that is a primitive root of rand_m and != rand_m/2 
     * rand_a = rand_m/2 has a high likelyhood to generate a regular pattern */
    for (i=0;i<part_count;i++){
      if ((rand_m/2!=parts[i])&&(parts[i]*parts[i]>rand_m)&&(isprimitiveroot(parts[i]))) {rand_a=parts[i];break;}
    }
    
    /* find fixpoint 
     * check all possibilities: fix = a * fix + b, fix = (a * fix + b) - m, fix = (a * fix +b) - 2m, ... , fix = (a * fix +b) - (a * m)
     * b is != 0, thus fix = a * fix + b (i.e., fix = 0) cannot happen 
     */
    rand_fix=0;
    if (rand_a!=0) for(x=1;x<=rand_a;x++){        // check for '- (n * m)' with 1 <= n <= a, '- (0 * m)' does not happen (see above)
        f1 = ((x*rand_m) -rand_b ) / (rand_a-1);  // f1 = (a * f1 + b) - (x * m) -> 0 = (a-1) * f1 + b - (x * m) -> f1 = ((x * m) -b) / (a - 1)
        f2 = ((f1*rand_a)+rand_b) % rand_m;       // check if f1 is the fixpoint (this only happens for the right x)
        if (f1==f2) {rand_fix=f1;break;}
    }    
  }
  /* condition 1 avoids small values for rand_a in order to generate highly fluctuating sequences,
   * condition 2 avoids that a combination of rand_m, rand_a, and rand_b is choosen that does not have a fixpoint (should never happen for prime rand_m)
   */
  while((rand_a*rand_a<rand_m)||(rand_fix==0));


  /* generator is initialized with the user defined start value */
  random_value= (unsigned long long)start%rand_m;
  if (random_value==rand_fix) random_value=0;  /* replace with 0 if it equals rand_fix */
}

/*
 * use a block of memory to ensure it is in the caches afterwards
 * MODE_EXCLUSIVE: - cache line will be exclusive in cache of calling CPU
 * MODE_MODIFIED:  - cache line will be modified in cache of calling CPU
 * MODE_INVALID:   - cache line will be invalid in all caches
 * MODE_SHARED/MODE_OWNED/MODE_FORWARD:
 *   - these modes perform a read-only access (on SHARE_CPU)
 *   - together with accesses on another CPU with MODE_{EXCLUSIVE|MODIFIED} cache line will be in the
 *     desired coherency state in the cache of the OTHER CPU, and SHARED in the cache of SHARE_CPU
 *     (see USE MODE ADAPTION in file work.c)
 */
static inline int use_memory(void* buffer,void* flush_buffer,unsigned long long memsize,int mode,int direction,int repeat,cpu_info_t cpuinfo)
{
   int i,j,tmp=0xd08a721b;
   unsigned long long stride = 64;

   for (i=cpuinfo.Cachelevels;i>0;i--)
   {
     if (cpuinfo.Cacheline_size[i-1]<stride) stride=cpuinfo.Cacheline_size[i-1];
   }

   if ((mode==MODE_MODIFIED)||(mode==MODE_EXCLUSIVE)||(mode==MODE_INVALID))
   {
     //invalidate remote caches
     __asm__ __volatile__(
       		"_use_mem_inv_loop:"
       		"mov %%rbx, (%%rax);"
       		"add %%rcx, %%rax;"
       		"sub $1, %%rdx;"
       		"jnz _use_mem_inv_loop;"
       		:: "a" ((unsigned long long)buffer), "b" (tmp), "c" (stride), "d" (memsize/stride) : "memory");

     //invalidate local caches
     if (!cpuinfo.disable_clflush) clflush(buffer,memsize,cpuinfo);
     else {
       __asm__ __volatile__(
       		"_use_mem_flush_loop:"
       		"mov %%rbx, (%%rax);"
       		"add %%rcx, %%rax;"
       		"sub $1, %%rdx;"
       		"jnz _use_mem_flush_loop;"
       		:: "a" ((unsigned long long)flush_buffer), "b" (tmp), "c" (stride), "d" (((cpuinfo.D_Cache_Size_per_Core*cpuinfo.EXTRA_FLUSH_SIZE)/50)/stride) : "memory");
       clflush(flush_buffer,(cpuinfo.D_Cache_Size_per_Core*cpuinfo.EXTRA_FLUSH_SIZE)/50,cpuinfo);
     }
   } 
   
      __asm__ __volatile__("mfence;"::: "memory");
  

   j=repeat;

   if (mode==MODE_MODIFIED)
   {
     while(j--)
     {
       if (direction==FIFO){
         __asm__ __volatile__(
       		"_use_mem_write_loop_fifo:"
       		"mov %%rbx, (%%rax);"
       		"add %%rcx, %%rax;"
       		"sub $1, %%rdx;"
       		"jnz _use_mem_write_loop_fifo;"
       		:: "a" ((unsigned long long)buffer), "b" (tmp), "c" (stride), "d" (memsize/stride) : "memory");
       }
       if (direction==LIFO){
         __asm__ __volatile__(
       		"_use_mem_write_loop_lifo:"
       		"sub %%rcx, %%rax;"
       		"mov %%rbx, (%%rax);"       		
       		"sub $1, %%rdx;"
       		"jnz _use_mem_write_loop_lifo;"
       		:: "a" ((unsigned long long)buffer+memsize), "b" (tmp), "c" (stride), "d" (memsize/stride) : "memory");
       }
     }
   } 
 
   if ((mode==MODE_EXCLUSIVE)||(mode==MODE_SHARED)||(mode==MODE_OWNED)||(mode==MODE_FORWARD)||(mode==MODE_RDONLY)) 
   {
     while(j--)
     {
       if (direction==FIFO){
         __asm__ __volatile__(
       		"_use_mem_read_loop_fifo:"
       		"add (%%rax), %%rbx;"
       		"add %%rcx, %%rax;"
       		"sub $1, %%rdx;"
       		"jnz _use_mem_read_loop_fifo;"
       		: "=b" (tmp) : "a" ((unsigned long long)buffer), "c" (stride), "d" (memsize/stride));
       }
       if (direction==LIFO) {
         __asm__ __volatile__(
       		"_use_mem_read_loop_lifo:"
       		"sub %%rcx, %%rax;"
       		"add (%%rax), %%rbx;"
       		"sub $1, %%rdx;"
       		"jnz _use_mem_read_loop_lifo;"
       		: "=b" (tmp) : "a" ((unsigned long long)buffer+memsize), "c" (stride), "d" (memsize/stride));
       }
     }
   }  

      __asm__ __volatile__("mfence;"::: "memory");


   return tmp;
}

/**
 * flushes data from the specified cachelevel
 * @param level the cachelevel that should be flushed
 * @param num_flushes number of accesses to each cacheline
 * @param mode MODE_EXCLUSIVE: fill cache with dummy data in state exclusive
 *             MODE_MODIFIED:  fill cache with dummy data in state modified (causes write backs of dirty data later on)
 *             MODE_INVALID:   invalidate cache (requires clflush)
 *             MODE_RDONLY:    fill cache with valid dummy data, does not perform any write operations, state can be exclusive or shared/forward
 * @param buffer pointer to a memory area, size of the buffer has to be 
 *               has to be larger than 2 x sum of all cachelevels <= level
 */
static inline int cacheflush(int level,int num_flushes,int mode,void* buffer,cpu_info_t cpuinfo)
{
  unsigned long long stride=cpuinfo.Cacheline_size[level-1]/num_flushes;
  unsigned long long size=0;
  int i,j,tmp=0x0fa38b09;

  if (level>cpuinfo.Cachelevels) return -1;

  //exclusive caches
  if ((!strcmp(cpuinfo.vendor,"AuthenticAMD")) && (cpuinfo.family != 21))for (i=0;i<level;i++)
  {
     if (cpuinfo.Cache_unified[i]) size+=cpuinfo.U_Cache_Size[i];
     else size+=cpuinfo.D_Cache_Size[i];
  }
  //inclusive L2, exclusive L3
  if ((!strcmp(cpuinfo.vendor,"AuthenticAMD")) && (cpuinfo.family == 21))
  {
    if (level<3)
    {
      i=level-1;
   	  if (cpuinfo.Cache_unified[i]) size=cpuinfo.U_Cache_Size[i];
      else size=cpuinfo.D_Cache_Size[i];
    }
    else for (i=1;i<level;i++)
    {     
     if (cpuinfo.Cache_unified[i]) size+=cpuinfo.U_Cache_Size[i];
     else size+=cpuinfo.D_Cache_Size[i];
    }
  }
  //inclusive caches
  if (!strcmp(cpuinfo.vendor,"GenuineIntel"))
  {
     i=level-1;
     if (cpuinfo.Cache_unified[i]) size=cpuinfo.U_Cache_Size[i];
     else size=cpuinfo.D_Cache_Size[i];
  } 

  size*=cpuinfo.EXTRA_FLUSH_SIZE;
  // double amount of accessed memory for LLC flushes and decrease num_flushes
  if (level==cpuinfo.Cachelevels){ 
    size*=2;
    num_flushes/=3;
    num_flushes++;
  }
  size/=100;

  if (stride<sizeof(unsigned int)) stride=sizeof(unsigned int);
  
  if (mode!=MODE_RDONLY){
    j=num_flushes;
    while(j--)
    {
     for (i=0;i<size;i+=stride)
     {
       tmp|=*((int*)((unsigned long long)buffer+i));
       *((int*)((unsigned long long)buffer+i))=tmp;
     }
    }
  }
  if ((mode==MODE_EXCLUSIVE)||(mode==MODE_INVALID)){
    clflush(buffer,size,cpuinfo);
  }
  if ((mode==MODE_EXCLUSIVE)||(mode==MODE_RDONLY)){
    j=num_flushes;
    while(j--)
    {
     for (i=0;i<size;i+=stride)
     {
       tmp|=*((int*)((unsigned long long)buffer+i));
     }
     *((int*)((unsigned long long)buffer+i))=tmp;
    }
  }

  return tmp;
}


/*
 * flush all caches that are smaller than the specified memory size, including shared caches
 * with respect to reduced capacity of caches, that are shared between threads (NOTE: worst case assumptions are
 * made, i.e flushes might start at smaller memsizes than requiered [e.g] when running 2 threads on a 2 socket
 * system with dual core processors it is assumed that both threads are running on a single package)
 * TODO: use cache shared map from sysfs and cpu bindings to figure out what is actally shared
 */
static inline void flush_caches(void* buffer,unsigned long long memsize,int settings,int num_flushes,int flush_mode,void* flush_buffer,cpu_info_t *cpuinfo,int id,int num_threads)
{
   int i,j,cachesize;
   for (i=cpuinfo->Cachelevels;i>0;i--)
   {   
     if (settings&FLUSH(i))
     {
       cachesize=cpuinfo->U_Cache_Size[i-1]+cpuinfo->D_Cache_Size[i-1];
       if (cpuinfo->Cache_shared[i-1]>1)
       { 
          if (num_threads<=cpuinfo->Cache_shared[i-1]) cachesize/=num_threads;
          else cachesize/=cpuinfo->Cache_shared[i-1];
       }
       /* add size of lower cache levels in case of non-inclusive caches*/
       /* TODO num threads * per core caches*/
       if (!strcmp(cpuinfo->vendor,"AuthenticAMD"))
       {
         for (j=i-1;j>0;j--)
         {
           cachesize+=cpuinfo->U_Cache_Size[j-1]+cpuinfo->D_Cache_Size[j-1];
         }
       }
       if (memsize>cachesize)
       {
         if (cpuinfo->Cachelevels>i)cacheflush(i,num_flushes,flush_mode,flush_buffer,*(cpuinfo));
         else if (clflush( buffer , memsize, *(cpuinfo) )) cacheflush(i,num_flushes,flush_mode,flush_buffer,*(cpuinfo));
         break;
       }
     }
   }
}



/* measure overhead of empty loop */
int asm_loop_overhead(int n)
{
   unsigned long long a,b,c,d,i;
   static unsigned long long ret=1000000;

   for (i=0;i<n;i++){
        /* Output: RAX: stop timestamp 
         *         RBX: start timestamp
         */
       __asm__ __volatile__(
                "mov $1,%%rcx;"       
                TIMESTAMP
                SERIALIZE
                "push %%rax;"
//                "jmp _work_loop_overhead;"
//                ".align 64,0x0;"
//                "_work_loop_overhead:"
//                "sub $1,%%rcx;"
//                "jnz _work_loop_overhead;"
                SERIALIZE    
                TIMESTAMP
                "pop %%rbx;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
        );
        if ((a-b)<ret) ret=(a-b);
   }			
  return (int)ret;
}

/** assembler implementation of bandwidth measurement using movdqa instruction
 */
static double asm_work_movdqa(unsigned long long addr, unsigned long long accesses, unsigned long long burst_length,unsigned long long call_latency,unsigned long long freq,unsigned long long running_threads,unsigned long long id, volatile void * sync_ptr,threaddata_t* data) __attribute__((noinline));
static double asm_work_movdqa(unsigned long long addr, unsigned long long accesses, unsigned long long burst_length,unsigned long long call_latency,unsigned long long freq,unsigned long long running_threads,unsigned long long id, volatile void * sync_ptr,threaddata_t* data)
{
   unsigned long long passes;
   double ret;
   unsigned long long a,b,c,d;
   int i;
   
   #ifdef USE_PAPI
    if ((!id) && (data->num_events)) PAPI_reset(data->Eventset);
   #endif


   switch (burst_length)
   {

    case 1:
      passes=accesses/64;
      #if (ACCESS_STRIDE>0)
      passes*=16;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movdqa_1)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movdqa_1;"
                ".align 64,0x0;"
                "_work_loop_movdqa_1:"
#if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movdqa %%xmm0, 0(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 16(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 32(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 48(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqa %%xmm0, 64(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 80(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 96(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 112(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqa %%xmm0, 128(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 144(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 160(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 176(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqa %%xmm0, 192(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 208(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 224(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 240(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqa %%xmm0, 256(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 272(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 288(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 304(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqa %%xmm0, 320(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 336(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 352(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 368(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqa %%xmm0, 384(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 400(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 416(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 432(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqa %%xmm0, 448(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 464(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 480(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 496(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqa %%xmm0, 512(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 528(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 544(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 560(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqa %%xmm0, 576(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 592(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 608(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 624(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqa %%xmm0, 640(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 656(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 672(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 688(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqa %%xmm0, 704(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 720(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 736(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 752(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqa %%xmm0, 768(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 784(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 800(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 816(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqa %%xmm0, 832(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 848(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 864(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 880(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqa %%xmm0, 896(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 912(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 928(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 944(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqa %%xmm0, 960(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 976(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 992(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 1008(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_64(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movdqa_1;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*64);
        break;

    case 2:
      passes=accesses/64;
      #if (ACCESS_STRIDE>0)
      passes*=16;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movdqa_2)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movdqa_2;"
                ".align 64,0x0;"
                "_work_loop_movdqa_2:"
#if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movdqa %%xmm0, 0(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 16(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 32(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 48(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqa %%xmm0, 64(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 80(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 96(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 112(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqa %%xmm0, 128(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 144(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 160(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 176(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqa %%xmm0, 192(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 208(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 224(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 240(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqa %%xmm0, 256(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 272(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 288(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 304(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqa %%xmm0, 320(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 336(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 352(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 368(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqa %%xmm0, 384(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 400(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 416(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 432(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqa %%xmm0, 448(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 464(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 480(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 496(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqa %%xmm0, 512(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 528(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 544(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 560(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqa %%xmm0, 576(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 592(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 608(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 624(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqa %%xmm0, 640(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 656(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 672(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 688(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqa %%xmm0, 704(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 720(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 736(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 752(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqa %%xmm0, 768(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 784(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 800(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 816(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqa %%xmm0, 832(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 848(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 864(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 880(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqa %%xmm0, 896(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 912(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 928(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 944(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqa %%xmm0, 960(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 976(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 992(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 1008(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_64(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movdqa_2;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*64);
        break;

    case 3:
      passes=accesses/66;
      #if (ACCESS_STRIDE>0)
      passes*=16;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movdqa_3)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movdqa_3;"
                ".align 64,0x0;"
                "_work_loop_movdqa_3:"
#if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movdqa %%xmm0, 0(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 16(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 32(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 48(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqa %%xmm1, 64(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 80(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 96(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 112(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqa %%xmm2, 128(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 144(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 160(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 176(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqa %%xmm0, 192(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 208(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 224(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 240(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqa %%xmm1, 256(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 272(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 288(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 304(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqa %%xmm2, 320(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 336(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 352(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 368(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqa %%xmm0, 384(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 400(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 416(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 432(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqa %%xmm1, 448(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 464(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 480(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 496(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqa %%xmm2, 512(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 528(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 544(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 560(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqa %%xmm0, 576(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 592(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 608(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 624(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqa %%xmm1, 640(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 656(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 672(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 688(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqa %%xmm2, 704(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 720(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 736(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 752(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqa %%xmm0, 768(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 784(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 800(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 816(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqa %%xmm1, 832(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 848(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 864(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 880(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqa %%xmm2, 896(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 912(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 928(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 944(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqa %%xmm0, 960(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 976(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 992(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm0, 1008(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,rbx)
                "movdqa %%xmm1, 1024(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 1040(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_64(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_65(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                "add $1056,%%rbx;"
		#else
		INC_66(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movdqa_3;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*66);
        break;

    case 4:
      passes=accesses/64;
      #if (ACCESS_STRIDE>0)
      passes*=16;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movdqa_4)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movdqa_4;"
                ".align 64,0x0;"
                "_work_loop_movdqa_4:"
#if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movdqa %%xmm0, 0(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 16(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 32(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 48(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqa %%xmm0, 64(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 80(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 96(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 112(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqa %%xmm0, 128(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 144(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 160(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 176(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqa %%xmm0, 192(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 208(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 224(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 240(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqa %%xmm0, 256(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 272(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 288(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 304(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqa %%xmm0, 320(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 336(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 352(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 368(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqa %%xmm0, 384(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 400(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 416(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 432(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqa %%xmm0, 448(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 464(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 480(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 496(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqa %%xmm0, 512(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 528(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 544(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 560(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqa %%xmm0, 576(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 592(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 608(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 624(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqa %%xmm0, 640(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 656(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 672(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 688(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqa %%xmm0, 704(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 720(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 736(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 752(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqa %%xmm0, 768(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 784(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 800(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 816(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqa %%xmm0, 832(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 848(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 864(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 880(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqa %%xmm0, 896(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 912(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 928(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 944(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqa %%xmm0, 960(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 976(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 992(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 1008(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_64(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movdqa_4;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*64);
        break;

    case 8:
      passes=accesses/64;
      #if (ACCESS_STRIDE>0)
      passes*=16;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movdqa_8)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movdqa_8;"
                ".align 64,0x0;"
                "_work_loop_movdqa_8:"
#if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movdqa %%xmm0, 0(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 16(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 32(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 48(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqa %%xmm4, 64(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm5, 80(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm6, 96(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm7, 112(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqa %%xmm0, 128(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 144(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 160(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 176(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqa %%xmm4, 192(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm5, 208(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm6, 224(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm7, 240(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqa %%xmm0, 256(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 272(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 288(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 304(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqa %%xmm4, 320(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm5, 336(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm6, 352(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm7, 368(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqa %%xmm0, 384(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 400(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 416(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 432(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqa %%xmm4, 448(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm5, 464(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm6, 480(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm7, 496(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqa %%xmm0, 512(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 528(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 544(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 560(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqa %%xmm4, 576(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm5, 592(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm6, 608(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm7, 624(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqa %%xmm0, 640(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 656(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 672(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 688(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqa %%xmm4, 704(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm5, 720(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm6, 736(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm7, 752(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqa %%xmm0, 768(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 784(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 800(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 816(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqa %%xmm4, 832(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm5, 848(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm6, 864(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm7, 880(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqa %%xmm0, 896(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm1, 912(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm2, 928(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm3, 944(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqa %%xmm4, 960(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm5, 976(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm6, 992(%%rbx);"NOP(NOPCOUNT)
                "movdqa %%xmm7, 1008(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movdqa,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movdqa,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movdqa,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movdqa,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movdqa,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movdqa,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movdqa,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movdqa,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movdqa,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movdqa,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movdqa,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movdqa,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movdqa,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movdqa,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movdqa,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movdqa,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movdqa,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movdqa,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movdqa,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movdqa,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movdqa,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movdqa,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movdqa,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movdqa,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movdqa,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movdqa,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movdqa,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movdqa,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movdqa,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movdqa,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movdqa,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movdqa,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movdqa,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movdqa,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movdqa,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movdqa,%%xmm7,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_64(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movdqa_8;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*64);
        break;
      default: ret=0.0;break;
   }  
	
  #ifdef USE_PAPI
    if ((!id)&&(data->num_events))
    { 
      PAPI_read(data->Eventset,data->values);
      for (i=0;i<data->num_events;i++)
      {
         if (burst_length==1) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==2) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==3) data->papi_results[i]=(double)data->values[i]/(double)(passes*66);
         if (burst_length==4) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==8) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
      }
    }
    else for (i=0;i<data->num_events;i++) data->papi_results[i]==(double)0;
  #endif		
  return ret;
}

/** assembler implementation of bandwidth measurement using vmovdqa instruction
 */
static double asm_work_vmovdqa(unsigned long long addr, unsigned long long accesses, unsigned long long burst_length,unsigned long long call_latency,unsigned long long freq,unsigned long long running_threads,unsigned long long id, volatile void * sync_ptr,threaddata_t* data) __attribute__((noinline));
static double asm_work_vmovdqa(unsigned long long addr, unsigned long long accesses, unsigned long long burst_length,unsigned long long call_latency,unsigned long long freq,unsigned long long running_threads,unsigned long long id, volatile void * sync_ptr,threaddata_t* data)
{
   unsigned long long passes;
   double ret;
   unsigned long long a,b,c,d;
   int i;
   
   #ifdef USE_PAPI
    if ((!id) && (data->num_events)) PAPI_reset(data->Eventset);
   #endif

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }

   switch (burst_length)
   {

    case 1:
      passes=accesses/32;
      #if (ACCESS_STRIDE>0)
      passes*=32;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(vmovdqa_1)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_vmovdqa_1;"
                ".align 64,0x0;"
                "_work_loop_vmovdqa_1:"
#if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "vmovdqa %%ymm0, 0(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 32(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqa %%ymm0, 64(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 96(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqa %%ymm0, 128(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 160(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqa %%ymm0, 192(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 224(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqa %%ymm0, 256(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 288(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqa %%ymm0, 320(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 352(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqa %%ymm0, 384(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 416(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqa %%ymm0, 448(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 480(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqa %%ymm0, 512(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 544(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqa %%ymm0, 576(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 608(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqa %%ymm0, 640(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 672(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqa %%ymm0, 704(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 736(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqa %%ymm0, 768(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 800(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqa %%ymm0, 832(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 864(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqa %%ymm0, 896(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 928(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqa %%ymm0, 960(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 992(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_32(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_vmovdqa_1;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*32);
        break;

    case 2:
      passes=accesses/32;
      #if (ACCESS_STRIDE>0)
      passes*=32;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(vmovdqa_2)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_vmovdqa_2;"
                ".align 64,0x0;"
                "_work_loop_vmovdqa_2:"
#if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "vmovdqa %%ymm0, 0(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 32(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqa %%ymm0, 64(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 96(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqa %%ymm0, 128(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 160(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqa %%ymm0, 192(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 224(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqa %%ymm0, 256(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 288(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqa %%ymm0, 320(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 352(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqa %%ymm0, 384(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 416(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqa %%ymm0, 448(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 480(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqa %%ymm0, 512(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 544(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqa %%ymm0, 576(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 608(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqa %%ymm0, 640(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 672(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqa %%ymm0, 704(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 736(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqa %%ymm0, 768(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 800(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqa %%ymm0, 832(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 864(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqa %%ymm0, 896(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 928(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqa %%ymm0, 960(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 992(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_32(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_vmovdqa_2;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*32);
        break;

    case 3:
      passes=accesses/33;
      #if (ACCESS_STRIDE>0)
      passes*=32;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(vmovdqa_3)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_vmovdqa_3;"
                ".align 64,0x0;"
                "_work_loop_vmovdqa_3:"
#if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "vmovdqa %%ymm0, 0(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 32(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqa %%ymm2, 64(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 96(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqa %%ymm1, 128(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm2, 160(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqa %%ymm0, 192(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 224(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqa %%ymm2, 256(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 288(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqa %%ymm1, 320(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm2, 352(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqa %%ymm0, 384(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 416(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqa %%ymm2, 448(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 480(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqa %%ymm1, 512(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm2, 544(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqa %%ymm0, 576(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 608(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqa %%ymm2, 640(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 672(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqa %%ymm1, 704(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm2, 736(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqa %%ymm0, 768(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 800(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqa %%ymm2, 832(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm0, 864(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqa %%ymm1, 896(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm2, 928(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqa %%ymm0, 960(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 992(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,rbx)
                "vmovdqa %%ymm2, 1024(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                "add $1056,%%rbx;"
		#else
		INC_33(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_vmovdqa_3;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*33);
        break;

    case 4:
      passes=accesses/32;
      #if (ACCESS_STRIDE>0)
      passes*=32;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(vmovdqa_4)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_vmovdqa_4;"
                ".align 64,0x0;"
                "_work_loop_vmovdqa_4:"
#if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "vmovdqa %%ymm0, 0(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 32(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqa %%ymm2, 64(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm3, 96(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqa %%ymm0, 128(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 160(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqa %%ymm2, 192(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm3, 224(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqa %%ymm0, 256(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 288(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqa %%ymm2, 320(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm3, 352(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqa %%ymm0, 384(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 416(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqa %%ymm2, 448(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm3, 480(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqa %%ymm0, 512(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 544(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqa %%ymm2, 576(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm3, 608(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqa %%ymm0, 640(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 672(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqa %%ymm2, 704(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm3, 736(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqa %%ymm0, 768(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 800(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqa %%ymm2, 832(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm3, 864(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqa %%ymm0, 896(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 928(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqa %%ymm2, 960(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm3, 992(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(vmovdqa,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(vmovdqa,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(vmovdqa,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(vmovdqa,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(vmovdqa,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(vmovdqa,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(vmovdqa,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(vmovdqa,%%ymm3,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_32(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_vmovdqa_4;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*32);
        break;

    case 8:
      passes=accesses/32;
      #if (ACCESS_STRIDE>0)
      passes*=32;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(vmovdqa_8)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_vmovdqa_8;"
                ".align 64,0x0;"
                "_work_loop_vmovdqa_8:"
#if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "vmovdqa %%ymm0, 0(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 32(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqa %%ymm2, 64(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm3, 96(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqa %%ymm4, 128(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm5, 160(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqa %%ymm6, 192(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm7, 224(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqa %%ymm0, 256(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 288(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqa %%ymm2, 320(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm3, 352(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqa %%ymm4, 384(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm5, 416(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqa %%ymm6, 448(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm7, 480(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqa %%ymm0, 512(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 544(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqa %%ymm2, 576(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm3, 608(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqa %%ymm4, 640(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm5, 672(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqa %%ymm6, 704(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm7, 736(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqa %%ymm0, 768(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm1, 800(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqa %%ymm2, 832(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm3, 864(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqa %%ymm4, 896(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm5, 928(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqa %%ymm6, 960(%%rbx);"NOP(NOPCOUNT)
                "vmovdqa %%ymm7, 992(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(vmovdqa,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(vmovdqa,%%ymm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(vmovdqa,%%ymm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(vmovdqa,%%ymm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(vmovdqa,%%ymm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(vmovdqa,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(vmovdqa,%%ymm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(vmovdqa,%%ymm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(vmovdqa,%%ymm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(vmovdqa,%%ymm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(vmovdqa,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(vmovdqa,%%ymm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(vmovdqa,%%ymm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(vmovdqa,%%ymm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(vmovdqa,%%ymm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(vmovdqa,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(vmovdqa,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(vmovdqa,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(vmovdqa,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(vmovdqa,%%ymm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(vmovdqa,%%ymm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(vmovdqa,%%ymm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(vmovdqa,%%ymm7,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_32(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_vmovdqa_8;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*32);
        break;
      default: ret=0.0;break;
   }  
	
  #ifdef USE_PAPI
    if ((!id)&&(data->num_events))
    { 
      PAPI_read(data->Eventset,data->values);
      for (i=0;i<data->num_events;i++)
      {
         if (burst_length==1) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==2) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==3) data->papi_results[i]=(double)data->values[i]/(double)(passes*66);
         if (burst_length==4) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==8) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
      }
    }
    else for (i=0;i<data->num_events;i++) data->papi_results[i]==(double)0;
  #endif		
  return ret;
}

/** assembler implementation of bandwidth measurement using movdqu instruction
 */
static double asm_work_movdqu(unsigned long long addr, unsigned long long accesses, unsigned long long burst_length,unsigned long long call_latency,unsigned long long freq,unsigned long long running_threads,unsigned long long id, volatile void * sync_ptr,threaddata_t* data) __attribute__((noinline));
static double asm_work_movdqu(unsigned long long addr, unsigned long long accesses, unsigned long long burst_length,unsigned long long call_latency,unsigned long long freq,unsigned long long running_threads,unsigned long long id, volatile void * sync_ptr,threaddata_t* data)
{
   unsigned long long passes;
   double ret;
   unsigned long long a,b,c,d;
   int i;
   
   #ifdef USE_PAPI
    if ((!id) && (data->num_events)) PAPI_reset(data->Eventset);
   #endif


   switch (burst_length)
   {

    case 1:
      passes=accesses/64;
      #if (ACCESS_STRIDE>0)
      passes*=16;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movdqu_1)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movdqu_1;"
                ".align 64,0x0;"
                "_work_loop_movdqu_1:"
#if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movdqu %%xmm0, 0(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 16(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 32(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 48(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqu %%xmm0, 64(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 80(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 96(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 112(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqu %%xmm0, 128(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 144(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 160(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 176(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqu %%xmm0, 192(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 208(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 224(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 240(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqu %%xmm0, 256(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 272(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 288(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 304(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqu %%xmm0, 320(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 336(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 352(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 368(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqu %%xmm0, 384(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 400(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 416(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 432(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqu %%xmm0, 448(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 464(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 480(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 496(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqu %%xmm0, 512(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 528(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 544(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 560(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqu %%xmm0, 576(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 592(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 608(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 624(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqu %%xmm0, 640(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 656(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 672(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 688(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqu %%xmm0, 704(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 720(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 736(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 752(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqu %%xmm0, 768(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 784(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 800(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 816(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqu %%xmm0, 832(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 848(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 864(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 880(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqu %%xmm0, 896(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 912(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 928(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 944(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqu %%xmm0, 960(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 976(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 992(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 1008(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_64(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movdqu_1;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*64);
        break;

    case 2:
      passes=accesses/64;
      #if (ACCESS_STRIDE>0)
      passes*=16;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movdqu_2)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movdqu_2;"
                ".align 64,0x0;"
                "_work_loop_movdqu_2:"
#if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movdqu %%xmm0, 0(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 16(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 32(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 48(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqu %%xmm0, 64(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 80(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 96(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 112(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqu %%xmm0, 128(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 144(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 160(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 176(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqu %%xmm0, 192(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 208(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 224(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 240(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqu %%xmm0, 256(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 272(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 288(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 304(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqu %%xmm0, 320(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 336(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 352(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 368(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqu %%xmm0, 384(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 400(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 416(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 432(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqu %%xmm0, 448(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 464(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 480(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 496(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqu %%xmm0, 512(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 528(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 544(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 560(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqu %%xmm0, 576(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 592(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 608(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 624(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqu %%xmm0, 640(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 656(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 672(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 688(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqu %%xmm0, 704(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 720(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 736(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 752(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqu %%xmm0, 768(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 784(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 800(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 816(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqu %%xmm0, 832(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 848(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 864(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 880(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqu %%xmm0, 896(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 912(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 928(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 944(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqu %%xmm0, 960(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 976(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 992(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 1008(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_64(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movdqu_2;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*64);
        break;

    case 3:
      passes=accesses/66;
      #if (ACCESS_STRIDE>0)
      passes*=16;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movdqu_3)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movdqu_3;"
                ".align 64,0x0;"
                "_work_loop_movdqu_3:"
#if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movdqu %%xmm0, 0(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 16(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 32(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 48(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqu %%xmm1, 64(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 80(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 96(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 112(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqu %%xmm2, 128(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 144(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 160(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 176(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqu %%xmm0, 192(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 208(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 224(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 240(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqu %%xmm1, 256(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 272(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 288(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 304(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqu %%xmm2, 320(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 336(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 352(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 368(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqu %%xmm0, 384(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 400(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 416(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 432(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqu %%xmm1, 448(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 464(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 480(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 496(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqu %%xmm2, 512(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 528(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 544(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 560(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqu %%xmm0, 576(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 592(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 608(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 624(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqu %%xmm1, 640(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 656(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 672(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 688(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqu %%xmm2, 704(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 720(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 736(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 752(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqu %%xmm0, 768(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 784(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 800(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 816(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqu %%xmm1, 832(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 848(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 864(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 880(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqu %%xmm2, 896(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 912(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 928(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 944(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqu %%xmm0, 960(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 976(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 992(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm0, 1008(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,rbx)
                "movdqu %%xmm1, 1024(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 1040(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_64(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_65(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                "add $1056,%%rbx;"
		#else
		INC_66(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movdqu_3;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*66);
        break;

    case 4:
      passes=accesses/64;
      #if (ACCESS_STRIDE>0)
      passes*=16;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movdqu_4)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movdqu_4;"
                ".align 64,0x0;"
                "_work_loop_movdqu_4:"
#if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movdqu %%xmm0, 0(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 16(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 32(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 48(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqu %%xmm0, 64(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 80(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 96(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 112(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqu %%xmm0, 128(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 144(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 160(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 176(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqu %%xmm0, 192(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 208(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 224(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 240(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqu %%xmm0, 256(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 272(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 288(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 304(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqu %%xmm0, 320(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 336(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 352(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 368(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqu %%xmm0, 384(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 400(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 416(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 432(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqu %%xmm0, 448(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 464(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 480(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 496(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqu %%xmm0, 512(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 528(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 544(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 560(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqu %%xmm0, 576(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 592(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 608(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 624(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqu %%xmm0, 640(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 656(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 672(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 688(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqu %%xmm0, 704(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 720(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 736(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 752(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqu %%xmm0, 768(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 784(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 800(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 816(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqu %%xmm0, 832(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 848(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 864(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 880(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqu %%xmm0, 896(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 912(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 928(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 944(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqu %%xmm0, 960(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 976(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 992(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 1008(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_64(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movdqu_4;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*64);
        break;

    case 8:
      passes=accesses/64;
      #if (ACCESS_STRIDE>0)
      passes*=16;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movdqu_8)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movdqu_8;"
                ".align 64,0x0;"
                "_work_loop_movdqu_8:"
#if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movdqu %%xmm0, 0(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 16(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 32(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 48(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqu %%xmm4, 64(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm5, 80(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm6, 96(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm7, 112(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqu %%xmm0, 128(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 144(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 160(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 176(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqu %%xmm4, 192(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm5, 208(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm6, 224(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm7, 240(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqu %%xmm0, 256(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 272(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 288(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 304(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqu %%xmm4, 320(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm5, 336(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm6, 352(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm7, 368(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqu %%xmm0, 384(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 400(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 416(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 432(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqu %%xmm4, 448(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm5, 464(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm6, 480(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm7, 496(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqu %%xmm0, 512(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 528(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 544(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 560(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqu %%xmm4, 576(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm5, 592(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm6, 608(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm7, 624(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqu %%xmm0, 640(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 656(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 672(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 688(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqu %%xmm4, 704(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm5, 720(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm6, 736(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm7, 752(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqu %%xmm0, 768(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 784(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 800(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 816(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqu %%xmm4, 832(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm5, 848(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm6, 864(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm7, 880(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqu %%xmm0, 896(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm1, 912(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm2, 928(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm3, 944(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqu %%xmm4, 960(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm5, 976(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm6, 992(%%rbx);"NOP(NOPCOUNT)
                "movdqu %%xmm7, 1008(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movdqu,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movdqu,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movdqu,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movdqu,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movdqu,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movdqu,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movdqu,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movdqu,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movdqu,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movdqu,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movdqu,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movdqu,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movdqu,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movdqu,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movdqu,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movdqu,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movdqu,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movdqu,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movdqu,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movdqu,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movdqu,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movdqu,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movdqu,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movdqu,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movdqu,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movdqu,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movdqu,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movdqu,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movdqu,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movdqu,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movdqu,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movdqu,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movdqu,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movdqu,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movdqu,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movdqu,%%xmm7,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_64(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movdqu_8;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*64);
        break;
      default: ret=0.0;break;
   }  
	
  #ifdef USE_PAPI
    if ((!id)&&(data->num_events))
    { 
      PAPI_read(data->Eventset,data->values);
      for (i=0;i<data->num_events;i++)
      {
         if (burst_length==1) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==2) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==3) data->papi_results[i]=(double)data->values[i]/(double)(passes*66);
         if (burst_length==4) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==8) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
      }
    }
    else for (i=0;i<data->num_events;i++) data->papi_results[i]==(double)0;
  #endif		
  return ret;
}

/** assembler implementation of bandwidth measurement using vmovdqu instruction
 */
static double asm_work_vmovdqu(unsigned long long addr, unsigned long long accesses, unsigned long long burst_length,unsigned long long call_latency,unsigned long long freq,unsigned long long running_threads,unsigned long long id, volatile void * sync_ptr,threaddata_t* data) __attribute__((noinline));
static double asm_work_vmovdqu(unsigned long long addr, unsigned long long accesses, unsigned long long burst_length,unsigned long long call_latency,unsigned long long freq,unsigned long long running_threads,unsigned long long id, volatile void * sync_ptr,threaddata_t* data)
{
   unsigned long long passes;
   double ret;
   unsigned long long a,b,c,d;
   int i;
   
   #ifdef USE_PAPI
    if ((!id) && (data->num_events)) PAPI_reset(data->Eventset);
   #endif

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }

   switch (burst_length)
   {

    case 1:
      passes=accesses/32;
      #if (ACCESS_STRIDE>0)
      passes*=32;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(vmovdqu_1)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_vmovdqu_1;"
                ".align 64,0x0;"
                "_work_loop_vmovdqu_1:"
#if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "vmovdqu %%ymm0, 0(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 32(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqu %%ymm0, 64(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 96(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqu %%ymm0, 128(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 160(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqu %%ymm0, 192(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 224(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqu %%ymm0, 256(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 288(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqu %%ymm0, 320(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 352(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqu %%ymm0, 384(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 416(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqu %%ymm0, 448(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 480(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqu %%ymm0, 512(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 544(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqu %%ymm0, 576(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 608(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqu %%ymm0, 640(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 672(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqu %%ymm0, 704(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 736(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqu %%ymm0, 768(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 800(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqu %%ymm0, 832(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 864(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqu %%ymm0, 896(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 928(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqu %%ymm0, 960(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 992(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_32(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_vmovdqu_1;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*32);
        break;

    case 2:
      passes=accesses/32;
      #if (ACCESS_STRIDE>0)
      passes*=32;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(vmovdqu_2)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_vmovdqu_2;"
                ".align 64,0x0;"
                "_work_loop_vmovdqu_2:"
#if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "vmovdqu %%ymm0, 0(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 32(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqu %%ymm0, 64(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 96(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqu %%ymm0, 128(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 160(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqu %%ymm0, 192(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 224(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqu %%ymm0, 256(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 288(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqu %%ymm0, 320(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 352(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqu %%ymm0, 384(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 416(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqu %%ymm0, 448(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 480(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqu %%ymm0, 512(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 544(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqu %%ymm0, 576(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 608(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqu %%ymm0, 640(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 672(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqu %%ymm0, 704(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 736(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqu %%ymm0, 768(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 800(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqu %%ymm0, 832(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 864(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqu %%ymm0, 896(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 928(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqu %%ymm0, 960(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 992(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_32(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_vmovdqu_2;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*32);
        break;

    case 3:
      passes=accesses/33;
      #if (ACCESS_STRIDE>0)
      passes*=32;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(vmovdqu_3)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_vmovdqu_3;"
                ".align 64,0x0;"
                "_work_loop_vmovdqu_3:"
#if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "vmovdqu %%ymm0, 0(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 32(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqu %%ymm2, 64(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 96(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqu %%ymm1, 128(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm2, 160(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqu %%ymm0, 192(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 224(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqu %%ymm2, 256(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 288(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqu %%ymm1, 320(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm2, 352(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqu %%ymm0, 384(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 416(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqu %%ymm2, 448(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 480(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqu %%ymm1, 512(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm2, 544(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqu %%ymm0, 576(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 608(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqu %%ymm2, 640(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 672(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqu %%ymm1, 704(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm2, 736(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqu %%ymm0, 768(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 800(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqu %%ymm2, 832(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm0, 864(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqu %%ymm1, 896(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm2, 928(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqu %%ymm0, 960(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 992(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,rbx)
                "vmovdqu %%ymm2, 1024(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                "add $1056,%%rbx;"
		#else
		INC_33(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_vmovdqu_3;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*33);
        break;

    case 4:
      passes=accesses/32;
      #if (ACCESS_STRIDE>0)
      passes*=32;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(vmovdqu_4)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_vmovdqu_4;"
                ".align 64,0x0;"
                "_work_loop_vmovdqu_4:"
#if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "vmovdqu %%ymm0, 0(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 32(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqu %%ymm2, 64(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm3, 96(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqu %%ymm0, 128(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 160(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqu %%ymm2, 192(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm3, 224(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqu %%ymm0, 256(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 288(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqu %%ymm2, 320(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm3, 352(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqu %%ymm0, 384(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 416(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqu %%ymm2, 448(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm3, 480(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqu %%ymm0, 512(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 544(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqu %%ymm2, 576(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm3, 608(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqu %%ymm0, 640(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 672(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqu %%ymm2, 704(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm3, 736(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqu %%ymm0, 768(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 800(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqu %%ymm2, 832(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm3, 864(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqu %%ymm0, 896(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 928(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqu %%ymm2, 960(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm3, 992(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(vmovdqu,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(vmovdqu,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(vmovdqu,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(vmovdqu,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(vmovdqu,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(vmovdqu,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(vmovdqu,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(vmovdqu,%%ymm3,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_32(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_vmovdqu_4;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*32);
        break;

    case 8:
      passes=accesses/32;
      #if (ACCESS_STRIDE>0)
      passes*=32;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(vmovdqu_8)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_vmovdqu_8;"
                ".align 64,0x0;"
                "_work_loop_vmovdqu_8:"
#if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "vmovdqu %%ymm0, 0(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 32(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqu %%ymm2, 64(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm3, 96(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqu %%ymm4, 128(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm5, 160(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqu %%ymm6, 192(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm7, 224(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqu %%ymm0, 256(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 288(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqu %%ymm2, 320(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm3, 352(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqu %%ymm4, 384(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm5, 416(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqu %%ymm6, 448(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm7, 480(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqu %%ymm0, 512(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 544(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqu %%ymm2, 576(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm3, 608(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqu %%ymm4, 640(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm5, 672(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqu %%ymm6, 704(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm7, 736(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqu %%ymm0, 768(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm1, 800(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqu %%ymm2, 832(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm3, 864(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqu %%ymm4, 896(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm5, 928(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqu %%ymm6, 960(%%rbx);"NOP(NOPCOUNT)
                "vmovdqu %%ymm7, 992(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(vmovdqu,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(vmovdqu,%%ymm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(vmovdqu,%%ymm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(vmovdqu,%%ymm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(vmovdqu,%%ymm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(vmovdqu,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(vmovdqu,%%ymm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(vmovdqu,%%ymm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(vmovdqu,%%ymm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(vmovdqu,%%ymm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(vmovdqu,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(vmovdqu,%%ymm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(vmovdqu,%%ymm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(vmovdqu,%%ymm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(vmovdqu,%%ymm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(vmovdqu,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(vmovdqu,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(vmovdqu,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(vmovdqu,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(vmovdqu,%%ymm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(vmovdqu,%%ymm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(vmovdqu,%%ymm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(vmovdqu,%%ymm7,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_32(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_vmovdqu_8;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*32);
        break;
      default: ret=0.0;break;
   }  
	
  #ifdef USE_PAPI
    if ((!id)&&(data->num_events))
    { 
      PAPI_read(data->Eventset,data->values);
      for (i=0;i<data->num_events;i++)
      {
         if (burst_length==1) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==2) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==3) data->papi_results[i]=(double)data->values[i]/(double)(passes*66);
         if (burst_length==4) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==8) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
      }
    }
    else for (i=0;i<data->num_events;i++) data->papi_results[i]==(double)0;
  #endif		
  return ret;
}

/** assembler implementation of bandwidth measurement using mov instruction
 */
static double asm_work_mov(unsigned long long addr, unsigned long long accesses, unsigned long long burst_length,unsigned long long call_latency,unsigned long long freq,unsigned long long running_threads,unsigned long long id, volatile void * sync_ptr,threaddata_t* data) __attribute__((noinline));
static double asm_work_mov(unsigned long long addr, unsigned long long accesses, unsigned long long burst_length,unsigned long long call_latency,unsigned long long freq,unsigned long long running_threads,unsigned long long id, volatile void * sync_ptr,threaddata_t* data)
{
   unsigned long long passes;
   double ret;
   unsigned long long a,b,c,d;
   int i;
   
   #ifdef USE_PAPI
    if ((!id) && (data->num_events)) PAPI_reset(data->Eventset);
   #endif


   switch (burst_length)
   {

    case 1:
      passes=accesses/128;
      #if (ACCESS_STRIDE>0)
      passes*=8;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(mov_1)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_mov_1;"
                ".align 64,0x0;"
                "_work_loop_mov_1:"
#if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "mov %%r8, 0(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 8(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 16(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 24(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 32(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 40(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 48(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 56(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "mov %%r8, 64(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 72(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 80(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 88(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 96(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 104(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 112(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 120(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "mov %%r8, 128(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 136(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 144(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 152(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 160(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 168(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 176(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 184(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "mov %%r8, 192(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 200(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 208(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 216(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 224(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 232(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 240(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 248(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "mov %%r8, 256(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 264(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 272(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 280(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 288(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 296(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 304(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 312(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "mov %%r8, 320(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 328(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 336(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 344(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 352(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 360(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 368(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 376(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "mov %%r8, 384(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 392(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 400(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 408(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 416(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 424(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 432(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 440(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "mov %%r8, 448(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 456(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 464(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 472(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 480(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 488(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 496(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 504(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "mov %%r8, 512(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 520(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 528(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 536(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 544(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 552(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 560(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 568(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "mov %%r8, 576(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 584(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 592(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 600(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 608(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 616(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 624(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 632(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "mov %%r8, 640(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 648(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 656(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 664(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 672(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 680(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 688(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 696(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "mov %%r8, 704(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 712(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 720(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 728(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 736(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 744(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 752(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 760(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "mov %%r8, 768(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 776(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 784(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 792(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 800(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 808(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 816(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 824(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "mov %%r8, 832(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 840(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 848(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 856(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 864(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 872(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 880(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 888(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "mov %%r8, 896(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 904(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 912(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 920(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 928(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 936(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 944(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 952(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "mov %%r8, 960(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 968(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 976(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 984(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 992(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 1000(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 1008(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 1016(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_64(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_65(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_66(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_67(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_68(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_69(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_70(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_71(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_72(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_73(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_74(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_75(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_76(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_77(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_78(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_79(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_80(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_81(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_82(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_83(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_84(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_85(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_86(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_87(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_88(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_89(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_90(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_91(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_92(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_93(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_94(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_95(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_96(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_97(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_98(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_99(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_100(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_101(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_102(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_103(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_104(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_105(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_106(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_107(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_108(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_109(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_110(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_111(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_112(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_113(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_114(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_115(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_116(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_117(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_118(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_119(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_120(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_121(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_122(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_123(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_124(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_125(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_126(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_127(mov,%%r8,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_128(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_mov_1;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*128);
        break;

    case 2:
      passes=accesses/128;
      #if (ACCESS_STRIDE>0)
      passes*=8;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(mov_2)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_mov_2;"
                ".align 64,0x0;"
                "_work_loop_mov_2:"
#if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "mov %%r8, 0(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 8(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 16(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 24(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 32(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 40(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 48(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 56(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "mov %%r8, 64(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 72(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 80(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 88(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 96(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 104(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 112(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 120(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "mov %%r8, 128(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 136(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 144(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 152(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 160(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 168(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 176(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 184(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "mov %%r8, 192(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 200(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 208(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 216(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 224(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 232(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 240(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 248(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "mov %%r8, 256(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 264(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 272(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 280(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 288(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 296(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 304(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 312(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "mov %%r8, 320(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 328(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 336(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 344(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 352(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 360(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 368(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 376(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "mov %%r8, 384(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 392(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 400(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 408(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 416(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 424(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 432(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 440(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "mov %%r8, 448(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 456(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 464(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 472(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 480(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 488(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 496(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 504(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "mov %%r8, 512(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 520(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 528(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 536(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 544(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 552(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 560(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 568(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "mov %%r8, 576(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 584(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 592(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 600(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 608(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 616(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 624(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 632(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "mov %%r8, 640(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 648(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 656(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 664(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 672(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 680(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 688(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 696(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "mov %%r8, 704(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 712(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 720(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 728(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 736(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 744(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 752(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 760(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "mov %%r8, 768(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 776(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 784(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 792(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 800(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 808(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 816(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 824(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "mov %%r8, 832(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 840(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 848(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 856(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 864(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 872(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 880(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 888(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "mov %%r8, 896(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 904(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 912(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 920(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 928(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 936(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 944(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 952(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "mov %%r8, 960(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 968(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 976(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 984(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 992(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 1000(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 1008(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 1016(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_64(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_65(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_66(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_67(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_68(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_69(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_70(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_71(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_72(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_73(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_74(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_75(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_76(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_77(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_78(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_79(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_80(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_81(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_82(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_83(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_84(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_85(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_86(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_87(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_88(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_89(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_90(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_91(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_92(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_93(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_94(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_95(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_96(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_97(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_98(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_99(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_100(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_101(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_102(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_103(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_104(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_105(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_106(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_107(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_108(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_109(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_110(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_111(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_112(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_113(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_114(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_115(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_116(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_117(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_118(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_119(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_120(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_121(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_122(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_123(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_124(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_125(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_126(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_127(mov,%%r9,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_128(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_mov_2;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*128);
        break;

    case 3:
      passes=accesses/132;
      #if (ACCESS_STRIDE>0)
      passes*=8;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(mov_3)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_mov_3;"
                ".align 64,0x0;"
                "_work_loop_mov_3:"
#if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "mov %%r8, 0(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 8(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 16(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 24(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 32(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 40(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 48(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 56(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "mov %%r10, 64(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 72(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 80(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 88(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 96(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 104(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 112(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 120(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "mov %%r9, 128(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 136(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 144(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 152(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 160(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 168(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 176(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 184(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "mov %%r8, 192(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 200(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 208(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 216(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 224(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 232(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 240(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 248(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "mov %%r10, 256(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 264(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 272(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 280(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 288(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 296(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 304(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 312(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "mov %%r9, 320(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 328(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 336(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 344(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 352(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 360(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 368(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 376(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "mov %%r8, 384(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 392(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 400(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 408(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 416(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 424(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 432(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 440(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "mov %%r10, 448(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 456(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 464(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 472(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 480(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 488(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 496(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 504(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "mov %%r9, 512(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 520(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 528(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 536(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 544(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 552(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 560(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 568(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "mov %%r8, 576(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 584(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 592(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 600(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 608(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 616(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 624(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 632(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "mov %%r10, 640(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 648(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 656(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 664(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 672(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 680(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 688(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 696(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "mov %%r9, 704(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 712(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 720(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 728(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 736(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 744(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 752(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 760(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "mov %%r8, 768(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 776(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 784(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 792(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 800(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 808(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 816(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 824(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "mov %%r10, 832(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 840(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 848(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 856(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 864(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 872(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 880(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 888(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "mov %%r9, 896(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 904(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 912(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 920(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 928(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 936(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 944(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 952(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "mov %%r8, 960(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 968(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 976(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 984(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 992(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 1000(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 1008(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 1016(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,rbx)
                "mov %%r10, 1024(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 1032(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 1040(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 1048(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_64(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_65(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_66(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_67(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_68(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_69(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_70(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_71(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_72(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_73(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_74(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_75(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_76(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_77(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_78(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_79(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_80(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_81(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_82(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_83(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_84(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_85(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_86(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_87(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_88(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_89(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_90(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_91(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_92(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_93(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_94(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_95(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_96(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_97(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_98(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_99(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_100(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_101(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_102(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_103(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_104(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_105(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_106(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_107(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_108(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_109(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_110(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_111(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_112(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_113(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_114(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_115(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_116(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_117(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_118(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_119(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_120(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_121(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_122(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_123(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_124(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_125(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_126(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_127(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_128(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_129(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_130(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_131(mov,%%r10,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                "add $1056,%%rbx;"
		#else
		INC_132(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_mov_3;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*132);
        break;

    case 4:
      passes=accesses/128;
      #if (ACCESS_STRIDE>0)
      passes*=8;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(mov_4)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_mov_4;"
                ".align 64,0x0;"
                "_work_loop_mov_4:"
#if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "mov %%r8, 0(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 8(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 16(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 24(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 32(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 40(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 48(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 56(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "mov %%r8, 64(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 72(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 80(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 88(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 96(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 104(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 112(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 120(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "mov %%r8, 128(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 136(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 144(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 152(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 160(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 168(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 176(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 184(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "mov %%r8, 192(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 200(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 208(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 216(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 224(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 232(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 240(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 248(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "mov %%r8, 256(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 264(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 272(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 280(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 288(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 296(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 304(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 312(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "mov %%r8, 320(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 328(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 336(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 344(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 352(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 360(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 368(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 376(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "mov %%r8, 384(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 392(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 400(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 408(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 416(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 424(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 432(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 440(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "mov %%r8, 448(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 456(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 464(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 472(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 480(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 488(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 496(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 504(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "mov %%r8, 512(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 520(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 528(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 536(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 544(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 552(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 560(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 568(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "mov %%r8, 576(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 584(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 592(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 600(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 608(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 616(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 624(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 632(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "mov %%r8, 640(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 648(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 656(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 664(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 672(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 680(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 688(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 696(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "mov %%r8, 704(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 712(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 720(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 728(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 736(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 744(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 752(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 760(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "mov %%r8, 768(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 776(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 784(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 792(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 800(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 808(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 816(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 824(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "mov %%r8, 832(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 840(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 848(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 856(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 864(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 872(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 880(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 888(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "mov %%r8, 896(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 904(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 912(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 920(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 928(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 936(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 944(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 952(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "mov %%r8, 960(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 968(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 976(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 984(%%rbx);"NOP(NOPCOUNT)
                "mov %%r8, 992(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 1000(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 1008(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 1016(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_64(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_65(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_66(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_67(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_68(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_69(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_70(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_71(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_72(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_73(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_74(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_75(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_76(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_77(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_78(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_79(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_80(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_81(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_82(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_83(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_84(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_85(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_86(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_87(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_88(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_89(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_90(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_91(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_92(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_93(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_94(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_95(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_96(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_97(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_98(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_99(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_100(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_101(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_102(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_103(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_104(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_105(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_106(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_107(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_108(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_109(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_110(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_111(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_112(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_113(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_114(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_115(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_116(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_117(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_118(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_119(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_120(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_121(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_122(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_123(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_124(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_125(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_126(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_127(mov,%%r11,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_128(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_mov_4;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*128);
        break;

    case 8:
      passes=accesses/128;
      #if (ACCESS_STRIDE>0)
      passes*=8;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(mov_8)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_mov_8;"
                ".align 64,0x0;"
                "_work_loop_mov_8:"
#if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "mov %%r8, 0(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 8(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 16(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 24(%%rbx);"NOP(NOPCOUNT)
                "mov %%r12, 32(%%rbx);"NOP(NOPCOUNT)
                "mov %%r13, 40(%%rbx);"NOP(NOPCOUNT)
                "mov %%r14, 48(%%rbx);"NOP(NOPCOUNT)
                "mov %%r15, 56(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "mov %%r8, 64(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 72(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 80(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 88(%%rbx);"NOP(NOPCOUNT)
                "mov %%r12, 96(%%rbx);"NOP(NOPCOUNT)
                "mov %%r13, 104(%%rbx);"NOP(NOPCOUNT)
                "mov %%r14, 112(%%rbx);"NOP(NOPCOUNT)
                "mov %%r15, 120(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "mov %%r8, 128(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 136(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 144(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 152(%%rbx);"NOP(NOPCOUNT)
                "mov %%r12, 160(%%rbx);"NOP(NOPCOUNT)
                "mov %%r13, 168(%%rbx);"NOP(NOPCOUNT)
                "mov %%r14, 176(%%rbx);"NOP(NOPCOUNT)
                "mov %%r15, 184(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "mov %%r8, 192(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 200(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 208(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 216(%%rbx);"NOP(NOPCOUNT)
                "mov %%r12, 224(%%rbx);"NOP(NOPCOUNT)
                "mov %%r13, 232(%%rbx);"NOP(NOPCOUNT)
                "mov %%r14, 240(%%rbx);"NOP(NOPCOUNT)
                "mov %%r15, 248(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "mov %%r8, 256(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 264(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 272(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 280(%%rbx);"NOP(NOPCOUNT)
                "mov %%r12, 288(%%rbx);"NOP(NOPCOUNT)
                "mov %%r13, 296(%%rbx);"NOP(NOPCOUNT)
                "mov %%r14, 304(%%rbx);"NOP(NOPCOUNT)
                "mov %%r15, 312(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "mov %%r8, 320(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 328(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 336(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 344(%%rbx);"NOP(NOPCOUNT)
                "mov %%r12, 352(%%rbx);"NOP(NOPCOUNT)
                "mov %%r13, 360(%%rbx);"NOP(NOPCOUNT)
                "mov %%r14, 368(%%rbx);"NOP(NOPCOUNT)
                "mov %%r15, 376(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "mov %%r8, 384(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 392(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 400(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 408(%%rbx);"NOP(NOPCOUNT)
                "mov %%r12, 416(%%rbx);"NOP(NOPCOUNT)
                "mov %%r13, 424(%%rbx);"NOP(NOPCOUNT)
                "mov %%r14, 432(%%rbx);"NOP(NOPCOUNT)
                "mov %%r15, 440(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "mov %%r8, 448(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 456(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 464(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 472(%%rbx);"NOP(NOPCOUNT)
                "mov %%r12, 480(%%rbx);"NOP(NOPCOUNT)
                "mov %%r13, 488(%%rbx);"NOP(NOPCOUNT)
                "mov %%r14, 496(%%rbx);"NOP(NOPCOUNT)
                "mov %%r15, 504(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "mov %%r8, 512(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 520(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 528(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 536(%%rbx);"NOP(NOPCOUNT)
                "mov %%r12, 544(%%rbx);"NOP(NOPCOUNT)
                "mov %%r13, 552(%%rbx);"NOP(NOPCOUNT)
                "mov %%r14, 560(%%rbx);"NOP(NOPCOUNT)
                "mov %%r15, 568(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "mov %%r8, 576(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 584(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 592(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 600(%%rbx);"NOP(NOPCOUNT)
                "mov %%r12, 608(%%rbx);"NOP(NOPCOUNT)
                "mov %%r13, 616(%%rbx);"NOP(NOPCOUNT)
                "mov %%r14, 624(%%rbx);"NOP(NOPCOUNT)
                "mov %%r15, 632(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "mov %%r8, 640(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 648(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 656(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 664(%%rbx);"NOP(NOPCOUNT)
                "mov %%r12, 672(%%rbx);"NOP(NOPCOUNT)
                "mov %%r13, 680(%%rbx);"NOP(NOPCOUNT)
                "mov %%r14, 688(%%rbx);"NOP(NOPCOUNT)
                "mov %%r15, 696(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "mov %%r8, 704(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 712(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 720(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 728(%%rbx);"NOP(NOPCOUNT)
                "mov %%r12, 736(%%rbx);"NOP(NOPCOUNT)
                "mov %%r13, 744(%%rbx);"NOP(NOPCOUNT)
                "mov %%r14, 752(%%rbx);"NOP(NOPCOUNT)
                "mov %%r15, 760(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "mov %%r8, 768(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 776(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 784(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 792(%%rbx);"NOP(NOPCOUNT)
                "mov %%r12, 800(%%rbx);"NOP(NOPCOUNT)
                "mov %%r13, 808(%%rbx);"NOP(NOPCOUNT)
                "mov %%r14, 816(%%rbx);"NOP(NOPCOUNT)
                "mov %%r15, 824(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "mov %%r8, 832(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 840(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 848(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 856(%%rbx);"NOP(NOPCOUNT)
                "mov %%r12, 864(%%rbx);"NOP(NOPCOUNT)
                "mov %%r13, 872(%%rbx);"NOP(NOPCOUNT)
                "mov %%r14, 880(%%rbx);"NOP(NOPCOUNT)
                "mov %%r15, 888(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "mov %%r8, 896(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 904(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 912(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 920(%%rbx);"NOP(NOPCOUNT)
                "mov %%r12, 928(%%rbx);"NOP(NOPCOUNT)
                "mov %%r13, 936(%%rbx);"NOP(NOPCOUNT)
                "mov %%r14, 944(%%rbx);"NOP(NOPCOUNT)
                "mov %%r15, 952(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "mov %%r8, 960(%%rbx);"NOP(NOPCOUNT)
                "mov %%r9, 968(%%rbx);"NOP(NOPCOUNT)
                "mov %%r10, 976(%%rbx);"NOP(NOPCOUNT)
                "mov %%r11, 984(%%rbx);"NOP(NOPCOUNT)
                "mov %%r12, 992(%%rbx);"NOP(NOPCOUNT)
                "mov %%r13, 1000(%%rbx);"NOP(NOPCOUNT)
                "mov %%r14, 1008(%%rbx);"NOP(NOPCOUNT)
                "mov %%r15, 1016(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(mov,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(mov,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(mov,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(mov,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(mov,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(mov,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(mov,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(mov,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(mov,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(mov,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(mov,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(mov,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(mov,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(mov,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(mov,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(mov,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(mov,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(mov,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(mov,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(mov,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(mov,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(mov,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(mov,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(mov,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(mov,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(mov,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(mov,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(mov,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(mov,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(mov,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(mov,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(mov,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_64(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_65(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_66(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_67(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_68(mov,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_69(mov,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_70(mov,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_71(mov,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_72(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_73(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_74(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_75(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_76(mov,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_77(mov,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_78(mov,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_79(mov,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_80(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_81(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_82(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_83(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_84(mov,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_85(mov,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_86(mov,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_87(mov,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_88(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_89(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_90(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_91(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_92(mov,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_93(mov,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_94(mov,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_95(mov,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_96(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_97(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_98(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_99(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_100(mov,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_101(mov,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_102(mov,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_103(mov,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_104(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_105(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_106(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_107(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_108(mov,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_109(mov,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_110(mov,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_111(mov,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_112(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_113(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_114(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_115(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_116(mov,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_117(mov,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_118(mov,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_119(mov,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_120(mov,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_121(mov,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_122(mov,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_123(mov,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_124(mov,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_125(mov,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_126(mov,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_127(mov,%%r15,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_128(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_mov_8;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*128);
        break;
      default: ret=0.0;break;
   }  
	
  #ifdef USE_PAPI
    if ((!id)&&(data->num_events))
    { 
      PAPI_read(data->Eventset,data->values);
      for (i=0;i<data->num_events;i++)
      {
         if (burst_length==1) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==2) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==3) data->papi_results[i]=(double)data->values[i]/(double)(passes*66);
         if (burst_length==4) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==8) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
      }
    }
    else for (i=0;i<data->num_events;i++) data->papi_results[i]==(double)0;
  #endif		
  return ret;
}

/** assembler implementation of bandwidth measurement using movnti instruction
 */
static double asm_work_movnti(unsigned long long addr, unsigned long long accesses, unsigned long long burst_length,unsigned long long call_latency,unsigned long long freq,unsigned long long running_threads,unsigned long long id, volatile void * sync_ptr,threaddata_t* data) __attribute__((noinline));
static double asm_work_movnti(unsigned long long addr, unsigned long long accesses, unsigned long long burst_length,unsigned long long call_latency,unsigned long long freq,unsigned long long running_threads,unsigned long long id, volatile void * sync_ptr,threaddata_t* data)
{
   unsigned long long passes;
   double ret;
   unsigned long long a,b,c,d;
   int i;
   
   #ifdef USE_PAPI
    if ((!id) && (data->num_events)) PAPI_reset(data->Eventset);
   #endif


   switch (burst_length)
   {

    case 1:
      passes=accesses/128;
      #if (ACCESS_STRIDE>0)
      passes*=8;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movnti_1)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movnti_1;"
                ".align 64,0x0;"
                "_work_loop_movnti_1:"
#if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movnti %%r8, 0(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 8(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 16(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 24(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 32(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 40(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 48(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 56(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movnti %%r8, 64(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 72(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 80(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 88(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 96(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 104(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 112(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 120(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movnti %%r8, 128(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 136(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 144(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 152(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 160(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 168(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 176(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 184(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movnti %%r8, 192(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 200(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 208(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 216(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 224(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 232(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 240(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 248(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movnti %%r8, 256(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 264(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 272(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 280(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 288(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 296(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 304(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 312(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movnti %%r8, 320(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 328(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 336(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 344(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 352(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 360(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 368(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 376(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movnti %%r8, 384(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 392(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 400(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 408(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 416(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 424(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 432(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 440(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movnti %%r8, 448(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 456(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 464(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 472(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 480(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 488(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 496(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 504(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movnti %%r8, 512(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 520(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 528(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 536(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 544(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 552(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 560(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 568(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movnti %%r8, 576(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 584(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 592(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 600(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 608(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 616(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 624(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 632(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movnti %%r8, 640(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 648(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 656(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 664(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 672(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 680(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 688(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 696(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movnti %%r8, 704(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 712(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 720(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 728(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 736(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 744(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 752(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 760(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movnti %%r8, 768(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 776(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 784(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 792(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 800(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 808(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 816(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 824(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movnti %%r8, 832(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 840(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 848(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 856(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 864(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 872(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 880(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 888(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movnti %%r8, 896(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 904(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 912(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 920(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 928(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 936(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 944(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 952(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movnti %%r8, 960(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 968(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 976(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 984(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 992(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 1000(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 1008(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 1016(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_64(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_65(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_66(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_67(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_68(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_69(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_70(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_71(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_72(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_73(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_74(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_75(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_76(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_77(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_78(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_79(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_80(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_81(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_82(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_83(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_84(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_85(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_86(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_87(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_88(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_89(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_90(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_91(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_92(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_93(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_94(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_95(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_96(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_97(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_98(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_99(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_100(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_101(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_102(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_103(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_104(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_105(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_106(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_107(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_108(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_109(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_110(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_111(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_112(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_113(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_114(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_115(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_116(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_117(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_118(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_119(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_120(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_121(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_122(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_123(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_124(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_125(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_126(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_127(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_128(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movnti_1;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*128);
        break;

    case 2:
      passes=accesses/128;
      #if (ACCESS_STRIDE>0)
      passes*=8;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movnti_2)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movnti_2;"
                ".align 64,0x0;"
                "_work_loop_movnti_2:"
#if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movnti %%r8, 0(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 8(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 16(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 24(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 32(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 40(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 48(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 56(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movnti %%r8, 64(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 72(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 80(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 88(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 96(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 104(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 112(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 120(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movnti %%r8, 128(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 136(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 144(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 152(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 160(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 168(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 176(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 184(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movnti %%r8, 192(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 200(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 208(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 216(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 224(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 232(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 240(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 248(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movnti %%r8, 256(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 264(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 272(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 280(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 288(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 296(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 304(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 312(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movnti %%r8, 320(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 328(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 336(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 344(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 352(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 360(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 368(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 376(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movnti %%r8, 384(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 392(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 400(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 408(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 416(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 424(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 432(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 440(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movnti %%r8, 448(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 456(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 464(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 472(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 480(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 488(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 496(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 504(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movnti %%r8, 512(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 520(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 528(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 536(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 544(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 552(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 560(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 568(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movnti %%r8, 576(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 584(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 592(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 600(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 608(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 616(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 624(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 632(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movnti %%r8, 640(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 648(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 656(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 664(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 672(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 680(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 688(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 696(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movnti %%r8, 704(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 712(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 720(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 728(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 736(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 744(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 752(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 760(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movnti %%r8, 768(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 776(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 784(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 792(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 800(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 808(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 816(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 824(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movnti %%r8, 832(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 840(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 848(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 856(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 864(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 872(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 880(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 888(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movnti %%r8, 896(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 904(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 912(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 920(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 928(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 936(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 944(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 952(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movnti %%r8, 960(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 968(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 976(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 984(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 992(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 1000(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 1008(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 1016(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_64(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_65(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_66(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_67(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_68(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_69(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_70(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_71(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_72(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_73(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_74(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_75(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_76(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_77(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_78(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_79(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_80(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_81(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_82(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_83(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_84(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_85(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_86(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_87(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_88(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_89(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_90(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_91(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_92(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_93(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_94(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_95(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_96(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_97(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_98(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_99(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_100(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_101(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_102(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_103(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_104(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_105(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_106(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_107(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_108(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_109(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_110(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_111(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_112(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_113(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_114(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_115(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_116(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_117(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_118(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_119(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_120(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_121(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_122(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_123(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_124(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_125(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_126(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_127(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_128(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movnti_2;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*128);
        break;

    case 3:
      passes=accesses/132;
      #if (ACCESS_STRIDE>0)
      passes*=8;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movnti_3)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movnti_3;"
                ".align 64,0x0;"
                "_work_loop_movnti_3:"
#if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movnti %%r8, 0(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 8(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 16(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 24(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 32(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 40(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 48(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 56(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movnti %%r10, 64(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 72(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 80(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 88(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 96(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 104(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 112(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 120(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movnti %%r9, 128(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 136(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 144(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 152(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 160(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 168(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 176(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 184(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movnti %%r8, 192(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 200(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 208(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 216(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 224(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 232(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 240(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 248(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movnti %%r10, 256(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 264(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 272(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 280(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 288(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 296(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 304(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 312(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movnti %%r9, 320(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 328(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 336(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 344(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 352(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 360(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 368(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 376(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movnti %%r8, 384(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 392(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 400(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 408(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 416(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 424(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 432(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 440(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movnti %%r10, 448(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 456(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 464(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 472(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 480(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 488(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 496(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 504(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movnti %%r9, 512(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 520(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 528(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 536(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 544(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 552(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 560(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 568(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movnti %%r8, 576(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 584(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 592(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 600(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 608(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 616(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 624(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 632(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movnti %%r10, 640(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 648(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 656(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 664(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 672(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 680(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 688(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 696(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movnti %%r9, 704(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 712(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 720(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 728(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 736(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 744(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 752(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 760(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movnti %%r8, 768(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 776(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 784(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 792(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 800(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 808(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 816(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 824(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movnti %%r10, 832(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 840(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 848(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 856(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 864(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 872(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 880(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 888(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movnti %%r9, 896(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 904(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 912(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 920(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 928(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 936(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 944(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 952(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movnti %%r8, 960(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 968(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 976(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 984(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 992(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 1000(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 1008(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 1016(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,rbx)
                "movnti %%r10, 1024(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 1032(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 1040(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 1048(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_64(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_65(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_66(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_67(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_68(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_69(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_70(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_71(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_72(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_73(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_74(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_75(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_76(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_77(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_78(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_79(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_80(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_81(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_82(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_83(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_84(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_85(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_86(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_87(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_88(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_89(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_90(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_91(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_92(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_93(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_94(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_95(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_96(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_97(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_98(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_99(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_100(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_101(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_102(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_103(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_104(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_105(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_106(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_107(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_108(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_109(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_110(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_111(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_112(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_113(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_114(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_115(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_116(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_117(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_118(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_119(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_120(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_121(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_122(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_123(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_124(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_125(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_126(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_127(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_128(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_129(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_130(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_131(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                "add $1056,%%rbx;"
		#else
		INC_132(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movnti_3;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*132);
        break;

    case 4:
      passes=accesses/128;
      #if (ACCESS_STRIDE>0)
      passes*=8;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movnti_4)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movnti_4;"
                ".align 64,0x0;"
                "_work_loop_movnti_4:"
#if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movnti %%r8, 0(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 8(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 16(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 24(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 32(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 40(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 48(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 56(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movnti %%r8, 64(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 72(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 80(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 88(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 96(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 104(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 112(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 120(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movnti %%r8, 128(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 136(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 144(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 152(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 160(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 168(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 176(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 184(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movnti %%r8, 192(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 200(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 208(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 216(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 224(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 232(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 240(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 248(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movnti %%r8, 256(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 264(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 272(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 280(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 288(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 296(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 304(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 312(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movnti %%r8, 320(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 328(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 336(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 344(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 352(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 360(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 368(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 376(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movnti %%r8, 384(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 392(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 400(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 408(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 416(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 424(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 432(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 440(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movnti %%r8, 448(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 456(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 464(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 472(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 480(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 488(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 496(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 504(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movnti %%r8, 512(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 520(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 528(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 536(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 544(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 552(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 560(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 568(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movnti %%r8, 576(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 584(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 592(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 600(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 608(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 616(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 624(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 632(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movnti %%r8, 640(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 648(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 656(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 664(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 672(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 680(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 688(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 696(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movnti %%r8, 704(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 712(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 720(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 728(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 736(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 744(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 752(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 760(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movnti %%r8, 768(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 776(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 784(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 792(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 800(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 808(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 816(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 824(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movnti %%r8, 832(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 840(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 848(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 856(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 864(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 872(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 880(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 888(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movnti %%r8, 896(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 904(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 912(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 920(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 928(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 936(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 944(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 952(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movnti %%r8, 960(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 968(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 976(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 984(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r8, 992(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 1000(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 1008(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 1016(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_64(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_65(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_66(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_67(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_68(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_69(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_70(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_71(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_72(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_73(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_74(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_75(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_76(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_77(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_78(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_79(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_80(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_81(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_82(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_83(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_84(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_85(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_86(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_87(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_88(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_89(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_90(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_91(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_92(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_93(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_94(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_95(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_96(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_97(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_98(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_99(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_100(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_101(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_102(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_103(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_104(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_105(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_106(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_107(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_108(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_109(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_110(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_111(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_112(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_113(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_114(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_115(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_116(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_117(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_118(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_119(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_120(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_121(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_122(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_123(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_124(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_125(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_126(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_127(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_128(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movnti_4;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*128);
        break;

    case 8:
      passes=accesses/128;
      #if (ACCESS_STRIDE>0)
      passes*=8;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movnti_8)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movnti_8;"
                ".align 64,0x0;"
                "_work_loop_movnti_8:"
#if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movnti %%r8, 0(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 8(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 16(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 24(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r12, 32(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r13, 40(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r14, 48(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r15, 56(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movnti %%r8, 64(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 72(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 80(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 88(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r12, 96(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r13, 104(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r14, 112(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r15, 120(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movnti %%r8, 128(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 136(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 144(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 152(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r12, 160(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r13, 168(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r14, 176(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r15, 184(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movnti %%r8, 192(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 200(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 208(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 216(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r12, 224(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r13, 232(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r14, 240(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r15, 248(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movnti %%r8, 256(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 264(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 272(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 280(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r12, 288(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r13, 296(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r14, 304(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r15, 312(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movnti %%r8, 320(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 328(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 336(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 344(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r12, 352(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r13, 360(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r14, 368(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r15, 376(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movnti %%r8, 384(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 392(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 400(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 408(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r12, 416(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r13, 424(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r14, 432(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r15, 440(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movnti %%r8, 448(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 456(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 464(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 472(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r12, 480(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r13, 488(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r14, 496(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r15, 504(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movnti %%r8, 512(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 520(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 528(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 536(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r12, 544(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r13, 552(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r14, 560(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r15, 568(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movnti %%r8, 576(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 584(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 592(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 600(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r12, 608(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r13, 616(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r14, 624(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r15, 632(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movnti %%r8, 640(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 648(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 656(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 664(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r12, 672(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r13, 680(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r14, 688(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r15, 696(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movnti %%r8, 704(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 712(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 720(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 728(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r12, 736(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r13, 744(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r14, 752(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r15, 760(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movnti %%r8, 768(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 776(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 784(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 792(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r12, 800(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r13, 808(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r14, 816(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r15, 824(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movnti %%r8, 832(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 840(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 848(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 856(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r12, 864(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r13, 872(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r14, 880(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r15, 888(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movnti %%r8, 896(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 904(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 912(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 920(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r12, 928(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r13, 936(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r14, 944(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r15, 952(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movnti %%r8, 960(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r9, 968(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r10, 976(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r11, 984(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r12, 992(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r13, 1000(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r14, 1008(%%rbx);"NOP(NOPCOUNT)
                "movnti %%r15, 1016(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movnti,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movnti,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movnti,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movnti,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movnti,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movnti,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movnti,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movnti,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movnti,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movnti,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movnti,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movnti,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movnti,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movnti,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movnti,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movnti,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movnti,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movnti,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movnti,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movnti,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movnti,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movnti,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movnti,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movnti,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movnti,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movnti,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movnti,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movnti,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movnti,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movnti,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movnti,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movnti,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_64(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_65(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_66(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_67(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_68(movnti,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_69(movnti,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_70(movnti,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_71(movnti,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_72(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_73(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_74(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_75(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_76(movnti,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_77(movnti,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_78(movnti,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_79(movnti,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_80(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_81(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_82(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_83(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_84(movnti,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_85(movnti,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_86(movnti,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_87(movnti,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_88(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_89(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_90(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_91(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_92(movnti,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_93(movnti,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_94(movnti,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_95(movnti,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_96(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_97(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_98(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_99(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_100(movnti,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_101(movnti,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_102(movnti,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_103(movnti,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_104(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_105(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_106(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_107(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_108(movnti,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_109(movnti,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_110(movnti,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_111(movnti,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_112(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_113(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_114(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_115(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_116(movnti,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_117(movnti,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_118(movnti,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_119(movnti,%%r15,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_120(movnti,%%r8,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_121(movnti,%%r9,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_122(movnti,%%r10,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_123(movnti,%%r11,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_124(movnti,%%r12,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_125(movnti,%%r13,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_126(movnti,%%r14,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_127(movnti,%%r15,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==8) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_128(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movnti_8;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*128);
        break;
      default: ret=0.0;break;
   }  
	
  #ifdef USE_PAPI
    if ((!id)&&(data->num_events))
    { 
      PAPI_read(data->Eventset,data->values);
      for (i=0;i<data->num_events;i++)
      {
         if (burst_length==1) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==2) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==3) data->papi_results[i]=(double)data->values[i]/(double)(passes*66);
         if (burst_length==4) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==8) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
      }
    }
    else for (i=0;i<data->num_events;i++) data->papi_results[i]==(double)0;
  #endif		
  return ret;
}

/** assembler implementation of bandwidth measurement using movntdq instruction
 */
static double asm_work_movntdq(unsigned long long addr, unsigned long long accesses, unsigned long long burst_length,unsigned long long call_latency,unsigned long long freq,unsigned long long running_threads,unsigned long long id, volatile void * sync_ptr,threaddata_t* data) __attribute__((noinline));
static double asm_work_movntdq(unsigned long long addr, unsigned long long accesses, unsigned long long burst_length,unsigned long long call_latency,unsigned long long freq,unsigned long long running_threads,unsigned long long id, volatile void * sync_ptr,threaddata_t* data)
{
   unsigned long long passes;
   double ret;
   unsigned long long a,b,c,d;
   int i;
   
   #ifdef USE_PAPI
    if ((!id) && (data->num_events)) PAPI_reset(data->Eventset);
   #endif


   switch (burst_length)
   {

    case 1:
      passes=accesses/64;
      #if (ACCESS_STRIDE>0)
      passes*=16;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movntdq_1)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movntdq_1;"
                ".align 64,0x0;"
                "_work_loop_movntdq_1:"
#if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movntdq %%xmm0, 0(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 16(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 32(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 48(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movntdq %%xmm0, 64(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 80(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 96(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 112(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movntdq %%xmm0, 128(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 144(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 160(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 176(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movntdq %%xmm0, 192(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 208(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 224(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 240(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movntdq %%xmm0, 256(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 272(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 288(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 304(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movntdq %%xmm0, 320(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 336(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 352(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 368(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movntdq %%xmm0, 384(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 400(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 416(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 432(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movntdq %%xmm0, 448(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 464(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 480(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 496(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movntdq %%xmm0, 512(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 528(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 544(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 560(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movntdq %%xmm0, 576(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 592(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 608(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 624(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movntdq %%xmm0, 640(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 656(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 672(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 688(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movntdq %%xmm0, 704(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 720(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 736(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 752(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movntdq %%xmm0, 768(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 784(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 800(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 816(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movntdq %%xmm0, 832(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 848(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 864(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 880(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movntdq %%xmm0, 896(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 912(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 928(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 944(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movntdq %%xmm0, 960(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 976(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 992(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 1008(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_64(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movntdq_1;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*64);
        break;

    case 2:
      passes=accesses/64;
      #if (ACCESS_STRIDE>0)
      passes*=16;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movntdq_2)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movntdq_2;"
                ".align 64,0x0;"
                "_work_loop_movntdq_2:"
#if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movntdq %%xmm0, 0(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 16(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 32(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 48(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movntdq %%xmm0, 64(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 80(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 96(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 112(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movntdq %%xmm0, 128(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 144(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 160(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 176(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movntdq %%xmm0, 192(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 208(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 224(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 240(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movntdq %%xmm0, 256(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 272(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 288(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 304(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movntdq %%xmm0, 320(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 336(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 352(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 368(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movntdq %%xmm0, 384(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 400(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 416(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 432(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movntdq %%xmm0, 448(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 464(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 480(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 496(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movntdq %%xmm0, 512(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 528(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 544(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 560(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movntdq %%xmm0, 576(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 592(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 608(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 624(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movntdq %%xmm0, 640(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 656(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 672(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 688(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movntdq %%xmm0, 704(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 720(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 736(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 752(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movntdq %%xmm0, 768(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 784(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 800(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 816(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movntdq %%xmm0, 832(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 848(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 864(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 880(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movntdq %%xmm0, 896(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 912(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 928(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 944(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movntdq %%xmm0, 960(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 976(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 992(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 1008(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_64(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movntdq_2;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*64);
        break;

    case 3:
      passes=accesses/66;
      #if (ACCESS_STRIDE>0)
      passes*=16;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movntdq_3)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movntdq_3;"
                ".align 64,0x0;"
                "_work_loop_movntdq_3:"
#if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movntdq %%xmm0, 0(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 16(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 32(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 48(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movntdq %%xmm1, 64(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 80(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 96(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 112(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movntdq %%xmm2, 128(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 144(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 160(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 176(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movntdq %%xmm0, 192(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 208(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 224(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 240(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movntdq %%xmm1, 256(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 272(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 288(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 304(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movntdq %%xmm2, 320(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 336(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 352(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 368(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movntdq %%xmm0, 384(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 400(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 416(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 432(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movntdq %%xmm1, 448(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 464(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 480(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 496(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movntdq %%xmm2, 512(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 528(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 544(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 560(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movntdq %%xmm0, 576(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 592(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 608(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 624(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movntdq %%xmm1, 640(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 656(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 672(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 688(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movntdq %%xmm2, 704(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 720(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 736(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 752(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movntdq %%xmm0, 768(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 784(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 800(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 816(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movntdq %%xmm1, 832(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 848(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 864(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 880(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movntdq %%xmm2, 896(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 912(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 928(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 944(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movntdq %%xmm0, 960(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 976(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 992(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm0, 1008(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,rbx)
                "movntdq %%xmm1, 1024(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 1040(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_64(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_65(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                "add $1056,%%rbx;"
		#else
		INC_66(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movntdq_3;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*66);
        break;

    case 4:
      passes=accesses/64;
      #if (ACCESS_STRIDE>0)
      passes*=16;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movntdq_4)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movntdq_4;"
                ".align 64,0x0;"
                "_work_loop_movntdq_4:"
#if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movntdq %%xmm0, 0(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 16(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 32(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 48(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movntdq %%xmm0, 64(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 80(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 96(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 112(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movntdq %%xmm0, 128(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 144(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 160(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 176(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movntdq %%xmm0, 192(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 208(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 224(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 240(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movntdq %%xmm0, 256(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 272(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 288(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 304(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movntdq %%xmm0, 320(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 336(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 352(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 368(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movntdq %%xmm0, 384(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 400(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 416(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 432(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movntdq %%xmm0, 448(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 464(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 480(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 496(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movntdq %%xmm0, 512(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 528(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 544(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 560(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movntdq %%xmm0, 576(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 592(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 608(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 624(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movntdq %%xmm0, 640(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 656(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 672(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 688(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movntdq %%xmm0, 704(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 720(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 736(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 752(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movntdq %%xmm0, 768(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 784(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 800(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 816(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movntdq %%xmm0, 832(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 848(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 864(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 880(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movntdq %%xmm0, 896(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 912(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 928(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 944(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movntdq %%xmm0, 960(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 976(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 992(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 1008(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_64(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movntdq_4;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*64);
        break;

    case 8:
      passes=accesses/64;
      #if (ACCESS_STRIDE>0)
      passes*=16;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(movntdq_8)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_movntdq_8;"
                ".align 64,0x0;"
                "_work_loop_movntdq_8:"
#if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "movntdq %%xmm0, 0(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 16(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 32(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 48(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movntdq %%xmm4, 64(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm5, 80(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm6, 96(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm7, 112(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movntdq %%xmm0, 128(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 144(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 160(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 176(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movntdq %%xmm4, 192(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm5, 208(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm6, 224(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm7, 240(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movntdq %%xmm0, 256(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 272(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 288(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 304(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movntdq %%xmm4, 320(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm5, 336(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm6, 352(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm7, 368(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movntdq %%xmm0, 384(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 400(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 416(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 432(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movntdq %%xmm4, 448(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm5, 464(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm6, 480(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm7, 496(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movntdq %%xmm0, 512(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 528(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 544(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 560(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movntdq %%xmm4, 576(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm5, 592(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm6, 608(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm7, 624(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movntdq %%xmm0, 640(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 656(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 672(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 688(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movntdq %%xmm4, 704(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm5, 720(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm6, 736(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm7, 752(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movntdq %%xmm0, 768(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 784(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 800(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 816(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movntdq %%xmm4, 832(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm5, 848(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm6, 864(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm7, 880(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movntdq %%xmm0, 896(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm1, 912(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm2, 928(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm3, 944(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movntdq %%xmm4, 960(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm5, 976(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm6, 992(%%rbx);"NOP(NOPCOUNT)
                "movntdq %%xmm7, 1008(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(movntdq,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(movntdq,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(movntdq,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(movntdq,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(movntdq,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(movntdq,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(movntdq,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(movntdq,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(movntdq,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(movntdq,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(movntdq,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(movntdq,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(movntdq,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(movntdq,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(movntdq,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(movntdq,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_33(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_34(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_35(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_36(movntdq,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_37(movntdq,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_38(movntdq,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_39(movntdq,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_40(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_41(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_42(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_43(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_44(movntdq,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_45(movntdq,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_46(movntdq,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_47(movntdq,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_48(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_49(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_50(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_51(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_52(movntdq,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_53(movntdq,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_54(movntdq,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_55(movntdq,%%xmm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_56(movntdq,%%xmm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_57(movntdq,%%xmm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_58(movntdq,%%xmm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_59(movntdq,%%xmm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_60(movntdq,%%xmm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_61(movntdq,%%xmm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_62(movntdq,%%xmm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_63(movntdq,%%xmm7,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==16) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_64(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_movntdq_8;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*64);
        break;
      default: ret=0.0;break;
   }  
	
  #ifdef USE_PAPI
    if ((!id)&&(data->num_events))
    { 
      PAPI_read(data->Eventset,data->values);
      for (i=0;i<data->num_events;i++)
      {
         if (burst_length==1) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==2) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==3) data->papi_results[i]=(double)data->values[i]/(double)(passes*66);
         if (burst_length==4) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==8) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
      }
    }
    else for (i=0;i<data->num_events;i++) data->papi_results[i]==(double)0;
  #endif		
  return ret;
}

/** assembler implementation of bandwidth measurement using vmovntdq instruction
 */
static double asm_work_vmovntdq(unsigned long long addr, unsigned long long accesses, unsigned long long burst_length,unsigned long long call_latency,unsigned long long freq,unsigned long long running_threads,unsigned long long id, volatile void * sync_ptr,threaddata_t* data) __attribute__((noinline));
static double asm_work_vmovntdq(unsigned long long addr, unsigned long long accesses, unsigned long long burst_length,unsigned long long call_latency,unsigned long long freq,unsigned long long running_threads,unsigned long long id, volatile void * sync_ptr,threaddata_t* data)
{
   unsigned long long passes;
   double ret;
   unsigned long long a,b,c,d;
   int i;
   
   #ifdef USE_PAPI
    if ((!id) && (data->num_events)) PAPI_reset(data->Eventset);
   #endif

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }

   switch (burst_length)
   {

    case 1:
      passes=accesses/32;
      #if (ACCESS_STRIDE>0)
      passes*=32;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(vmovntdq_1)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_vmovntdq_1;"
                ".align 64,0x0;"
                "_work_loop_vmovntdq_1:"
#if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "vmovntdq %%ymm0, 0(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 32(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovntdq %%ymm0, 64(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 96(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovntdq %%ymm0, 128(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 160(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovntdq %%ymm0, 192(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 224(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovntdq %%ymm0, 256(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 288(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovntdq %%ymm0, 320(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 352(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovntdq %%ymm0, 384(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 416(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovntdq %%ymm0, 448(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 480(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovntdq %%ymm0, 512(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 544(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovntdq %%ymm0, 576(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 608(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovntdq %%ymm0, 640(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 672(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovntdq %%ymm0, 704(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 736(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovntdq %%ymm0, 768(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 800(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovntdq %%ymm0, 832(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 864(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovntdq %%ymm0, 896(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 928(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovntdq %%ymm0, 960(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 992(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_32(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_vmovntdq_1;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*32);
        break;

    case 2:
      passes=accesses/32;
      #if (ACCESS_STRIDE>0)
      passes*=32;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(vmovntdq_2)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_vmovntdq_2;"
                ".align 64,0x0;"
                "_work_loop_vmovntdq_2:"
#if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "vmovntdq %%ymm0, 0(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 32(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovntdq %%ymm0, 64(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 96(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovntdq %%ymm0, 128(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 160(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovntdq %%ymm0, 192(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 224(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovntdq %%ymm0, 256(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 288(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovntdq %%ymm0, 320(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 352(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovntdq %%ymm0, 384(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 416(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovntdq %%ymm0, 448(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 480(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovntdq %%ymm0, 512(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 544(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovntdq %%ymm0, 576(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 608(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovntdq %%ymm0, 640(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 672(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovntdq %%ymm0, 704(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 736(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovntdq %%ymm0, 768(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 800(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovntdq %%ymm0, 832(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 864(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovntdq %%ymm0, 896(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 928(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovntdq %%ymm0, 960(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 992(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_32(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_vmovntdq_2;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*32);
        break;

    case 3:
      passes=accesses/33;
      #if (ACCESS_STRIDE>0)
      passes*=32;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(vmovntdq_3)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_vmovntdq_3;"
                ".align 64,0x0;"
                "_work_loop_vmovntdq_3:"
#if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "vmovntdq %%ymm0, 0(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 32(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovntdq %%ymm2, 64(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 96(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovntdq %%ymm1, 128(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm2, 160(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovntdq %%ymm0, 192(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 224(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovntdq %%ymm2, 256(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 288(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovntdq %%ymm1, 320(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm2, 352(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovntdq %%ymm0, 384(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 416(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovntdq %%ymm2, 448(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 480(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovntdq %%ymm1, 512(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm2, 544(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovntdq %%ymm0, 576(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 608(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovntdq %%ymm2, 640(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 672(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovntdq %%ymm1, 704(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm2, 736(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovntdq %%ymm0, 768(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 800(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovntdq %%ymm2, 832(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm0, 864(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovntdq %%ymm1, 896(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm2, 928(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovntdq %%ymm0, 960(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 992(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,rbx)
                "vmovntdq %%ymm2, 1024(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_32(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                "add $1056,%%rbx;"
		#else
		INC_33(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_vmovntdq_3;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*33);
        break;

    case 4:
      passes=accesses/32;
      #if (ACCESS_STRIDE>0)
      passes*=32;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(vmovntdq_4)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_vmovntdq_4;"
                ".align 64,0x0;"
                "_work_loop_vmovntdq_4:"
#if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "vmovntdq %%ymm0, 0(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 32(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovntdq %%ymm2, 64(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm3, 96(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovntdq %%ymm0, 128(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 160(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovntdq %%ymm2, 192(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm3, 224(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovntdq %%ymm0, 256(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 288(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovntdq %%ymm2, 320(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm3, 352(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovntdq %%ymm0, 384(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 416(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovntdq %%ymm2, 448(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm3, 480(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovntdq %%ymm0, 512(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 544(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovntdq %%ymm2, 576(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm3, 608(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovntdq %%ymm0, 640(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 672(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovntdq %%ymm2, 704(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm3, 736(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovntdq %%ymm0, 768(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 800(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovntdq %%ymm2, 832(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm3, 864(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovntdq %%ymm0, 896(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 928(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovntdq %%ymm2, 960(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm3, 992(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(vmovntdq,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(vmovntdq,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(vmovntdq,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(vmovntdq,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(vmovntdq,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(vmovntdq,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(vmovntdq,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(vmovntdq,%%ymm3,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_32(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_vmovntdq_4;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*32);
        break;

    case 8:
      passes=accesses/32;
      #if (ACCESS_STRIDE>0)
      passes*=32;
      passes/=ACCESS_STRIDE;
      #endif
      if (!passes) return 0;
      /*
       * Input:  RAX: addr (pointer to the buffer)
       *         RBX: passes (number of iterations)
       *         RCX: running_threads (number of threads)
       *         RDX: id (thread ID)
       *         RSI: sync_ptr (pointer to sync buffer for cmpxchg and TSC sync)
       * Output: RAX: stop timestamp 
       *         RBX: start timestamp
       *         RCX: scheduled start (0 if TSC sync is disabled)
       */
       __asm__ __volatile__(
                "push %%rbp;"       // store rbp to make it available for use as general purpose register
                "mov %%rsi,%%r8;"   // sync_ptr        (input for SYNC)
                "mov %%rax,%%r9;"   // move addr       (rax destroyed by SYNC)
                "mov %%rbx,%%r10;"  // move passes     (rbx destroyed by SYNC)
                "mov %%rcx,%%r11;"  // running threads (input for SYNC)
                "mov %%rdx,%%r12;"  // ID              (input for SYNC)
                SYNC(vmovntdq_8)
                "push %%r13;"       // output of SYNC  (start time)
                "mov %%r9,%%rbx;"   // move addr to rbx
                "mov %%r10,%%rcx;"  // move loop counter to rcx
                TIMESTAMP
                "push %%rax;"
                SERIALIZE
                "jmp _work_loop_vmovntdq_8;"
                ".align 64,0x0;"
                "_work_loop_vmovntdq_8:"
#if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                PREFETCH(LINE_PREFETCH,0,rbx)
                "vmovntdq %%ymm0, 0(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 32(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovntdq %%ymm2, 64(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm3, 96(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovntdq %%ymm4, 128(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm5, 160(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovntdq %%ymm6, 192(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm7, 224(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovntdq %%ymm0, 256(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 288(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovntdq %%ymm2, 320(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm3, 352(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovntdq %%ymm4, 384(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm5, 416(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovntdq %%ymm6, 448(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm7, 480(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovntdq %%ymm0, 512(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 544(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovntdq %%ymm2, 576(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm3, 608(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovntdq %%ymm4, 640(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm5, 672(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovntdq %%ymm6, 704(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm7, 736(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovntdq %%ymm0, 768(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm1, 800(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovntdq %%ymm2, 832(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm3, 864(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovntdq %%ymm4, 896(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm5, 928(%%rbx);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovntdq %%ymm6, 960(%%rbx);"NOP(NOPCOUNT)
                "vmovntdq %%ymm7, 992(%%rbx);"NOP(NOPCOUNT)
#else
                WRITE_ACCESS_0(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_1(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_2(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_3(vmovntdq,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_4(vmovntdq,%%ymm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_5(vmovntdq,%%ymm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_6(vmovntdq,%%ymm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_7(vmovntdq,%%ymm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_8(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_9(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_10(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_11(vmovntdq,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_12(vmovntdq,%%ymm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_13(vmovntdq,%%ymm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_14(vmovntdq,%%ymm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_15(vmovntdq,%%ymm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_16(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_17(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_18(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_19(vmovntdq,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_20(vmovntdq,%%ymm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_21(vmovntdq,%%ymm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_22(vmovntdq,%%ymm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_23(vmovntdq,%%ymm7,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_24(vmovntdq,%%ymm0,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_25(vmovntdq,%%ymm1,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_26(vmovntdq,%%ymm2,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_27(vmovntdq,%%ymm3,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_28(vmovntdq,%%ymm4,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_29(vmovntdq,%%ymm5,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_30(vmovntdq,%%ymm6,%%rbx)NOP(NOPCOUNT)
                WRITE_ACCESS_31(vmovntdq,%%ymm7,%%rbx)NOP(NOPCOUNT)
#endif
                #if (ACCESS_STRIDE==32) || (ACCESS_STRIDE==0)
                "add $1024,%%rbx;"
		#else
		INC_32(%%rbx)
		#endif
                "sub $1,%%rcx;"
     
                "jnz _work_loop_vmovntdq_8;"
                SERIALIZE
                TIMESTAMP
                "pop %%rbx;"
                "pop %%rcx;"
                "pop %%rbp;"
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
                : "a"(addr), "b" (passes), "c" (running_threads), "d" (id), "S" (sync_ptr)
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory", "memory"

        );
        data->start_ts=b;
        data->end_ts=a;
        //if (c>0) printf("ID: %3i - scheduled: %llx, start: %llx (+%5lli), end: %llx (+%5lli, duration: %5lli)\n",id,c,b,b-c,a,a-c,a-b);
        //else printf("ID: %3i - start: %llx, end: %llx, duration: %5lli\n",id,b,a,a-b);

        ret=(double)(passes*32);
        break;
      default: ret=0.0;break;
   }  
	
  #ifdef USE_PAPI
    if ((!id)&&(data->num_events))
    { 
      PAPI_read(data->Eventset,data->values);
      for (i=0;i<data->num_events;i++)
      {
         if (burst_length==1) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==2) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==3) data->papi_results[i]=(double)data->values[i]/(double)(passes*66);
         if (burst_length==4) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
         if (burst_length==8) data->papi_results[i]=(double)data->values[i]/(double)(passes*64);
      }
    }
    else for (i=0;i<data->num_events;i++) data->papi_results[i]==(double)0;
  #endif		
  return ret;
}

/** function that performs the measurement
 *   - entry point for BenchIT framework (called by bi_entry())
 */
void  _work( unsigned long long memsize, int offset, int function, int burst_length, int runs, volatile mydata_t* data, double **results)
{
  int latency,i,j,k,t;
  int loop_overhead=0;
  double tmax;
  double tmp=(double)0;
  unsigned long long tmp2,tmp3;
  int dtsize, looplength;
  unsigned long long aligned_addr,accesses;

  int ignors,resets,discard;
  int sync_variation=0;
  int duration_variation=0;

  aligned_addr=(unsigned long long)(data->buffer) + offset;

  switch (function) {
    case 1: dtsize = 32; break; // vmovdqa 
    case 3: dtsize = 32; break; // vmovdqu 
    case 4: dtsize = 8; break; // mov 
    case 5: dtsize = 8; break; // movnti 
    case 7: dtsize = 32; break; // vmovntdq 
    default: dtsize = 16; break; // SSE funktions
  }
  switch (burst_length) {
    case 1: looplength = 64; break;
    case 2: looplength = 64; break;
    case 3: looplength = 66; break;
    case 4: looplength = 64; break;
    case 8: looplength = 64; break;
  }

  accesses = memsize / dtsize;

   t=data->num_threads-1;
   tmax=-1.0;
   latency=data->cpuinfo->rdtsc_latency;
   if ((data->settings)&LOOP_OVERHEAD_COMP) loop_overhead=asm_loop_overhead(100);
   else loop_overhead=latency;

   if ((memsize / (looplength*16)) >= 4*(t+1))
   {
    data->running_threads=t+1;

    //init threaddata
    if (t)
    {
     for (j=0;j<t;j++){
      data->threaddata[j+1].memsize = memsize/(t+1);
      data->threaddata[j+1].accesses = accesses/(t+1);
      }
    }   

    ignors=4*runs;
    resets=runs;
    discard=0;

    if (memsize > (data->cpuinfo->Total_D_Cache_Size * data->cpuinfo->num_numa_nodes)) runs/=3;
    if (runs==0) runs=1;
   
    for (i=0;i<runs;i++)
    {
     data->synch[0]=0;
     /* copy invariant TSC flag to sync area, asm work functions will skip TSC based synchronization if not set */ 
     data->synch[1]=data->cpuinfo->tsc_invariant;

     //tell other threads to touch memory 
     if (t)
     {
       for (j=0;j<t;j++)
       {
        data->thread_comm[j+1]=THREAD_USE_MEMORY;
        while (!data->ack);
        data->ack=0;
        //printf("per thread: memsize: %i, accesses: %i\n",data->threaddata[j+1].memsize,data->threaddata[j+1].accesses);
       }
     }
          
     //access whole buffer to warm up cache and tlb
     use_memory((void*)aligned_addr,data->cache_flush_area,memsize/(t+1),data->USE_MODE,data->USE_DIRECTION,data->NUM_USES,*(data->cpuinfo));
     //flush cachelevels as specified in PARAMETERS
     flush_caches((void*) aligned_addr,memsize/(t+1),data->settings,data->NUM_FLUSHES,data->FLUSH_MODE,data->cache_flush_area,data->cpuinfo,0,data->running_threads);

     /* most likely never necessary - uncomment in case of deadlocks
      * //wait for other threads touching the memory
      * if (t)
      * {
      *   for (j=0;j<t;j++){
      *     data->thread_comm[j+1]=THREAD_WAIT;       
      *     while (!data->ack);
      *     data->ack=0;
      *   }
      * }
      */

     //prefetch measurement routine if enabled
     if (data->ENABLE_CODE_PREFETCH){
       data->done=0;
//      __asm__ __volatile__("mfence;"::: "memory");

     
       //tell other threads to prefetch code
       if (t)
       {
         for (j=0;j<t;j++){
           data->thread_comm[j+1]=THREAD_PREFETCH_CODE;
           while (data->ack!=j+1);
           data->ack=0;
         }
       }

       for (k=0;k<data->NUM_USES;k++){
         /* call ASM implementation */
         switch(function)
         {
          case 0: tmp=asm_work_movdqa((unsigned long long)data->cache_flush_area,48,burst_length,0,data->cpuinfo->clockrate,data->running_threads,0,(&(data->synch[0])),&(data->threaddata[0]));break;
          case 1: tmp=asm_work_vmovdqa((unsigned long long)data->cache_flush_area,24,burst_length,0,data->cpuinfo->clockrate,data->running_threads,0,(&(data->synch[0])),&(data->threaddata[0]));break;
          case 2: tmp=asm_work_movdqu((unsigned long long)data->cache_flush_area,48,burst_length,0,data->cpuinfo->clockrate,data->running_threads,0,(&(data->synch[0])),&(data->threaddata[0]));break;
          case 3: tmp=asm_work_vmovdqu((unsigned long long)data->cache_flush_area,24,burst_length,0,data->cpuinfo->clockrate,data->running_threads,0,(&(data->synch[0])),&(data->threaddata[0]));break;
          case 4: tmp=asm_work_mov((unsigned long long)data->cache_flush_area,96,burst_length,0,data->cpuinfo->clockrate,data->running_threads,0,(&(data->synch[0])),&(data->threaddata[0]));break;
          case 5: tmp=asm_work_movnti((unsigned long long)data->cache_flush_area,96,burst_length,0,data->cpuinfo->clockrate,data->running_threads,0,(&(data->synch[0])),&(data->threaddata[0]));break;
          case 6: tmp=asm_work_movntdq((unsigned long long)data->cache_flush_area,48,burst_length,0,data->cpuinfo->clockrate,data->running_threads,0,(&(data->synch[0])),&(data->threaddata[0]));break;
          case 7: tmp=asm_work_vmovntdq((unsigned long long)data->cache_flush_area,24,burst_length,0,data->cpuinfo->clockrate,data->running_threads,0,(&(data->synch[0])),&(data->threaddata[0]));break;
          default:
           fprintf(stderr,"Error: unknown function %i\n",function);
           exit(1);
         }

         //wait for other THREADS
         data->done=1;
         while(data->done!=data->running_threads);
         
         //restore sync variables
         data->synch[0]=0;
         data->synch[1]=data->cpuinfo->tsc_invariant;
//      __asm__ __volatile__("mfence;"::: "memory");

       }       
     }

     //tell other threads to start
     if (t)
     {
       for (j=0;j<t;j++){
         data->thread_comm[j+1]=THREAD_WORK;
         while (!data->ack);
         data->ack=0;
       }
     }      


      /* call ASM implementation (latency=0 as loop_overhead is compensated later) */
      switch(function)
      {
        case 0: tmp=asm_work_movdqa(aligned_addr,((accesses/(t+1))),burst_length,0,data->cpuinfo->clockrate,data->running_threads,0,(&(data->synch[0])),&(data->threaddata[0]));break;
        case 1: tmp=asm_work_vmovdqa(aligned_addr,((accesses/(t+1))),burst_length,0,data->cpuinfo->clockrate,data->running_threads,0,(&(data->synch[0])),&(data->threaddata[0]));break;
        case 2: tmp=asm_work_movdqu(aligned_addr,((accesses/(t+1))),burst_length,0,data->cpuinfo->clockrate,data->running_threads,0,(&(data->synch[0])),&(data->threaddata[0]));break;
        case 3: tmp=asm_work_vmovdqu(aligned_addr,((accesses/(t+1))),burst_length,0,data->cpuinfo->clockrate,data->running_threads,0,(&(data->synch[0])),&(data->threaddata[0]));break;
        case 4: tmp=asm_work_mov(aligned_addr,((accesses/(t+1))),burst_length,0,data->cpuinfo->clockrate,data->running_threads,0,(&(data->synch[0])),&(data->threaddata[0]));break;
        case 5: tmp=asm_work_movnti(aligned_addr,((accesses/(t+1))),burst_length,0,data->cpuinfo->clockrate,data->running_threads,0,(&(data->synch[0])),&(data->threaddata[0]));break;
        case 6: tmp=asm_work_movntdq(aligned_addr,((accesses/(t+1))),burst_length,0,data->cpuinfo->clockrate,data->running_threads,0,(&(data->synch[0])),&(data->threaddata[0]));break;
        case 7: tmp=asm_work_vmovntdq(aligned_addr,((accesses/(t+1))),burst_length,0,data->cpuinfo->clockrate,data->running_threads,0,(&(data->synch[0])),&(data->threaddata[0]));break;
        default:
         fprintf(stderr,"Error: unknown function %i\n",function);
         exit(1);
      }     
      tmp2=data->threaddata[0].start_ts;
      tmp3=data->threaddata[0].end_ts;
      
      
     //wait for other THREADS
     if (t)
     {
       long long min_start,max_start,min_dur,max_dur;
       min_start=tmp2;
       max_start=tmp2;
       min_dur=tmp3-tmp2;

       for (j=0;j<t;j++)
       {
         data->thread_comm[j+1]=THREAD_WAIT;       
         while (!data->ack);
         data->ack=0;

         /* choose longest interval (assume concurrent start) */
         if ((data->threaddata[j+1].end_ts-data->threaddata[j+1].start_ts)>(tmp3-tmp2)){
           tmp2=data->threaddata[j+1].start_ts;
           tmp3=data->threaddata[j+1].end_ts; 
         }
         if (data->cpuinfo->tsc_invariant==1){
           if (data->threaddata[j+1].start_ts<min_start) min_start=data->threaddata[j+1].start_ts;
           if (data->threaddata[j+1].start_ts>max_start) max_start=data->threaddata[j+1].start_ts;
         }
         if ((data->threaddata[j+1].end_ts-data->threaddata[j+1].start_ts)<min_dur) min_dur=data->threaddata[j+1].end_ts-data->threaddata[j+1].start_ts;
         max_dur=tmp3-tmp2;
       }
       if(!sync_variation) sync_variation=1.5*(max_start-min_start)+latency;
       if(!duration_variation) duration_variation=1.2*(max_dur-min_dur)+latency;

       //printf("%i: duration: %lli(+%i), sync variation: %lli (%i), duration variation: %lli (%i)\n",i,(tmp3-tmp2)-loop_overhead,loop_overhead,max_start-min_start,sync_variation,max_dur-min_dur,duration_variation);

       /* discard values with high variation in start or stop timestamps based on best case seen so far */
       if ((ignors)&&((max_dur-min_dur)>0.01*max_dur)&&((max_dur-min_dur)>duration_variation)) {
          ignors--;
          i--;
          discard++;
          //printf("discarding value: high duration variation\n");
       }
       else {
          //adopt duration variation if necessary
          if ( 1.4 * (max_dur-min_dur)+(double)latency < (double) duration_variation){
            duration_variation=(int)(1.2*(max_dur-min_dur))+latency;
            if (resets) {resets--;discard+=(i+1);i=0;ignors=4*runs;}
          }
          if (data->cpuinfo->tsc_invariant==1){
            if((ignors)&&((max_start-min_start)>sync_variation)) {
              ignors--;
              i--;
              discard++;
              //printf("discarding value: high synchronization variation\n");
            }
            else {
              //adopt sync variation if necessary
              if (1.7*(max_start-min_start)+(double)latency<(double)sync_variation) sync_variation=(int)(1.5*(max_start-min_start))+latency;
            }
          }
       }
     } 

     tmp2=(tmp3-tmp2)-loop_overhead;

     if ((int)tmp!=-1)
      {
       tmp=((((double)(tmp*(t+1)*dtsize)))/ ((double)(tmp2)/data->cpuinfo->clockrate)) *0.000000001;

       if (tmp>tmax) tmax=tmp;
      }
    }
   }
   //printf("memsize: %lli, discarded values: %i, %i resets\n",memsize,discard,runs-resets);
  
   if (tmax>0.0)
   {
     (*results)[0]=(double)tmax;
     #ifdef USE_PAPI
     for (j=0;j<data->num_events;j++)
     {
       (*results)[j+1]=0;
       for (t=0;t<data->num_threads;t++)
       {
         (*results)[j+1]+=data->threaddata[t].papi_results[j];
       }
       //if (data->num_threads) (*results)[j+1]=(double)(*results)[j+1]/(double)data->num_threads;
     }
     #endif
   }
   else 
   {
     (*results)[0]=INVALID_MEASUREMENT;
     #ifdef USE_PAPI
     for (j=0;j<data->num_events;j++)
     {
       (*results)[j+1]=INVALID_MEASUREMENT;
     }
     #endif    
   }
}



/** loop for additional worker threads
 *  communicating with master thread using shared variables
 */
void *thread(void *threaddata)
{
  int id= ((threaddata_t *) threaddata)->thread_id;
  unsigned int numa_node;
  struct bitmask *numa_bitmask;
  volatile mydata_t* global_data = ((threaddata_t *) threaddata)->data; //communication
  threaddata_t* mydata = (threaddata_t*)threaddata;
  char* filename=NULL;

  struct timespec wait_ns;
  int j,k,fd;
  double tmp=(double)0;
  unsigned long long i,tmp2,tmp3,old=THREAD_STOP;
  
  wait_ns.tv_sec=0;
  wait_ns.tv_nsec=100000;
  
  do
  {
   old=global_data->thread_comm[id];
  }
  while (old!=THREAD_INIT);
  global_data->ack=id;

  cpu_set(((threaddata_t *) threaddata)->mem_bind);
  numa_node = numa_node_of_cpu(((threaddata_t *) threaddata)->mem_bind);
  numa_bitmask = numa_bitmask_alloc((unsigned int) numa_max_possible_node());
  numa_bitmask = numa_bitmask_clearall(numa_bitmask);
  numa_bitmask = numa_bitmask_setbit(numa_bitmask, numa_node);
  numa_set_membind(numa_bitmask);
  numa_bitmask_free(numa_bitmask);

  if(mydata->buffersize)
  {
    if (global_data->hugepages==HUGEPAGES_OFF) mydata->buffer = (void *) _mm_malloc( mydata->buffersize,mydata->alignment);
    if (global_data->hugepages==HUGEPAGES_ON)
    {
      char *dir;
      dir=bi_getenv("BENCHIT_KERNEL_HUGEPAGE_DIR",0);
      filename=(char*)malloc((strlen(dir)+20)*sizeof(char));
      sprintf(filename,"%s/thread_data_%i",dir,id);
      mydata->buffer=NULL;
      fd=open(filename,O_CREAT|O_RDWR,0664);
      if (fd == -1)
      {
        fprintf( stderr, "Allocation of buffer failed\n" ); fflush( stderr );
        perror("open");
        exit( 127 );
      } 
      mydata->buffer=(char*) mmap(NULL,mydata->buffersize,PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);
      close(fd);unlink(filename);
    } 
    //fill buffer
   /* initialize buffer */
   tmp=sizeof(unsigned long long);
   for (i=0;i<=mydata->buffersize-tmp;i+=tmp){
      *((unsigned long long*)((unsigned long long)mydata->buffer+i))=(unsigned long long)i;
   }

    clflush(mydata->buffer,mydata->buffersize,*(mydata->cpuinfo));
    mydata->aligned_addr=(unsigned long long)(mydata->buffer) + mydata->offset + id*mydata->thread_offset;
  }

  cpu_set(((threaddata_t *) threaddata)->cpu_id);
  while(1)
  {
     switch (global_data->thread_comm[id]){
       case THREAD_USE_MEMORY: 
         if (old!=THREAD_USE_MEMORY)
         {
           old=THREAD_USE_MEMORY;
           global_data->ack=id;

           if (!mydata->buffersize)
           {
             mydata->buffer = (char*) (((unsigned long long)global_data->buffer+((id)*mydata->memsize)+mydata->alignment)&((mydata->alignment-1)^0xffffffffffffffffULL));
             mydata->aligned_addr = (unsigned long long)(mydata->buffer) + mydata->offset;
           }
           // use memory
           use_memory((void*)mydata->aligned_addr,mydata->cache_flush_area,mydata->memsize,mydata->USE_MODE,mydata->USE_DIRECTION,mydata->NUM_USES,*(mydata->cpuinfo)); 
         }
         else 
         {
           tmp=100;while(tmp>0) tmp--; 
         }        
         break;
       case THREAD_FLUSH: 
         if (old!=THREAD_FLUSH)
         {
           old=THREAD_FLUSH;
           global_data->ack=id;

           //flush cachelevels as specified in PARAMETERS
           flush_caches((void*) (mydata->aligned_addr),mydata->memsize,mydata->settings,mydata->NUM_FLUSHES,mydata->FLUSH_MODE,mydata->cache_flush_area,mydata->cpuinfo,id,global_data->running_threads);
         }
         else 
         {
           tmp=100;while(tmp>0) tmp--; 
         }        
         break;
       case THREAD_WAIT: // waiting
          if (old!=THREAD_WAIT) {
             global_data->ack=id;old=THREAD_WAIT;
          }
          tmp=100;while(tmp) tmp--; 
          break;
       case THREAD_PREFETCH_CODE:
          if (old!=THREAD_PREFETCH_CODE) {
           global_data->ack=id;old=THREAD_PREFETCH_CODE;
           for (k=0;k<mydata->NUM_USES;k++){
            /* call ASM implementation */

            /* call ASM implementation */
            switch (mydata->FUNCTION)
            {
               case 0: tmp=asm_work_movdqa((unsigned long long)(mydata->cache_flush_area),48,mydata->BURST_LENGTH,0,global_data->cpuinfo->clockrate,global_data->running_threads,id,(&(global_data->synch[0])),mydata);break;
               case 1: tmp=asm_work_vmovdqa((unsigned long long)(mydata->cache_flush_area),24,mydata->BURST_LENGTH,0,global_data->cpuinfo->clockrate,global_data->running_threads,id,(&(global_data->synch[0])),mydata);break;
               case 2: tmp=asm_work_movdqu((unsigned long long)(mydata->cache_flush_area),48,mydata->BURST_LENGTH,0,global_data->cpuinfo->clockrate,global_data->running_threads,id,(&(global_data->synch[0])),mydata);break;
               case 3: tmp=asm_work_vmovdqu((unsigned long long)(mydata->cache_flush_area),24,mydata->BURST_LENGTH,0,global_data->cpuinfo->clockrate,global_data->running_threads,id,(&(global_data->synch[0])),mydata);break;
               case 4: tmp=asm_work_mov((unsigned long long)(mydata->cache_flush_area),96,mydata->BURST_LENGTH,0,global_data->cpuinfo->clockrate,global_data->running_threads,id,(&(global_data->synch[0])),mydata);break;
               case 5: tmp=asm_work_movnti((unsigned long long)(mydata->cache_flush_area),96,mydata->BURST_LENGTH,0,global_data->cpuinfo->clockrate,global_data->running_threads,id,(&(global_data->synch[0])),mydata);break;
               case 6: tmp=asm_work_movntdq((unsigned long long)(mydata->cache_flush_area),48,mydata->BURST_LENGTH,0,global_data->cpuinfo->clockrate,global_data->running_threads,id,(&(global_data->synch[0])),mydata);break;
               case 7: tmp=asm_work_vmovntdq((unsigned long long)(mydata->cache_flush_area),24,mydata->BURST_LENGTH,0,global_data->cpuinfo->clockrate,global_data->running_threads,id,(&(global_data->synch[0])),mydata);break;
               default:
                 fprintf(stderr,"Error: unknown function %i\n",mydata->FUNCTION);
                 pthread_exit(NULL);
               break;
            }
            while (global_data->done!=id);
            global_data->done=id+1;
           }
          }
         else 
         {
           tmp=100;while(tmp>0) tmp--; 
         }        
         break;
       case THREAD_WORK:
          if (old!=THREAD_WORK) 
          {

            global_data->ack=id;old=THREAD_WORK;
            
            if (!mydata->buffersize)
            {
             mydata->buffer = (char*) (((unsigned long long)global_data->buffer+((id)*mydata->memsize)+mydata->alignment)&((mydata->alignment-1)^0xffffffffffffffffULL));
             mydata->aligned_addr = (unsigned long long)(mydata->buffer) + mydata->offset;
            }

            /* call ASM implementation */
            switch (mydata->FUNCTION)
            {
               case 0: tmp=asm_work_movdqa(mydata->aligned_addr,mydata->accesses,mydata->BURST_LENGTH,0,global_data->cpuinfo->clockrate,global_data->running_threads,id,(&(global_data->synch[0])),mydata);break;
               case 1: tmp=asm_work_vmovdqa(mydata->aligned_addr,mydata->accesses,mydata->BURST_LENGTH,0,global_data->cpuinfo->clockrate,global_data->running_threads,id,(&(global_data->synch[0])),mydata);break;
               case 2: tmp=asm_work_movdqu(mydata->aligned_addr,mydata->accesses,mydata->BURST_LENGTH,0,global_data->cpuinfo->clockrate,global_data->running_threads,id,(&(global_data->synch[0])),mydata);break;
               case 3: tmp=asm_work_vmovdqu(mydata->aligned_addr,mydata->accesses,mydata->BURST_LENGTH,0,global_data->cpuinfo->clockrate,global_data->running_threads,id,(&(global_data->synch[0])),mydata);break;
               case 4: tmp=asm_work_mov(mydata->aligned_addr,mydata->accesses,mydata->BURST_LENGTH,0,global_data->cpuinfo->clockrate,global_data->running_threads,id,(&(global_data->synch[0])),mydata);break;
               case 5: tmp=asm_work_movnti(mydata->aligned_addr,mydata->accesses,mydata->BURST_LENGTH,0,global_data->cpuinfo->clockrate,global_data->running_threads,id,(&(global_data->synch[0])),mydata);break;
               case 6: tmp=asm_work_movntdq(mydata->aligned_addr,mydata->accesses,mydata->BURST_LENGTH,0,global_data->cpuinfo->clockrate,global_data->running_threads,id,(&(global_data->synch[0])),mydata);break;
               case 7: tmp=asm_work_vmovntdq(mydata->aligned_addr,mydata->accesses,mydata->BURST_LENGTH,0,global_data->cpuinfo->clockrate,global_data->running_threads,id,(&(global_data->synch[0])),mydata);break;
               default:
                 fprintf(stderr,"Error: unknown function %i\n",mydata->FUNCTION);
                 pthread_exit(NULL);
               break;
            }
          }
          else 
          {
            tmp=100;while(tmp>0) tmp--; 
          }  
          break;
       case THREAD_INIT: // used for parallel initialisation only
          tmp=100;while(tmp) tmp--; 
          break;
       case THREAD_STOP: // exit
       default:
         if (global_data->hugepages==HUGEPAGES_ON)
         {
           if(mydata->buffer!=NULL) munmap((void*)mydata->buffer,mydata->buffersize);
         }
         pthread_exit(NULL);
    }
  }
}


