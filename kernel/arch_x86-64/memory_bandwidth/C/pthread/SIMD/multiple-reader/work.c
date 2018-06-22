/******************************************************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id$
 * For license details see COPYING in the package base directory
 ******************************************************************************************************/
/* Kernel: measures aggregate read bandwidth of multiple parallel threads for cache levels and main memory.
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
                "movdqa 0(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 16(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 32(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 48(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqa 64(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 80(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 96(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 112(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqa 128(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 144(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 160(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 176(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqa 192(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 208(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 224(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 240(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqa 256(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 272(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 288(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 304(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqa 320(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 336(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 352(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 368(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqa 384(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 400(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 416(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 432(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqa 448(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 464(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 480(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 496(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqa 512(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 528(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 544(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 560(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqa 576(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 592(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 608(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 624(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqa 640(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 656(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 672(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 688(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqa 704(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 720(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 736(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 752(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqa 768(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 784(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 800(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 816(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqa 832(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 848(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 864(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 880(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqa 896(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 912(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 928(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 944(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqa 960(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 976(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 992(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 1008(%%rbx), %%xmm0;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_1(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_2(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_3(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_4(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_5(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_6(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_7(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_8(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_9(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_10(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_11(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_12(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_13(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_14(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_15(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_16(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_17(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_18(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_19(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_20(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_21(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_22(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_23(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_24(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_25(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_26(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_27(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_28(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_29(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_30(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_31(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_32(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_33(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_34(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_35(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_36(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_37(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_38(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_39(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_40(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_41(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_42(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_43(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_44(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_45(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_46(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_47(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_48(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_49(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_50(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_51(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_52(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_53(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_54(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_55(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_56(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_57(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_58(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_59(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_60(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_61(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_62(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_63(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "movdqa 0(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 16(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 32(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 48(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqa 64(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 80(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 96(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 112(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqa 128(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 144(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 160(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 176(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqa 192(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 208(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 224(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 240(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqa 256(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 272(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 288(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 304(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqa 320(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 336(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 352(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 368(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqa 384(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 400(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 416(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 432(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqa 448(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 464(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 480(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 496(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqa 512(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 528(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 544(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 560(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqa 576(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 592(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 608(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 624(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqa 640(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 656(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 672(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 688(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqa 704(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 720(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 736(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 752(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqa 768(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 784(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 800(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 816(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqa 832(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 848(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 864(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 880(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqa 896(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 912(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 928(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 944(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqa 960(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 976(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 992(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 1008(%%rbx), %%xmm1;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_1(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_2(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_3(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_4(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_5(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_6(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_7(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_8(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_9(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_10(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_11(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_12(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_13(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_14(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_15(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_16(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_17(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_18(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_19(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_20(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_21(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_22(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_23(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_24(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_25(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_26(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_27(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_28(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_29(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_30(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_31(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_32(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_33(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_34(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_35(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_36(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_37(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_38(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_39(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_40(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_41(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_42(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_43(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_44(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_45(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_46(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_47(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_48(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_49(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_50(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_51(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_52(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_53(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_54(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_55(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_56(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_57(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_58(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_59(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_60(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_61(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_62(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_63(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "movdqa 0(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 16(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 32(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 48(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqa 64(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 80(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 96(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 112(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqa 128(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 144(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 160(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 176(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqa 192(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 208(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 224(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 240(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqa 256(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 272(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 288(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 304(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqa 320(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 336(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 352(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 368(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqa 384(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 400(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 416(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 432(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqa 448(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 464(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 480(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 496(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqa 512(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 528(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 544(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 560(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqa 576(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 592(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 608(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 624(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqa 640(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 656(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 672(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 688(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqa 704(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 720(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 736(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 752(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqa 768(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 784(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 800(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 816(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqa 832(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 848(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 864(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 880(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqa 896(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 912(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 928(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 944(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqa 960(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 976(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 992(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 1008(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,rbx)
                "movdqa 1024(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 1040(%%rbx), %%xmm2;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_1(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_2(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_3(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_4(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_5(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_6(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_7(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_8(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_9(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_10(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_11(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_12(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_13(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_14(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_15(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_16(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_17(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_18(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_19(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_20(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_21(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_22(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_23(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_24(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_25(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_26(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_27(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_28(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_29(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_30(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_31(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_32(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_33(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_34(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_35(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_36(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_37(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_38(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_39(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_40(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_41(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_42(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_43(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_44(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_45(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_46(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_47(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_48(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_49(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_50(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_51(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_52(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_53(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_54(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_55(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_56(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_57(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_58(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_59(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_60(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_61(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_62(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_63(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_64(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_65(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "movdqa 0(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 16(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 32(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 48(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqa 64(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 80(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 96(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 112(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqa 128(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 144(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 160(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 176(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqa 192(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 208(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 224(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 240(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqa 256(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 272(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 288(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 304(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqa 320(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 336(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 352(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 368(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqa 384(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 400(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 416(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 432(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqa 448(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 464(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 480(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 496(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqa 512(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 528(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 544(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 560(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqa 576(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 592(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 608(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 624(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqa 640(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 656(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 672(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 688(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqa 704(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 720(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 736(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 752(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqa 768(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 784(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 800(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 816(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqa 832(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 848(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 864(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 880(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqa 896(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 912(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 928(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 944(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqa 960(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 976(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 992(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 1008(%%rbx), %%xmm3;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_1(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_2(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_3(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_4(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_5(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_6(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_7(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_8(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_9(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_10(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_11(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_12(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_13(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_14(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_15(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_16(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_17(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_18(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_19(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_20(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_21(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_22(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_23(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_24(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_25(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_26(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_27(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_28(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_29(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_30(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_31(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_32(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_33(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_34(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_35(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_36(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_37(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_38(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_39(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_40(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_41(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_42(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_43(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_44(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_45(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_46(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_47(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_48(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_49(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_50(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_51(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_52(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_53(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_54(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_55(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_56(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_57(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_58(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_59(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_60(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_61(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_62(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_63(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "movdqa 0(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 16(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 32(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 48(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqa 64(%%rbx), %%xmm4;"NOP(NOPCOUNT)
                "movdqa 80(%%rbx), %%xmm5;"NOP(NOPCOUNT)
                "movdqa 96(%%rbx), %%xmm6;"NOP(NOPCOUNT)
                "movdqa 112(%%rbx), %%xmm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqa 128(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 144(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 160(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 176(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqa 192(%%rbx), %%xmm4;"NOP(NOPCOUNT)
                "movdqa 208(%%rbx), %%xmm5;"NOP(NOPCOUNT)
                "movdqa 224(%%rbx), %%xmm6;"NOP(NOPCOUNT)
                "movdqa 240(%%rbx), %%xmm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqa 256(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 272(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 288(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 304(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqa 320(%%rbx), %%xmm4;"NOP(NOPCOUNT)
                "movdqa 336(%%rbx), %%xmm5;"NOP(NOPCOUNT)
                "movdqa 352(%%rbx), %%xmm6;"NOP(NOPCOUNT)
                "movdqa 368(%%rbx), %%xmm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqa 384(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 400(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 416(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 432(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqa 448(%%rbx), %%xmm4;"NOP(NOPCOUNT)
                "movdqa 464(%%rbx), %%xmm5;"NOP(NOPCOUNT)
                "movdqa 480(%%rbx), %%xmm6;"NOP(NOPCOUNT)
                "movdqa 496(%%rbx), %%xmm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqa 512(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 528(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 544(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 560(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqa 576(%%rbx), %%xmm4;"NOP(NOPCOUNT)
                "movdqa 592(%%rbx), %%xmm5;"NOP(NOPCOUNT)
                "movdqa 608(%%rbx), %%xmm6;"NOP(NOPCOUNT)
                "movdqa 624(%%rbx), %%xmm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqa 640(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 656(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 672(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 688(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqa 704(%%rbx), %%xmm4;"NOP(NOPCOUNT)
                "movdqa 720(%%rbx), %%xmm5;"NOP(NOPCOUNT)
                "movdqa 736(%%rbx), %%xmm6;"NOP(NOPCOUNT)
                "movdqa 752(%%rbx), %%xmm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqa 768(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 784(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 800(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 816(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqa 832(%%rbx), %%xmm4;"NOP(NOPCOUNT)
                "movdqa 848(%%rbx), %%xmm5;"NOP(NOPCOUNT)
                "movdqa 864(%%rbx), %%xmm6;"NOP(NOPCOUNT)
                "movdqa 880(%%rbx), %%xmm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqa 896(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqa 912(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqa 928(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqa 944(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqa 960(%%rbx), %%xmm4;"NOP(NOPCOUNT)
                "movdqa 976(%%rbx), %%xmm5;"NOP(NOPCOUNT)
                "movdqa 992(%%rbx), %%xmm6;"NOP(NOPCOUNT)
                "movdqa 1008(%%rbx), %%xmm7;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_1(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_2(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_3(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_4(movdqa,%%rbx,%%xmm4)NOP(NOPCOUNT)
                READ_ACCESS_5(movdqa,%%rbx,%%xmm5)NOP(NOPCOUNT)
                READ_ACCESS_6(movdqa,%%rbx,%%xmm6)NOP(NOPCOUNT)
                READ_ACCESS_7(movdqa,%%rbx,%%xmm7)NOP(NOPCOUNT)
                READ_ACCESS_8(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_9(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_10(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_11(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_12(movdqa,%%rbx,%%xmm4)NOP(NOPCOUNT)
                READ_ACCESS_13(movdqa,%%rbx,%%xmm5)NOP(NOPCOUNT)
                READ_ACCESS_14(movdqa,%%rbx,%%xmm6)NOP(NOPCOUNT)
                READ_ACCESS_15(movdqa,%%rbx,%%xmm7)NOP(NOPCOUNT)
                READ_ACCESS_16(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_17(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_18(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_19(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_20(movdqa,%%rbx,%%xmm4)NOP(NOPCOUNT)
                READ_ACCESS_21(movdqa,%%rbx,%%xmm5)NOP(NOPCOUNT)
                READ_ACCESS_22(movdqa,%%rbx,%%xmm6)NOP(NOPCOUNT)
                READ_ACCESS_23(movdqa,%%rbx,%%xmm7)NOP(NOPCOUNT)
                READ_ACCESS_24(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_25(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_26(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_27(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_28(movdqa,%%rbx,%%xmm4)NOP(NOPCOUNT)
                READ_ACCESS_29(movdqa,%%rbx,%%xmm5)NOP(NOPCOUNT)
                READ_ACCESS_30(movdqa,%%rbx,%%xmm6)NOP(NOPCOUNT)
                READ_ACCESS_31(movdqa,%%rbx,%%xmm7)NOP(NOPCOUNT)
                READ_ACCESS_32(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_33(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_34(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_35(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_36(movdqa,%%rbx,%%xmm4)NOP(NOPCOUNT)
                READ_ACCESS_37(movdqa,%%rbx,%%xmm5)NOP(NOPCOUNT)
                READ_ACCESS_38(movdqa,%%rbx,%%xmm6)NOP(NOPCOUNT)
                READ_ACCESS_39(movdqa,%%rbx,%%xmm7)NOP(NOPCOUNT)
                READ_ACCESS_40(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_41(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_42(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_43(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_44(movdqa,%%rbx,%%xmm4)NOP(NOPCOUNT)
                READ_ACCESS_45(movdqa,%%rbx,%%xmm5)NOP(NOPCOUNT)
                READ_ACCESS_46(movdqa,%%rbx,%%xmm6)NOP(NOPCOUNT)
                READ_ACCESS_47(movdqa,%%rbx,%%xmm7)NOP(NOPCOUNT)
                READ_ACCESS_48(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_49(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_50(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_51(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_52(movdqa,%%rbx,%%xmm4)NOP(NOPCOUNT)
                READ_ACCESS_53(movdqa,%%rbx,%%xmm5)NOP(NOPCOUNT)
                READ_ACCESS_54(movdqa,%%rbx,%%xmm6)NOP(NOPCOUNT)
                READ_ACCESS_55(movdqa,%%rbx,%%xmm7)NOP(NOPCOUNT)
                READ_ACCESS_56(movdqa,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_57(movdqa,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_58(movdqa,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_59(movdqa,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_60(movdqa,%%rbx,%%xmm4)NOP(NOPCOUNT)
                READ_ACCESS_61(movdqa,%%rbx,%%xmm5)NOP(NOPCOUNT)
                READ_ACCESS_62(movdqa,%%rbx,%%xmm6)NOP(NOPCOUNT)
                READ_ACCESS_63(movdqa,%%rbx,%%xmm7)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "vmovdqa 0(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 32(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqa 64(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 96(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqa 128(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 160(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqa 192(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 224(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqa 256(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 288(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqa 320(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 352(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqa 384(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 416(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqa 448(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 480(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqa 512(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 544(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqa 576(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 608(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqa 640(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 672(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqa 704(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 736(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqa 768(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 800(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqa 832(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 864(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqa 896(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 928(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqa 960(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 992(%%rbx), %%ymm0;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_1(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_2(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_3(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_4(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_5(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_6(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_7(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_8(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_9(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_10(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_11(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_12(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_13(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_14(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_15(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_16(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_17(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_18(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_19(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_20(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_21(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_22(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_23(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_24(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_25(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_26(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_27(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_28(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_29(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_30(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_31(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "vmovdqa 0(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 32(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqa 64(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 96(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqa 128(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 160(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqa 192(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 224(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqa 256(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 288(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqa 320(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 352(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqa 384(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 416(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqa 448(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 480(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqa 512(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 544(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqa 576(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 608(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqa 640(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 672(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqa 704(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 736(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqa 768(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 800(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqa 832(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 864(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqa 896(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 928(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqa 960(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 992(%%rbx), %%ymm1;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_1(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_2(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_3(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_4(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_5(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_6(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_7(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_8(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_9(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_10(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_11(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_12(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_13(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_14(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_15(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_16(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_17(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_18(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_19(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_20(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_21(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_22(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_23(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_24(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_25(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_26(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_27(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_28(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_29(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_30(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_31(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "vmovdqa 0(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 32(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqa 64(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqa 96(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqa 128(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                "vmovdqa 160(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqa 192(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 224(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqa 256(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqa 288(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqa 320(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                "vmovdqa 352(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqa 384(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 416(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqa 448(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqa 480(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqa 512(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                "vmovdqa 544(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqa 576(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 608(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqa 640(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqa 672(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqa 704(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                "vmovdqa 736(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqa 768(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 800(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqa 832(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqa 864(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqa 896(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                "vmovdqa 928(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqa 960(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 992(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,rbx)
                "vmovdqa 1024(%%rbx), %%ymm2;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_1(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_2(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_3(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_4(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_5(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_6(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_7(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_8(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_9(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_10(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_11(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_12(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_13(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_14(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_15(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_16(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_17(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_18(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_19(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_20(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_21(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_22(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_23(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_24(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_25(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_26(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_27(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_28(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_29(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_30(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_31(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_32(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "vmovdqa 0(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 32(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqa 64(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqa 96(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqa 128(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 160(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqa 192(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqa 224(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqa 256(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 288(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqa 320(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqa 352(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqa 384(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 416(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqa 448(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqa 480(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqa 512(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 544(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqa 576(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqa 608(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqa 640(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 672(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqa 704(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqa 736(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqa 768(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 800(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqa 832(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqa 864(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqa 896(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 928(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqa 960(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqa 992(%%rbx), %%ymm3;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_1(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_2(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_3(vmovdqa,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_4(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_5(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_6(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_7(vmovdqa,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_8(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_9(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_10(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_11(vmovdqa,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_12(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_13(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_14(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_15(vmovdqa,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_16(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_17(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_18(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_19(vmovdqa,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_20(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_21(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_22(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_23(vmovdqa,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_24(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_25(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_26(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_27(vmovdqa,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_28(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_29(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_30(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_31(vmovdqa,%%rbx,%%ymm3)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "vmovdqa 0(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 32(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqa 64(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqa 96(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqa 128(%%rbx), %%ymm4;"NOP(NOPCOUNT)
                "vmovdqa 160(%%rbx), %%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqa 192(%%rbx), %%ymm6;"NOP(NOPCOUNT)
                "vmovdqa 224(%%rbx), %%ymm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqa 256(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 288(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqa 320(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqa 352(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqa 384(%%rbx), %%ymm4;"NOP(NOPCOUNT)
                "vmovdqa 416(%%rbx), %%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqa 448(%%rbx), %%ymm6;"NOP(NOPCOUNT)
                "vmovdqa 480(%%rbx), %%ymm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqa 512(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 544(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqa 576(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqa 608(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqa 640(%%rbx), %%ymm4;"NOP(NOPCOUNT)
                "vmovdqa 672(%%rbx), %%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqa 704(%%rbx), %%ymm6;"NOP(NOPCOUNT)
                "vmovdqa 736(%%rbx), %%ymm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqa 768(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqa 800(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqa 832(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqa 864(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqa 896(%%rbx), %%ymm4;"NOP(NOPCOUNT)
                "vmovdqa 928(%%rbx), %%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqa 960(%%rbx), %%ymm6;"NOP(NOPCOUNT)
                "vmovdqa 992(%%rbx), %%ymm7;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_1(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_2(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_3(vmovdqa,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_4(vmovdqa,%%rbx,%%ymm4)NOP(NOPCOUNT)
                READ_ACCESS_5(vmovdqa,%%rbx,%%ymm5)NOP(NOPCOUNT)
                READ_ACCESS_6(vmovdqa,%%rbx,%%ymm6)NOP(NOPCOUNT)
                READ_ACCESS_7(vmovdqa,%%rbx,%%ymm7)NOP(NOPCOUNT)
                READ_ACCESS_8(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_9(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_10(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_11(vmovdqa,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_12(vmovdqa,%%rbx,%%ymm4)NOP(NOPCOUNT)
                READ_ACCESS_13(vmovdqa,%%rbx,%%ymm5)NOP(NOPCOUNT)
                READ_ACCESS_14(vmovdqa,%%rbx,%%ymm6)NOP(NOPCOUNT)
                READ_ACCESS_15(vmovdqa,%%rbx,%%ymm7)NOP(NOPCOUNT)
                READ_ACCESS_16(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_17(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_18(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_19(vmovdqa,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_20(vmovdqa,%%rbx,%%ymm4)NOP(NOPCOUNT)
                READ_ACCESS_21(vmovdqa,%%rbx,%%ymm5)NOP(NOPCOUNT)
                READ_ACCESS_22(vmovdqa,%%rbx,%%ymm6)NOP(NOPCOUNT)
                READ_ACCESS_23(vmovdqa,%%rbx,%%ymm7)NOP(NOPCOUNT)
                READ_ACCESS_24(vmovdqa,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_25(vmovdqa,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_26(vmovdqa,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_27(vmovdqa,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_28(vmovdqa,%%rbx,%%ymm4)NOP(NOPCOUNT)
                READ_ACCESS_29(vmovdqa,%%rbx,%%ymm5)NOP(NOPCOUNT)
                READ_ACCESS_30(vmovdqa,%%rbx,%%ymm6)NOP(NOPCOUNT)
                READ_ACCESS_31(vmovdqa,%%rbx,%%ymm7)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "movdqu 0(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 16(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 32(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 48(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqu 64(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 80(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 96(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 112(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqu 128(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 144(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 160(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 176(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqu 192(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 208(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 224(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 240(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqu 256(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 272(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 288(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 304(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqu 320(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 336(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 352(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 368(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqu 384(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 400(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 416(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 432(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqu 448(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 464(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 480(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 496(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqu 512(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 528(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 544(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 560(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqu 576(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 592(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 608(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 624(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqu 640(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 656(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 672(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 688(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqu 704(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 720(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 736(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 752(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqu 768(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 784(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 800(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 816(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqu 832(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 848(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 864(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 880(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqu 896(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 912(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 928(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 944(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqu 960(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 976(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 992(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 1008(%%rbx), %%xmm0;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_1(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_2(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_3(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_4(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_5(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_6(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_7(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_8(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_9(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_10(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_11(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_12(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_13(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_14(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_15(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_16(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_17(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_18(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_19(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_20(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_21(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_22(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_23(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_24(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_25(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_26(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_27(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_28(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_29(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_30(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_31(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_32(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_33(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_34(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_35(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_36(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_37(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_38(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_39(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_40(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_41(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_42(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_43(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_44(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_45(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_46(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_47(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_48(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_49(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_50(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_51(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_52(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_53(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_54(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_55(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_56(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_57(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_58(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_59(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_60(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_61(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_62(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_63(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "movdqu 0(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 16(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 32(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 48(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqu 64(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 80(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 96(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 112(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqu 128(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 144(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 160(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 176(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqu 192(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 208(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 224(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 240(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqu 256(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 272(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 288(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 304(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqu 320(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 336(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 352(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 368(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqu 384(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 400(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 416(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 432(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqu 448(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 464(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 480(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 496(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqu 512(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 528(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 544(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 560(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqu 576(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 592(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 608(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 624(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqu 640(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 656(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 672(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 688(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqu 704(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 720(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 736(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 752(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqu 768(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 784(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 800(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 816(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqu 832(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 848(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 864(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 880(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqu 896(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 912(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 928(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 944(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqu 960(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 976(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 992(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 1008(%%rbx), %%xmm1;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_1(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_2(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_3(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_4(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_5(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_6(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_7(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_8(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_9(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_10(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_11(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_12(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_13(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_14(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_15(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_16(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_17(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_18(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_19(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_20(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_21(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_22(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_23(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_24(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_25(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_26(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_27(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_28(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_29(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_30(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_31(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_32(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_33(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_34(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_35(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_36(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_37(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_38(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_39(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_40(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_41(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_42(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_43(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_44(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_45(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_46(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_47(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_48(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_49(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_50(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_51(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_52(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_53(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_54(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_55(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_56(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_57(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_58(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_59(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_60(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_61(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_62(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_63(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "movdqu 0(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 16(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 32(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 48(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqu 64(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 80(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 96(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 112(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqu 128(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 144(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 160(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 176(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqu 192(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 208(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 224(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 240(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqu 256(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 272(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 288(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 304(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqu 320(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 336(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 352(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 368(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqu 384(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 400(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 416(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 432(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqu 448(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 464(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 480(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 496(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqu 512(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 528(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 544(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 560(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqu 576(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 592(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 608(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 624(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqu 640(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 656(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 672(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 688(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqu 704(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 720(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 736(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 752(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqu 768(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 784(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 800(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 816(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqu 832(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 848(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 864(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 880(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqu 896(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 912(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 928(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 944(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqu 960(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 976(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 992(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 1008(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,rbx)
                "movdqu 1024(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 1040(%%rbx), %%xmm2;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_1(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_2(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_3(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_4(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_5(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_6(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_7(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_8(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_9(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_10(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_11(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_12(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_13(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_14(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_15(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_16(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_17(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_18(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_19(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_20(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_21(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_22(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_23(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_24(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_25(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_26(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_27(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_28(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_29(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_30(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_31(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_32(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_33(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_34(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_35(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_36(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_37(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_38(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_39(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_40(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_41(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_42(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_43(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_44(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_45(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_46(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_47(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_48(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_49(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_50(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_51(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_52(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_53(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_54(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_55(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_56(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_57(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_58(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_59(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_60(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_61(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_62(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_63(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_64(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_65(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "movdqu 0(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 16(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 32(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 48(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqu 64(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 80(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 96(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 112(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqu 128(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 144(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 160(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 176(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqu 192(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 208(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 224(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 240(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqu 256(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 272(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 288(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 304(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqu 320(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 336(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 352(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 368(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqu 384(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 400(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 416(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 432(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqu 448(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 464(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 480(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 496(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqu 512(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 528(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 544(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 560(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqu 576(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 592(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 608(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 624(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqu 640(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 656(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 672(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 688(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqu 704(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 720(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 736(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 752(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqu 768(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 784(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 800(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 816(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqu 832(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 848(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 864(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 880(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqu 896(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 912(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 928(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 944(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqu 960(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 976(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 992(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 1008(%%rbx), %%xmm3;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_1(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_2(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_3(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_4(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_5(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_6(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_7(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_8(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_9(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_10(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_11(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_12(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_13(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_14(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_15(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_16(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_17(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_18(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_19(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_20(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_21(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_22(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_23(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_24(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_25(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_26(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_27(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_28(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_29(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_30(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_31(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_32(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_33(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_34(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_35(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_36(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_37(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_38(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_39(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_40(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_41(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_42(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_43(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_44(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_45(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_46(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_47(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_48(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_49(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_50(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_51(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_52(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_53(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_54(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_55(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_56(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_57(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_58(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_59(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_60(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_61(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_62(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_63(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "movdqu 0(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 16(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 32(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 48(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "movdqu 64(%%rbx), %%xmm4;"NOP(NOPCOUNT)
                "movdqu 80(%%rbx), %%xmm5;"NOP(NOPCOUNT)
                "movdqu 96(%%rbx), %%xmm6;"NOP(NOPCOUNT)
                "movdqu 112(%%rbx), %%xmm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "movdqu 128(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 144(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 160(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 176(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "movdqu 192(%%rbx), %%xmm4;"NOP(NOPCOUNT)
                "movdqu 208(%%rbx), %%xmm5;"NOP(NOPCOUNT)
                "movdqu 224(%%rbx), %%xmm6;"NOP(NOPCOUNT)
                "movdqu 240(%%rbx), %%xmm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "movdqu 256(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 272(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 288(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 304(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "movdqu 320(%%rbx), %%xmm4;"NOP(NOPCOUNT)
                "movdqu 336(%%rbx), %%xmm5;"NOP(NOPCOUNT)
                "movdqu 352(%%rbx), %%xmm6;"NOP(NOPCOUNT)
                "movdqu 368(%%rbx), %%xmm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "movdqu 384(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 400(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 416(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 432(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "movdqu 448(%%rbx), %%xmm4;"NOP(NOPCOUNT)
                "movdqu 464(%%rbx), %%xmm5;"NOP(NOPCOUNT)
                "movdqu 480(%%rbx), %%xmm6;"NOP(NOPCOUNT)
                "movdqu 496(%%rbx), %%xmm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "movdqu 512(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 528(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 544(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 560(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "movdqu 576(%%rbx), %%xmm4;"NOP(NOPCOUNT)
                "movdqu 592(%%rbx), %%xmm5;"NOP(NOPCOUNT)
                "movdqu 608(%%rbx), %%xmm6;"NOP(NOPCOUNT)
                "movdqu 624(%%rbx), %%xmm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "movdqu 640(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 656(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 672(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 688(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "movdqu 704(%%rbx), %%xmm4;"NOP(NOPCOUNT)
                "movdqu 720(%%rbx), %%xmm5;"NOP(NOPCOUNT)
                "movdqu 736(%%rbx), %%xmm6;"NOP(NOPCOUNT)
                "movdqu 752(%%rbx), %%xmm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "movdqu 768(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 784(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 800(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 816(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "movdqu 832(%%rbx), %%xmm4;"NOP(NOPCOUNT)
                "movdqu 848(%%rbx), %%xmm5;"NOP(NOPCOUNT)
                "movdqu 864(%%rbx), %%xmm6;"NOP(NOPCOUNT)
                "movdqu 880(%%rbx), %%xmm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "movdqu 896(%%rbx), %%xmm0;"NOP(NOPCOUNT)
                "movdqu 912(%%rbx), %%xmm1;"NOP(NOPCOUNT)
                "movdqu 928(%%rbx), %%xmm2;"NOP(NOPCOUNT)
                "movdqu 944(%%rbx), %%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "movdqu 960(%%rbx), %%xmm4;"NOP(NOPCOUNT)
                "movdqu 976(%%rbx), %%xmm5;"NOP(NOPCOUNT)
                "movdqu 992(%%rbx), %%xmm6;"NOP(NOPCOUNT)
                "movdqu 1008(%%rbx), %%xmm7;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_1(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_2(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_3(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_4(movdqu,%%rbx,%%xmm4)NOP(NOPCOUNT)
                READ_ACCESS_5(movdqu,%%rbx,%%xmm5)NOP(NOPCOUNT)
                READ_ACCESS_6(movdqu,%%rbx,%%xmm6)NOP(NOPCOUNT)
                READ_ACCESS_7(movdqu,%%rbx,%%xmm7)NOP(NOPCOUNT)
                READ_ACCESS_8(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_9(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_10(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_11(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_12(movdqu,%%rbx,%%xmm4)NOP(NOPCOUNT)
                READ_ACCESS_13(movdqu,%%rbx,%%xmm5)NOP(NOPCOUNT)
                READ_ACCESS_14(movdqu,%%rbx,%%xmm6)NOP(NOPCOUNT)
                READ_ACCESS_15(movdqu,%%rbx,%%xmm7)NOP(NOPCOUNT)
                READ_ACCESS_16(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_17(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_18(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_19(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_20(movdqu,%%rbx,%%xmm4)NOP(NOPCOUNT)
                READ_ACCESS_21(movdqu,%%rbx,%%xmm5)NOP(NOPCOUNT)
                READ_ACCESS_22(movdqu,%%rbx,%%xmm6)NOP(NOPCOUNT)
                READ_ACCESS_23(movdqu,%%rbx,%%xmm7)NOP(NOPCOUNT)
                READ_ACCESS_24(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_25(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_26(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_27(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_28(movdqu,%%rbx,%%xmm4)NOP(NOPCOUNT)
                READ_ACCESS_29(movdqu,%%rbx,%%xmm5)NOP(NOPCOUNT)
                READ_ACCESS_30(movdqu,%%rbx,%%xmm6)NOP(NOPCOUNT)
                READ_ACCESS_31(movdqu,%%rbx,%%xmm7)NOP(NOPCOUNT)
                READ_ACCESS_32(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_33(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_34(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_35(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_36(movdqu,%%rbx,%%xmm4)NOP(NOPCOUNT)
                READ_ACCESS_37(movdqu,%%rbx,%%xmm5)NOP(NOPCOUNT)
                READ_ACCESS_38(movdqu,%%rbx,%%xmm6)NOP(NOPCOUNT)
                READ_ACCESS_39(movdqu,%%rbx,%%xmm7)NOP(NOPCOUNT)
                READ_ACCESS_40(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_41(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_42(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_43(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_44(movdqu,%%rbx,%%xmm4)NOP(NOPCOUNT)
                READ_ACCESS_45(movdqu,%%rbx,%%xmm5)NOP(NOPCOUNT)
                READ_ACCESS_46(movdqu,%%rbx,%%xmm6)NOP(NOPCOUNT)
                READ_ACCESS_47(movdqu,%%rbx,%%xmm7)NOP(NOPCOUNT)
                READ_ACCESS_48(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_49(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_50(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_51(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_52(movdqu,%%rbx,%%xmm4)NOP(NOPCOUNT)
                READ_ACCESS_53(movdqu,%%rbx,%%xmm5)NOP(NOPCOUNT)
                READ_ACCESS_54(movdqu,%%rbx,%%xmm6)NOP(NOPCOUNT)
                READ_ACCESS_55(movdqu,%%rbx,%%xmm7)NOP(NOPCOUNT)
                READ_ACCESS_56(movdqu,%%rbx,%%xmm0)NOP(NOPCOUNT)
                READ_ACCESS_57(movdqu,%%rbx,%%xmm1)NOP(NOPCOUNT)
                READ_ACCESS_58(movdqu,%%rbx,%%xmm2)NOP(NOPCOUNT)
                READ_ACCESS_59(movdqu,%%rbx,%%xmm3)NOP(NOPCOUNT)
                READ_ACCESS_60(movdqu,%%rbx,%%xmm4)NOP(NOPCOUNT)
                READ_ACCESS_61(movdqu,%%rbx,%%xmm5)NOP(NOPCOUNT)
                READ_ACCESS_62(movdqu,%%rbx,%%xmm6)NOP(NOPCOUNT)
                READ_ACCESS_63(movdqu,%%rbx,%%xmm7)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "vmovdqu 0(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 32(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqu 64(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 96(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqu 128(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 160(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqu 192(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 224(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqu 256(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 288(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqu 320(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 352(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqu 384(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 416(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqu 448(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 480(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqu 512(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 544(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqu 576(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 608(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqu 640(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 672(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqu 704(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 736(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqu 768(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 800(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqu 832(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 864(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqu 896(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 928(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqu 960(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 992(%%rbx), %%ymm0;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_1(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_2(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_3(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_4(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_5(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_6(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_7(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_8(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_9(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_10(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_11(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_12(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_13(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_14(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_15(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_16(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_17(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_18(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_19(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_20(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_21(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_22(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_23(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_24(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_25(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_26(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_27(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_28(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_29(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_30(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_31(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "vmovdqu 0(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 32(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqu 64(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 96(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqu 128(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 160(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqu 192(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 224(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqu 256(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 288(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqu 320(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 352(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqu 384(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 416(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqu 448(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 480(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqu 512(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 544(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqu 576(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 608(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqu 640(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 672(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqu 704(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 736(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqu 768(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 800(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqu 832(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 864(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqu 896(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 928(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqu 960(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 992(%%rbx), %%ymm1;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_1(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_2(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_3(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_4(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_5(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_6(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_7(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_8(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_9(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_10(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_11(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_12(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_13(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_14(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_15(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_16(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_17(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_18(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_19(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_20(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_21(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_22(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_23(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_24(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_25(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_26(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_27(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_28(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_29(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_30(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_31(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "vmovdqu 0(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 32(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqu 64(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqu 96(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqu 128(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                "vmovdqu 160(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqu 192(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 224(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqu 256(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqu 288(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqu 320(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                "vmovdqu 352(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqu 384(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 416(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqu 448(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqu 480(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqu 512(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                "vmovdqu 544(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqu 576(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 608(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqu 640(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqu 672(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqu 704(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                "vmovdqu 736(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqu 768(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 800(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqu 832(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqu 864(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqu 896(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                "vmovdqu 928(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqu 960(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 992(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,rbx)
                "vmovdqu 1024(%%rbx), %%ymm2;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_1(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_2(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_3(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_4(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_5(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_6(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_7(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_8(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_9(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_10(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_11(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_12(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_13(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_14(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_15(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_16(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_17(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_18(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_19(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_20(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_21(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_22(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_23(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_24(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_25(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_26(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_27(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_28(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_29(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_30(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_31(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_32(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "vmovdqu 0(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 32(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqu 64(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqu 96(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqu 128(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 160(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqu 192(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqu 224(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqu 256(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 288(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqu 320(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqu 352(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqu 384(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 416(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqu 448(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqu 480(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqu 512(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 544(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqu 576(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqu 608(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqu 640(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 672(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqu 704(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqu 736(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqu 768(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 800(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqu 832(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqu 864(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqu 896(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 928(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqu 960(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqu 992(%%rbx), %%ymm3;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_1(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_2(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_3(vmovdqu,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_4(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_5(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_6(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_7(vmovdqu,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_8(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_9(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_10(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_11(vmovdqu,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_12(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_13(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_14(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_15(vmovdqu,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_16(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_17(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_18(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_19(vmovdqu,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_20(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_21(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_22(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_23(vmovdqu,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_24(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_25(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_26(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_27(vmovdqu,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_28(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_29(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_30(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_31(vmovdqu,%%rbx,%%ymm3)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "vmovdqu 0(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 32(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "vmovdqu 64(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqu 96(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "vmovdqu 128(%%rbx), %%ymm4;"NOP(NOPCOUNT)
                "vmovdqu 160(%%rbx), %%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "vmovdqu 192(%%rbx), %%ymm6;"NOP(NOPCOUNT)
                "vmovdqu 224(%%rbx), %%ymm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "vmovdqu 256(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 288(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "vmovdqu 320(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqu 352(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "vmovdqu 384(%%rbx), %%ymm4;"NOP(NOPCOUNT)
                "vmovdqu 416(%%rbx), %%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "vmovdqu 448(%%rbx), %%ymm6;"NOP(NOPCOUNT)
                "vmovdqu 480(%%rbx), %%ymm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "vmovdqu 512(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 544(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "vmovdqu 576(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqu 608(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "vmovdqu 640(%%rbx), %%ymm4;"NOP(NOPCOUNT)
                "vmovdqu 672(%%rbx), %%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "vmovdqu 704(%%rbx), %%ymm6;"NOP(NOPCOUNT)
                "vmovdqu 736(%%rbx), %%ymm7;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "vmovdqu 768(%%rbx), %%ymm0;"NOP(NOPCOUNT)
                "vmovdqu 800(%%rbx), %%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "vmovdqu 832(%%rbx), %%ymm2;"NOP(NOPCOUNT)
                "vmovdqu 864(%%rbx), %%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "vmovdqu 896(%%rbx), %%ymm4;"NOP(NOPCOUNT)
                "vmovdqu 928(%%rbx), %%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "vmovdqu 960(%%rbx), %%ymm6;"NOP(NOPCOUNT)
                "vmovdqu 992(%%rbx), %%ymm7;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_1(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_2(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_3(vmovdqu,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_4(vmovdqu,%%rbx,%%ymm4)NOP(NOPCOUNT)
                READ_ACCESS_5(vmovdqu,%%rbx,%%ymm5)NOP(NOPCOUNT)
                READ_ACCESS_6(vmovdqu,%%rbx,%%ymm6)NOP(NOPCOUNT)
                READ_ACCESS_7(vmovdqu,%%rbx,%%ymm7)NOP(NOPCOUNT)
                READ_ACCESS_8(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_9(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_10(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_11(vmovdqu,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_12(vmovdqu,%%rbx,%%ymm4)NOP(NOPCOUNT)
                READ_ACCESS_13(vmovdqu,%%rbx,%%ymm5)NOP(NOPCOUNT)
                READ_ACCESS_14(vmovdqu,%%rbx,%%ymm6)NOP(NOPCOUNT)
                READ_ACCESS_15(vmovdqu,%%rbx,%%ymm7)NOP(NOPCOUNT)
                READ_ACCESS_16(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_17(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_18(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_19(vmovdqu,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_20(vmovdqu,%%rbx,%%ymm4)NOP(NOPCOUNT)
                READ_ACCESS_21(vmovdqu,%%rbx,%%ymm5)NOP(NOPCOUNT)
                READ_ACCESS_22(vmovdqu,%%rbx,%%ymm6)NOP(NOPCOUNT)
                READ_ACCESS_23(vmovdqu,%%rbx,%%ymm7)NOP(NOPCOUNT)
                READ_ACCESS_24(vmovdqu,%%rbx,%%ymm0)NOP(NOPCOUNT)
                READ_ACCESS_25(vmovdqu,%%rbx,%%ymm1)NOP(NOPCOUNT)
                READ_ACCESS_26(vmovdqu,%%rbx,%%ymm2)NOP(NOPCOUNT)
                READ_ACCESS_27(vmovdqu,%%rbx,%%ymm3)NOP(NOPCOUNT)
                READ_ACCESS_28(vmovdqu,%%rbx,%%ymm4)NOP(NOPCOUNT)
                READ_ACCESS_29(vmovdqu,%%rbx,%%ymm5)NOP(NOPCOUNT)
                READ_ACCESS_30(vmovdqu,%%rbx,%%ymm6)NOP(NOPCOUNT)
                READ_ACCESS_31(vmovdqu,%%rbx,%%ymm7)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "xmm0", "xmm1", "xmm2", "xmm3", "memory"

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
                "mov 0(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 8(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 16(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 24(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 32(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 40(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 48(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 56(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "mov 64(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 72(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 80(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 88(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 96(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 104(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 112(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 120(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "mov 128(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 136(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 144(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 152(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 160(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 168(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 176(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 184(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "mov 192(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 200(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 208(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 216(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 224(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 232(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 240(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 248(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "mov 256(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 264(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 272(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 280(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 288(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 296(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 304(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 312(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "mov 320(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 328(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 336(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 344(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 352(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 360(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 368(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 376(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "mov 384(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 392(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 400(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 408(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 416(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 424(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 432(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 440(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "mov 448(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 456(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 464(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 472(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 480(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 488(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 496(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 504(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "mov 512(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 520(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 528(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 536(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 544(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 552(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 560(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 568(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "mov 576(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 584(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 592(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 600(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 608(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 616(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 624(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 632(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "mov 640(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 648(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 656(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 664(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 672(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 680(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 688(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 696(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "mov 704(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 712(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 720(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 728(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 736(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 744(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 752(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 760(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "mov 768(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 776(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 784(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 792(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 800(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 808(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 816(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 824(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "mov 832(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 840(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 848(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 856(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 864(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 872(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 880(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 888(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "mov 896(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 904(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 912(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 920(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 928(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 936(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 944(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 952(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "mov 960(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 968(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 976(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 984(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 992(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 1000(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 1008(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 1016(%%rbx), %%r8;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_1(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_2(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_3(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_4(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_5(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_6(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_7(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_8(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_9(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_10(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_11(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_12(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_13(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_14(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_15(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_16(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_17(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_18(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_19(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_20(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_21(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_22(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_23(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_24(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_25(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_26(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_27(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_28(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_29(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_30(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_31(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_32(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_33(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_34(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_35(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_36(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_37(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_38(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_39(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_40(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_41(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_42(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_43(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_44(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_45(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_46(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_47(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_48(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_49(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_50(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_51(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_52(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_53(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_54(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_55(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_56(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_57(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_58(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_59(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_60(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_61(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_62(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_63(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_64(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_65(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_66(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_67(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_68(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_69(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_70(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_71(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_72(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_73(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_74(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_75(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_76(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_77(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_78(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_79(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_80(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_81(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_82(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_83(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_84(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_85(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_86(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_87(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_88(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_89(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_90(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_91(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_92(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_93(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_94(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_95(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_96(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_97(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_98(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_99(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_100(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_101(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_102(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_103(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_104(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_105(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_106(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_107(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_108(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_109(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_110(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_111(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_112(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_113(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_114(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_115(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_116(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_117(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_118(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_119(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_120(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_121(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_122(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_123(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_124(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_125(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_126(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_127(mov,%%rbx,%%r8)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

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
                "mov 0(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 8(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 16(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 24(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 32(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 40(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 48(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 56(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "mov 64(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 72(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 80(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 88(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 96(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 104(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 112(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 120(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "mov 128(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 136(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 144(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 152(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 160(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 168(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 176(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 184(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "mov 192(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 200(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 208(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 216(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 224(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 232(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 240(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 248(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "mov 256(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 264(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 272(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 280(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 288(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 296(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 304(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 312(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "mov 320(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 328(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 336(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 344(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 352(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 360(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 368(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 376(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "mov 384(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 392(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 400(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 408(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 416(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 424(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 432(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 440(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "mov 448(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 456(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 464(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 472(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 480(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 488(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 496(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 504(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "mov 512(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 520(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 528(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 536(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 544(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 552(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 560(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 568(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "mov 576(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 584(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 592(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 600(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 608(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 616(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 624(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 632(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "mov 640(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 648(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 656(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 664(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 672(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 680(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 688(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 696(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "mov 704(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 712(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 720(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 728(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 736(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 744(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 752(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 760(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "mov 768(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 776(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 784(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 792(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 800(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 808(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 816(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 824(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "mov 832(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 840(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 848(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 856(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 864(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 872(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 880(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 888(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "mov 896(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 904(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 912(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 920(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 928(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 936(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 944(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 952(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "mov 960(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 968(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 976(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 984(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 992(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 1000(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 1008(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 1016(%%rbx), %%r9;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_1(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_2(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_3(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_4(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_5(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_6(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_7(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_8(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_9(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_10(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_11(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_12(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_13(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_14(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_15(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_16(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_17(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_18(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_19(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_20(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_21(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_22(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_23(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_24(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_25(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_26(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_27(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_28(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_29(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_30(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_31(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_32(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_33(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_34(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_35(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_36(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_37(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_38(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_39(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_40(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_41(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_42(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_43(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_44(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_45(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_46(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_47(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_48(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_49(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_50(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_51(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_52(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_53(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_54(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_55(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_56(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_57(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_58(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_59(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_60(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_61(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_62(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_63(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_64(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_65(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_66(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_67(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_68(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_69(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_70(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_71(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_72(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_73(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_74(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_75(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_76(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_77(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_78(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_79(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_80(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_81(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_82(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_83(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_84(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_85(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_86(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_87(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_88(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_89(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_90(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_91(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_92(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_93(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_94(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_95(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_96(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_97(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_98(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_99(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_100(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_101(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_102(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_103(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_104(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_105(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_106(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_107(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_108(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_109(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_110(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_111(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_112(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_113(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_114(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_115(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_116(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_117(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_118(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_119(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_120(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_121(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_122(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_123(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_124(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_125(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_126(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_127(mov,%%rbx,%%r9)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

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
                "mov 0(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 8(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 16(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 24(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 32(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 40(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 48(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 56(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "mov 64(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 72(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 80(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 88(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 96(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 104(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 112(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 120(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "mov 128(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 136(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 144(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 152(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 160(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 168(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 176(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 184(%%rbx), %%r10;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "mov 192(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 200(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 208(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 216(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 224(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 232(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 240(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 248(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "mov 256(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 264(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 272(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 280(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 288(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 296(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 304(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 312(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "mov 320(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 328(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 336(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 344(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 352(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 360(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 368(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 376(%%rbx), %%r10;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "mov 384(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 392(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 400(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 408(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 416(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 424(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 432(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 440(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "mov 448(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 456(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 464(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 472(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 480(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 488(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 496(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 504(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "mov 512(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 520(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 528(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 536(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 544(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 552(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 560(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 568(%%rbx), %%r10;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "mov 576(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 584(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 592(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 600(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 608(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 616(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 624(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 632(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "mov 640(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 648(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 656(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 664(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 672(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 680(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 688(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 696(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "mov 704(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 712(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 720(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 728(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 736(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 744(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 752(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 760(%%rbx), %%r10;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "mov 768(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 776(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 784(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 792(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 800(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 808(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 816(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 824(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "mov 832(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 840(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 848(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 856(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 864(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 872(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 880(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 888(%%rbx), %%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "mov 896(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 904(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 912(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 920(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 928(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 936(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 944(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 952(%%rbx), %%r10;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "mov 960(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 968(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 976(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 984(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 992(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 1000(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 1008(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 1016(%%rbx), %%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,rbx)
                "mov 1024(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 1032(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 1040(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 1048(%%rbx), %%r10;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_1(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_2(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_3(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_4(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_5(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_6(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_7(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_8(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_9(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_10(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_11(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_12(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_13(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_14(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_15(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_16(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_17(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_18(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_19(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_20(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_21(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_22(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_23(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_24(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_25(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_26(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_27(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_28(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_29(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_30(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_31(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_32(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_33(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_34(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_35(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_36(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_37(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_38(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_39(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_40(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_41(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_42(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_43(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_44(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_45(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_46(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_47(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_48(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_49(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_50(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_51(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_52(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_53(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_54(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_55(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_56(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_57(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_58(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_59(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_60(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_61(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_62(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_63(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_64(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_65(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_66(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_67(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_68(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_69(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_70(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_71(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_72(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_73(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_74(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_75(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_76(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_77(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_78(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_79(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_80(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_81(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_82(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_83(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_84(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_85(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_86(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_87(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_88(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_89(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_90(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_91(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_92(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_93(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_94(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_95(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_96(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_97(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_98(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_99(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_100(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_101(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_102(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_103(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_104(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_105(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_106(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_107(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_108(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_109(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_110(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_111(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_112(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_113(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_114(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_115(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_116(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_117(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_118(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_119(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_120(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_121(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_122(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_123(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_124(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_125(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_126(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_127(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_128(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_129(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_130(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_131(mov,%%rbx,%%r10)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

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
                "mov 0(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 8(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 16(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 24(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 32(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 40(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 48(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 56(%%rbx), %%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "mov 64(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 72(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 80(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 88(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 96(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 104(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 112(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 120(%%rbx), %%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "mov 128(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 136(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 144(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 152(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 160(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 168(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 176(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 184(%%rbx), %%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "mov 192(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 200(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 208(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 216(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 224(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 232(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 240(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 248(%%rbx), %%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "mov 256(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 264(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 272(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 280(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 288(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 296(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 304(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 312(%%rbx), %%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "mov 320(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 328(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 336(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 344(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 352(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 360(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 368(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 376(%%rbx), %%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "mov 384(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 392(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 400(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 408(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 416(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 424(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 432(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 440(%%rbx), %%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "mov 448(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 456(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 464(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 472(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 480(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 488(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 496(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 504(%%rbx), %%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "mov 512(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 520(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 528(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 536(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 544(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 552(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 560(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 568(%%rbx), %%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "mov 576(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 584(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 592(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 600(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 608(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 616(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 624(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 632(%%rbx), %%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "mov 640(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 648(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 656(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 664(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 672(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 680(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 688(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 696(%%rbx), %%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "mov 704(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 712(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 720(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 728(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 736(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 744(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 752(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 760(%%rbx), %%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "mov 768(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 776(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 784(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 792(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 800(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 808(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 816(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 824(%%rbx), %%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "mov 832(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 840(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 848(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 856(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 864(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 872(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 880(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 888(%%rbx), %%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "mov 896(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 904(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 912(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 920(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 928(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 936(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 944(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 952(%%rbx), %%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "mov 960(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 968(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 976(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 984(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 992(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 1000(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 1008(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 1016(%%rbx), %%r11;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_1(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_2(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_3(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_4(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_5(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_6(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_7(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_8(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_9(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_10(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_11(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_12(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_13(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_14(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_15(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_16(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_17(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_18(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_19(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_20(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_21(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_22(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_23(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_24(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_25(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_26(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_27(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_28(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_29(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_30(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_31(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_32(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_33(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_34(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_35(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_36(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_37(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_38(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_39(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_40(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_41(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_42(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_43(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_44(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_45(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_46(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_47(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_48(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_49(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_50(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_51(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_52(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_53(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_54(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_55(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_56(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_57(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_58(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_59(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_60(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_61(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_62(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_63(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_64(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_65(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_66(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_67(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_68(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_69(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_70(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_71(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_72(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_73(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_74(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_75(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_76(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_77(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_78(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_79(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_80(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_81(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_82(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_83(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_84(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_85(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_86(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_87(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_88(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_89(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_90(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_91(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_92(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_93(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_94(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_95(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_96(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_97(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_98(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_99(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_100(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_101(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_102(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_103(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_104(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_105(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_106(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_107(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_108(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_109(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_110(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_111(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_112(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_113(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_114(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_115(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_116(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_117(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_118(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_119(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_120(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_121(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_122(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_123(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_124(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_125(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_126(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_127(mov,%%rbx,%%r11)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

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
                "mov 0(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 8(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 16(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 24(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 32(%%rbx), %%r12;"NOP(NOPCOUNT)
                "mov 40(%%rbx), %%r13;"NOP(NOPCOUNT)
                "mov 48(%%rbx), %%r14;"NOP(NOPCOUNT)
                "mov 56(%%rbx), %%r15;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rbx)
                "mov 64(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 72(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 80(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 88(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 96(%%rbx), %%r12;"NOP(NOPCOUNT)
                "mov 104(%%rbx), %%r13;"NOP(NOPCOUNT)
                "mov 112(%%rbx), %%r14;"NOP(NOPCOUNT)
                "mov 120(%%rbx), %%r15;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rbx)
                "mov 128(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 136(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 144(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 152(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 160(%%rbx), %%r12;"NOP(NOPCOUNT)
                "mov 168(%%rbx), %%r13;"NOP(NOPCOUNT)
                "mov 176(%%rbx), %%r14;"NOP(NOPCOUNT)
                "mov 184(%%rbx), %%r15;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rbx)
                "mov 192(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 200(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 208(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 216(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 224(%%rbx), %%r12;"NOP(NOPCOUNT)
                "mov 232(%%rbx), %%r13;"NOP(NOPCOUNT)
                "mov 240(%%rbx), %%r14;"NOP(NOPCOUNT)
                "mov 248(%%rbx), %%r15;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rbx)
                "mov 256(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 264(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 272(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 280(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 288(%%rbx), %%r12;"NOP(NOPCOUNT)
                "mov 296(%%rbx), %%r13;"NOP(NOPCOUNT)
                "mov 304(%%rbx), %%r14;"NOP(NOPCOUNT)
                "mov 312(%%rbx), %%r15;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,rbx)
                "mov 320(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 328(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 336(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 344(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 352(%%rbx), %%r12;"NOP(NOPCOUNT)
                "mov 360(%%rbx), %%r13;"NOP(NOPCOUNT)
                "mov 368(%%rbx), %%r14;"NOP(NOPCOUNT)
                "mov 376(%%rbx), %%r15;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,rbx)
                "mov 384(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 392(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 400(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 408(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 416(%%rbx), %%r12;"NOP(NOPCOUNT)
                "mov 424(%%rbx), %%r13;"NOP(NOPCOUNT)
                "mov 432(%%rbx), %%r14;"NOP(NOPCOUNT)
                "mov 440(%%rbx), %%r15;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,rbx)
                "mov 448(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 456(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 464(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 472(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 480(%%rbx), %%r12;"NOP(NOPCOUNT)
                "mov 488(%%rbx), %%r13;"NOP(NOPCOUNT)
                "mov 496(%%rbx), %%r14;"NOP(NOPCOUNT)
                "mov 504(%%rbx), %%r15;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,rbx)
                "mov 512(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 520(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 528(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 536(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 544(%%rbx), %%r12;"NOP(NOPCOUNT)
                "mov 552(%%rbx), %%r13;"NOP(NOPCOUNT)
                "mov 560(%%rbx), %%r14;"NOP(NOPCOUNT)
                "mov 568(%%rbx), %%r15;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,rbx)
                "mov 576(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 584(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 592(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 600(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 608(%%rbx), %%r12;"NOP(NOPCOUNT)
                "mov 616(%%rbx), %%r13;"NOP(NOPCOUNT)
                "mov 624(%%rbx), %%r14;"NOP(NOPCOUNT)
                "mov 632(%%rbx), %%r15;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,rbx)
                "mov 640(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 648(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 656(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 664(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 672(%%rbx), %%r12;"NOP(NOPCOUNT)
                "mov 680(%%rbx), %%r13;"NOP(NOPCOUNT)
                "mov 688(%%rbx), %%r14;"NOP(NOPCOUNT)
                "mov 696(%%rbx), %%r15;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,rbx)
                "mov 704(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 712(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 720(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 728(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 736(%%rbx), %%r12;"NOP(NOPCOUNT)
                "mov 744(%%rbx), %%r13;"NOP(NOPCOUNT)
                "mov 752(%%rbx), %%r14;"NOP(NOPCOUNT)
                "mov 760(%%rbx), %%r15;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,rbx)
                "mov 768(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 776(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 784(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 792(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 800(%%rbx), %%r12;"NOP(NOPCOUNT)
                "mov 808(%%rbx), %%r13;"NOP(NOPCOUNT)
                "mov 816(%%rbx), %%r14;"NOP(NOPCOUNT)
                "mov 824(%%rbx), %%r15;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,rbx)
                "mov 832(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 840(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 848(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 856(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 864(%%rbx), %%r12;"NOP(NOPCOUNT)
                "mov 872(%%rbx), %%r13;"NOP(NOPCOUNT)
                "mov 880(%%rbx), %%r14;"NOP(NOPCOUNT)
                "mov 888(%%rbx), %%r15;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,rbx)
                "mov 896(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 904(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 912(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 920(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 928(%%rbx), %%r12;"NOP(NOPCOUNT)
                "mov 936(%%rbx), %%r13;"NOP(NOPCOUNT)
                "mov 944(%%rbx), %%r14;"NOP(NOPCOUNT)
                "mov 952(%%rbx), %%r15;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,rbx)
                "mov 960(%%rbx), %%r8;"NOP(NOPCOUNT)
                "mov 968(%%rbx), %%r9;"NOP(NOPCOUNT)
                "mov 976(%%rbx), %%r10;"NOP(NOPCOUNT)
                "mov 984(%%rbx), %%r11;"NOP(NOPCOUNT)
                "mov 992(%%rbx), %%r12;"NOP(NOPCOUNT)
                "mov 1000(%%rbx), %%r13;"NOP(NOPCOUNT)
                "mov 1008(%%rbx), %%r14;"NOP(NOPCOUNT)
                "mov 1016(%%rbx), %%r15;"NOP(NOPCOUNT)
#else
                READ_ACCESS_0(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_1(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_2(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_3(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_4(mov,%%rbx,%%r12)NOP(NOPCOUNT)
                READ_ACCESS_5(mov,%%rbx,%%r13)NOP(NOPCOUNT)
                READ_ACCESS_6(mov,%%rbx,%%r14)NOP(NOPCOUNT)
                READ_ACCESS_7(mov,%%rbx,%%r15)NOP(NOPCOUNT)
                READ_ACCESS_8(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_9(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_10(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_11(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_12(mov,%%rbx,%%r12)NOP(NOPCOUNT)
                READ_ACCESS_13(mov,%%rbx,%%r13)NOP(NOPCOUNT)
                READ_ACCESS_14(mov,%%rbx,%%r14)NOP(NOPCOUNT)
                READ_ACCESS_15(mov,%%rbx,%%r15)NOP(NOPCOUNT)
                READ_ACCESS_16(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_17(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_18(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_19(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_20(mov,%%rbx,%%r12)NOP(NOPCOUNT)
                READ_ACCESS_21(mov,%%rbx,%%r13)NOP(NOPCOUNT)
                READ_ACCESS_22(mov,%%rbx,%%r14)NOP(NOPCOUNT)
                READ_ACCESS_23(mov,%%rbx,%%r15)NOP(NOPCOUNT)
                READ_ACCESS_24(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_25(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_26(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_27(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_28(mov,%%rbx,%%r12)NOP(NOPCOUNT)
                READ_ACCESS_29(mov,%%rbx,%%r13)NOP(NOPCOUNT)
                READ_ACCESS_30(mov,%%rbx,%%r14)NOP(NOPCOUNT)
                READ_ACCESS_31(mov,%%rbx,%%r15)NOP(NOPCOUNT)
                READ_ACCESS_32(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_33(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_34(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_35(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_36(mov,%%rbx,%%r12)NOP(NOPCOUNT)
                READ_ACCESS_37(mov,%%rbx,%%r13)NOP(NOPCOUNT)
                READ_ACCESS_38(mov,%%rbx,%%r14)NOP(NOPCOUNT)
                READ_ACCESS_39(mov,%%rbx,%%r15)NOP(NOPCOUNT)
                READ_ACCESS_40(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_41(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_42(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_43(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_44(mov,%%rbx,%%r12)NOP(NOPCOUNT)
                READ_ACCESS_45(mov,%%rbx,%%r13)NOP(NOPCOUNT)
                READ_ACCESS_46(mov,%%rbx,%%r14)NOP(NOPCOUNT)
                READ_ACCESS_47(mov,%%rbx,%%r15)NOP(NOPCOUNT)
                READ_ACCESS_48(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_49(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_50(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_51(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_52(mov,%%rbx,%%r12)NOP(NOPCOUNT)
                READ_ACCESS_53(mov,%%rbx,%%r13)NOP(NOPCOUNT)
                READ_ACCESS_54(mov,%%rbx,%%r14)NOP(NOPCOUNT)
                READ_ACCESS_55(mov,%%rbx,%%r15)NOP(NOPCOUNT)
                READ_ACCESS_56(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_57(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_58(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_59(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_60(mov,%%rbx,%%r12)NOP(NOPCOUNT)
                READ_ACCESS_61(mov,%%rbx,%%r13)NOP(NOPCOUNT)
                READ_ACCESS_62(mov,%%rbx,%%r14)NOP(NOPCOUNT)
                READ_ACCESS_63(mov,%%rbx,%%r15)NOP(NOPCOUNT)
                READ_ACCESS_64(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_65(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_66(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_67(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_68(mov,%%rbx,%%r12)NOP(NOPCOUNT)
                READ_ACCESS_69(mov,%%rbx,%%r13)NOP(NOPCOUNT)
                READ_ACCESS_70(mov,%%rbx,%%r14)NOP(NOPCOUNT)
                READ_ACCESS_71(mov,%%rbx,%%r15)NOP(NOPCOUNT)
                READ_ACCESS_72(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_73(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_74(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_75(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_76(mov,%%rbx,%%r12)NOP(NOPCOUNT)
                READ_ACCESS_77(mov,%%rbx,%%r13)NOP(NOPCOUNT)
                READ_ACCESS_78(mov,%%rbx,%%r14)NOP(NOPCOUNT)
                READ_ACCESS_79(mov,%%rbx,%%r15)NOP(NOPCOUNT)
                READ_ACCESS_80(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_81(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_82(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_83(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_84(mov,%%rbx,%%r12)NOP(NOPCOUNT)
                READ_ACCESS_85(mov,%%rbx,%%r13)NOP(NOPCOUNT)
                READ_ACCESS_86(mov,%%rbx,%%r14)NOP(NOPCOUNT)
                READ_ACCESS_87(mov,%%rbx,%%r15)NOP(NOPCOUNT)
                READ_ACCESS_88(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_89(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_90(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_91(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_92(mov,%%rbx,%%r12)NOP(NOPCOUNT)
                READ_ACCESS_93(mov,%%rbx,%%r13)NOP(NOPCOUNT)
                READ_ACCESS_94(mov,%%rbx,%%r14)NOP(NOPCOUNT)
                READ_ACCESS_95(mov,%%rbx,%%r15)NOP(NOPCOUNT)
                READ_ACCESS_96(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_97(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_98(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_99(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_100(mov,%%rbx,%%r12)NOP(NOPCOUNT)
                READ_ACCESS_101(mov,%%rbx,%%r13)NOP(NOPCOUNT)
                READ_ACCESS_102(mov,%%rbx,%%r14)NOP(NOPCOUNT)
                READ_ACCESS_103(mov,%%rbx,%%r15)NOP(NOPCOUNT)
                READ_ACCESS_104(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_105(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_106(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_107(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_108(mov,%%rbx,%%r12)NOP(NOPCOUNT)
                READ_ACCESS_109(mov,%%rbx,%%r13)NOP(NOPCOUNT)
                READ_ACCESS_110(mov,%%rbx,%%r14)NOP(NOPCOUNT)
                READ_ACCESS_111(mov,%%rbx,%%r15)NOP(NOPCOUNT)
                READ_ACCESS_112(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_113(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_114(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_115(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_116(mov,%%rbx,%%r12)NOP(NOPCOUNT)
                READ_ACCESS_117(mov,%%rbx,%%r13)NOP(NOPCOUNT)
                READ_ACCESS_118(mov,%%rbx,%%r14)NOP(NOPCOUNT)
                READ_ACCESS_119(mov,%%rbx,%%r15)NOP(NOPCOUNT)
                READ_ACCESS_120(mov,%%rbx,%%r8)NOP(NOPCOUNT)
                READ_ACCESS_121(mov,%%rbx,%%r9)NOP(NOPCOUNT)
                READ_ACCESS_122(mov,%%rbx,%%r10)NOP(NOPCOUNT)
                READ_ACCESS_123(mov,%%rbx,%%r11)NOP(NOPCOUNT)
                READ_ACCESS_124(mov,%%rbx,%%r12)NOP(NOPCOUNT)
                READ_ACCESS_125(mov,%%rbx,%%r13)NOP(NOPCOUNT)
                READ_ACCESS_126(mov,%%rbx,%%r14)NOP(NOPCOUNT)
                READ_ACCESS_127(mov,%%rbx,%%r15)NOP(NOPCOUNT)
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
                : "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

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


