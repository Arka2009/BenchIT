/******************************************************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id$
 * For license details see COPYING in the package base directory
 ******************************************************************************************************/
/* Kernel: measures combined bandwidth of one read and one write stream located in different cache levels or memory of certain CPUs.
 ******************************************************************************************************/
 
/*
 * TODO  - check malloc and mmap return values for errors and abort if alocation of buffers fails
 *       - adopt cache and TLB parameters to refer to identifiers returned by 
 *         the hardware detection
 *       - optional global or local alloc of flush buffer
 *       - add manual instrumentation for VampirTracce
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

/* some defines to make code a little more readable */
#define PARAMS ((param_t*)aligned_addr)
#define THREAD_PARAMS ((param_t*)aligned_addr)->thread_params
#define SHARE_CPU_PARAMS ((param_t*)aligned_addr)->share_cpu_params


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
static inline int use_memory(param_t *params)
{
  if (params->use_direction==FIFO)
  {
     if ((params->use_mode_1&(MODE_EXCLUSIVE|MODE_MODIFIED|MODE_INVALID))&&(params->use_mode_2&(MODE_EXCLUSIVE|MODE_MODIFIED|MODE_INVALID))){
      for (params->i=0;params->i<params->memsize/2;params->i+=STRIDE) {
        params->j = params->num_uses; while(params->j--) *((double*)(params->addr_1+params->i))=(double)params->value;
        params->j = params->num_uses; while(params->j--) *((double*)(params->addr_2+params->i))=(double)params->value;
      }
     }
     else if (params->use_mode_1&(MODE_EXCLUSIVE|MODE_MODIFIED|MODE_INVALID)) {
      for (params->i=0;params->i<params->memsize/2;params->i+=STRIDE) {
        params->j = params->num_uses; while(params->j--) *((double*)(params->addr_1+params->i))=(double)params->value;
      }
     }
     else if (params->use_mode_2&(MODE_EXCLUSIVE|MODE_MODIFIED|MODE_INVALID)) {
      for (params->i=0;params->i<params->memsize/2;params->i+=STRIDE) {
        params->j = params->num_uses; while(params->j--) *((double*)(params->addr_2+params->i))=(double)params->value;
      } 
     } /* -> modified */
     params->j = 1;
     if (params->use_mode_1&(MODE_EXCLUSIVE|MODE_INVALID)) while(params->j--) {
      __asm__ __volatile__("mfence;"::: "memory");

      for (params->i=0;params->i<params->memsize/2;params->i+=STRIDE) {
         __asm__ __volatile__("clflush (%%rax);":: "a" (params->addr_1+params->i));     
      }
      __asm__ __volatile__("mfence;"::: "memory");

     }
     params->j = 1;
     if (params->use_mode_2&(MODE_EXCLUSIVE|MODE_INVALID)) while(params->j--) {
      __asm__ __volatile__("mfence;"::: "memory");

      for (params->i=0;params->i<params->memsize/2;params->i+=STRIDE) {
         __asm__ __volatile__("clflush (%%rax);":: "a" (params->addr_2+params->i));       
      }
      __asm__ __volatile__("mfence;"::: "memory");

     } /* -> invalid */
     if ((params->use_mode_1&(MODE_EXCLUSIVE|MODE_SHARED|MODE_OWNED|MODE_FORWARD)) && (params->use_mode_2&(MODE_EXCLUSIVE|MODE_SHARED|MODE_OWNED|MODE_FORWARD))) {
      for (params->i=0;params->i<params->memsize/2;params->i+=STRIDE) {
         params->j = params->num_uses; while(params->j--) params->value= *((double*)(params->addr_1+params->i));
         params->j = params->num_uses; while(params->j--) params->value= *((double*)(params->addr_2+params->i));
      }
     } 
     else if (params->use_mode_1&(MODE_EXCLUSIVE|MODE_SHARED|MODE_OWNED|MODE_FORWARD)) {
      for (params->i=0;params->i<params->memsize/2;params->i+=STRIDE) {
         params->j = params->num_uses; while(params->j--) params->value= *((double*)(params->addr_1+params->i));
         if (params->use_mode_2&MODE_MODIFIED) {params->j = params->num_uses; while(params->j--) params->value= *((double*)(params->addr_2+params->i));}
      }
     }      
     else if (params->use_mode_2&(MODE_EXCLUSIVE|MODE_SHARED|MODE_OWNED|MODE_FORWARD)) {
      for (params->i=0;params->i<params->memsize/2;params->i+=STRIDE) {
         if (params->use_mode_1&MODE_MODIFIED) {params->j = params->num_uses; while(params->j--) params->value= *((double*)(params->addr_1+params->i));}
         params->j = params->num_uses; while(params->j--) params->value= *((double*)(params->addr_2+params->i));
      }            
     }  /* -> exclusive / shared 
         * modified stream is read again which does not change coherency state*/
  }
  else
  {
  if ((params->use_mode_1&(MODE_EXCLUSIVE|MODE_MODIFIED|MODE_INVALID))&&(params->use_mode_2&(MODE_EXCLUSIVE|MODE_MODIFIED|MODE_INVALID))){
      for (params->i=params->memsize/2-STRIDE;params->i>=0;params->i-=STRIDE) {
        params->j = params->num_uses; while(params->j--) *((double*)(params->addr_1+params->i))=(double)params->value;
        params->j = params->num_uses; while(params->j--) *((double*)(params->addr_2+params->i))=(double)params->value;
      }
     }
     else if (params->use_mode_1&(MODE_EXCLUSIVE|MODE_MODIFIED|MODE_INVALID)) {
      for (params->i=params->memsize/2-STRIDE;params->i>=0;params->i-=STRIDE) {
        params->j = params->num_uses; while(params->j--) *((double*)(params->addr_1+params->i))=(double)params->value;
      }
     }
     else if (params->use_mode_2&(MODE_EXCLUSIVE|MODE_MODIFIED|MODE_INVALID)) {
      for (params->i=params->memsize/2-STRIDE;params->i>=0;params->i-=STRIDE) {
        params->j = params->num_uses; while(params->j--) *((double*)(params->addr_2+params->i))=(double)params->value;
      } 
     } /* -> modified */
     params->j = 1;
     if (params->use_mode_1&(MODE_EXCLUSIVE|MODE_INVALID)) while(params->j--) {
      __asm__ __volatile__("mfence;"::: "memory");

      for (params->i=params->memsize/2-STRIDE;params->i>=0;params->i-=STRIDE) {
         __asm__ __volatile__("clflush (%%rax);":: "a" (params->addr_1+params->i));     
      }
      __asm__ __volatile__("mfence;"::: "memory");

     }
     params->j = 1;
     if (params->use_mode_2&(MODE_EXCLUSIVE|MODE_INVALID)) while(params->j--) {
      __asm__ __volatile__("mfence;"::: "memory");

      for (params->i=params->memsize/2-STRIDE;params->i>=0;params->i-=STRIDE) {
         __asm__ __volatile__("clflush (%%rax);":: "a" (params->addr_2+params->i));       
      }
      __asm__ __volatile__("mfence;"::: "memory");

     } /* -> invalid */
     if ((params->use_mode_1&(MODE_EXCLUSIVE|MODE_SHARED|MODE_OWNED|MODE_FORWARD)) && (params->use_mode_2&(MODE_EXCLUSIVE|MODE_SHARED|MODE_OWNED|MODE_FORWARD))) {
      for (params->i=params->memsize/2-STRIDE;params->i>=0;params->i-=STRIDE) {
         params->j = params->num_uses; while(params->j--) params->value= *((double*)(params->addr_1+params->i));
         params->j = params->num_uses; while(params->j--) params->value= *((double*)(params->addr_2+params->i));
      }
     } 
     else if (params->use_mode_1&(MODE_EXCLUSIVE|MODE_SHARED|MODE_OWNED|MODE_FORWARD)) {
      for (params->i=params->memsize/2-STRIDE;params->i>=0;params->i-=STRIDE) {
         params->j = params->num_uses; while(params->j--) params->value= *((double*)(params->addr_1+params->i));
         if (params->use_mode_2&MODE_MODIFIED) {params->j = params->num_uses; while(params->j--) params->value= *((double*)(params->addr_2+params->i));}
      }
     }      
     else if (params->use_mode_2&(MODE_EXCLUSIVE|MODE_SHARED|MODE_OWNED|MODE_FORWARD)) {
      for (params->i=params->memsize/2-STRIDE;params->i>=0;params->i-=STRIDE)       {
         if (params->use_mode_1&MODE_MODIFIED) {params->j = params->num_uses; while(params->j--) params->value= *((double*)(params->addr_1+params->i));}
         params->j = params->num_uses; while(params->j--) params->value= *((double*)(params->addr_2+params->i));
      }            
     }  /* -> exclusive / shared 
         * modified stream is read again which does not change coherency state*/
  }

  return (int) params->value;
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
 * flush caches
 */
static inline void flush_caches(param_t *params)
{
  register unsigned long long tmp=0;

  if ((params->flush_mode==MODE_MODIFIED)||(params->flush_mode==MODE_EXCLUSIVE)||(params->flush_mode==MODE_INVALID))
  { 
   params->j=params->num_flushes;
   while(params->j--)
   {
    for (params->i=0;params->i<params->flushsize;params->i+=STRIDE)
    {
      //tmp=*((unsigned long long*)((unsigned long long)(params->flushaddr)+params->i)); //needed if non-destructive operation is required
      *((unsigned long long*)((unsigned long long)(params->flushaddr)+params->i))=tmp;
    }
   }
  }
  if (params->flush_mode==MODE_EXCLUSIVE) 
  {
      __asm__ __volatile__("mfence;"::: "memory");

    for(params->i = params->flushsize/64;params->i>=0;params->i--)
    {
      __asm__ __volatile__("clflush (%%rax);":: "a" (((unsigned long long)params->flushaddr)+64*params->i));
    }
      __asm__ __volatile__("mfence;"::: "memory");

    params->j=params->num_flushes;
    while(params->j--)
    {
     for (params->i=0;params->i<params->flushsize;params->i+=STRIDE)
     {
       tmp|=*((unsigned long long*)((unsigned long long)(params->flushaddr)+params->i));
     }
     /* store result somewhere to prevent compiler from "optimizations" */
     *((unsigned long long*)((unsigned long long)(params->flushaddr)+params->i))=tmp;
    }
  }
  if (params->flush_mode==MODE_INVALID) 
  {
      __asm__ __volatile__("mfence;"::: "memory");

    for(params->i = params->flushsize/64;params->i>=0;params->i--)
    {
      __asm__ __volatile__("clflush (%%rax);":: "a" (((unsigned long long)params->flushaddr)+64*params->i));
    }
      __asm__ __volatile__("mfence;"::: "memory");

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
                "mov %%rax,%%rbx;"
//                "jmp _work_loop_overhead;"
//                ".align 64,0x0;"
//                "_work_loop_overhead:"
//                "sub $1,%%rcx;"
//                "jnz _work_loop_overhead;"
                SERIALIZE    
                TIMESTAMP
                : "=a" (a), "=b" (b), "=c" (c), "=d" (d)
        );
        if ((a-b)<ret) ret=(a-b);
   }			
  return (int)ret;
}


/** assembler implementation of bandwidth measurement using movapd instruction
 */
static void asm_copy_movapd_1(param_t *params) __attribute__((noinline));
static void asm_copy_movapd_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movapd_1;"
                ".align 64,0x0;"
                "_copy_loop_movapd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,16(%%r12);"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,32(%%r12);"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movapd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,64(%%r12);"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,80(%%r12);"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,96(%%r12);"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movapd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,144(%%r14);"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,160(%%r14);"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movapd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,208(%%r14);"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,224(%%r14);"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movapd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,272(%%r14);"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,288(%%r14);"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movapd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,320(%%r14);"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,336(%%r14);"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,352(%%r14);"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,400(%%r14);"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,416(%%r14);"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movapd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,448(%%r14);"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,464(%%r14);"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,480(%%r14);"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm0,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_movapd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movapd instruction
 */
static void asm_copy_movapd_2(param_t *params) __attribute__((noinline));
static void asm_copy_movapd_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movapd_2;"
                ".align 64,0x0;"
                "_copy_loop_movapd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,0(%%r12);"NOP(NOPCOUNT)"movapd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd 48(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,32(%%r12);"NOP(NOPCOUNT)"movapd %%xmm1,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movapd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd 80(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,64(%%r12);"NOP(NOPCOUNT)"movapd %%xmm1,80(%%r12);"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd 112(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,96(%%r12);"NOP(NOPCOUNT)"movapd %%xmm1,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movapd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,128(%%r14);"NOP(NOPCOUNT)"movapd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 176(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,160(%%r14);"NOP(NOPCOUNT)"movapd %%xmm1,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movapd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,192(%%r14);"NOP(NOPCOUNT)"movapd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 240(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,224(%%r14);"NOP(NOPCOUNT)"movapd %%xmm1,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movapd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,256(%%r14);"NOP(NOPCOUNT)"movapd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 304(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,288(%%r14);"NOP(NOPCOUNT)"movapd %%xmm1,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movapd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 336(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,320(%%r14);"NOP(NOPCOUNT)"movapd %%xmm1,336(%%r14);"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 368(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,352(%%r14);"NOP(NOPCOUNT)"movapd %%xmm1,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,384(%%r14);"NOP(NOPCOUNT)"movapd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 432(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,416(%%r14);"NOP(NOPCOUNT)"movapd %%xmm1,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movapd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 464(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,448(%%r14);"NOP(NOPCOUNT)"movapd %%xmm1,464(%%r14);"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 496(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,480(%%r14);"NOP(NOPCOUNT)"movapd %%xmm1,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_movapd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movapd instruction
 */
static void asm_copy_movapd_3(param_t *params) __attribute__((noinline));
static void asm_copy_movapd_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movapd_3;"
                ".align 64,0x0;"
                "_copy_loop_movapd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movapd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "movapd 48(%%r10),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm0,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movapd %%xmm1,64(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm2,80(%%r12);"NOP(NOPCOUNT)
                "add $528,%%r10;"
                "movapd 96(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 112(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm0,96(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,112(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movapd %%xmm2,128(%%r14);"NOP(NOPCOUNT)
                "add $528,%%r12;"
                "movapd 144(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm0,144(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,160(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,176(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movapd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,224(%%r14);"NOP(NOPCOUNT)
                
                "movapd 240(%%r13),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm0,240(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movapd %%xmm1,256(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,272(%%r14);"NOP(NOPCOUNT)
                
                "movapd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm0,288(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movapd %%xmm2,320(%%r14);"NOP(NOPCOUNT)
                
                "movapd 336(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm0,336(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,352(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movapd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                
                "movapd 432(%%r13),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm0,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movapd %%xmm1,448(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,464(%%r14);"NOP(NOPCOUNT)
                
                "movapd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "movapd 512(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm0,480(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,496(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "movapd %%xmm2,512(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_movapd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movapd instruction
 */
static void asm_copy_movapd_4(param_t *params) __attribute__((noinline));
static void asm_copy_movapd_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movapd_4;"
                ".align 64,0x0;"
                "_copy_loop_movapd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movapd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movapd %%xmm0,64(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm1,80(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm2,96(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm3,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movapd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,160(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movapd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,224(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movapd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,288(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movapd %%xmm0,320(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,336(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,352(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movapd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movapd %%xmm0,448(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,464(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,480(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_movapd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movapd instruction
 */
static void asm_copy_movapd_8(param_t *params) __attribute__((noinline));
static void asm_copy_movapd_8(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movapd_8;"
                ".align 64,0x0;"
                "_copy_loop_movapd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10),%%xmm4;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm5;"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm6;"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "movapd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movapd %%xmm4,64(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm5,80(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm6,96(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm7,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm7;"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,128,r14)
                "movapd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,160(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,176(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movapd %%xmm4,192(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,208(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm6,224(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm7,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r14)
                "movapd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,288(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movapd %%xmm4,320(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,336(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm6,352(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm7,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r14)
                "movapd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movapd %%xmm4,448(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,464(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm6,480(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm7,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_movapd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovapd instruction
 */
static void asm_copy_vmovapd_1(param_t *params) __attribute__((noinline));
static void asm_copy_vmovapd_1(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_vmovapd_1;"
                ".align 64,0x0;"
                "_copy_loop_vmovapd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovapd 32(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "vmovapd 64(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,64(%%r12);"NOP(NOPCOUNT)
                "vmovapd 96(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
                "vmovapd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,128(%%r12);"NOP(NOPCOUNT)
                "vmovapd 160(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
                "vmovapd 192(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,192(%%r12);"NOP(NOPCOUNT)
                "vmovapd 224(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "vmovapd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovapd 288(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "vmovapd 320(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,320(%%r14);"NOP(NOPCOUNT)
                "vmovapd 352(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "vmovapd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovapd 416(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "vmovapd 448(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,448(%%r14);"NOP(NOPCOUNT)
                "vmovapd 480(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
                "vmovapd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovapd 544(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
                "vmovapd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,576(%%r14);"NOP(NOPCOUNT)
                "vmovapd 608(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
                "vmovapd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,640(%%r14);"NOP(NOPCOUNT)
                "vmovapd 672(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
                "vmovapd 704(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,704(%%r14);"NOP(NOPCOUNT)
                "vmovapd 736(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovapd 800(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
                "vmovapd 832(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,832(%%r14);"NOP(NOPCOUNT)
                "vmovapd 864(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
                "vmovapd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,896(%%r14);"NOP(NOPCOUNT)
                "vmovapd 928(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
                "vmovapd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,960(%%r14);"NOP(NOPCOUNT)
                "vmovapd 992(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm0,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_vmovapd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovapd instruction
 */
static void asm_copy_vmovapd_2(param_t *params) __attribute__((noinline));
static void asm_copy_vmovapd_2(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_vmovapd_2;"
                ".align 64,0x0;"
                "_copy_loop_vmovapd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,0(%%r12);"NOP(NOPCOUNT)"vmovapd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "vmovapd 64(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd 96(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,64(%%r12);"NOP(NOPCOUNT)"vmovapd %%ymm1,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
                "vmovapd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd 160(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,128(%%r12);"NOP(NOPCOUNT)"vmovapd %%ymm1,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
                "vmovapd 192(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd 224(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,192(%%r12);"NOP(NOPCOUNT)"vmovapd %%ymm1,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "vmovapd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,256(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "vmovapd 320(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 352(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,320(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm1,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "vmovapd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,384(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "vmovapd 448(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 480(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,448(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm1,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
                "vmovapd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,512(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
                "vmovapd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 608(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,576(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm1,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
                "vmovapd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 672(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,640(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm1,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
                "vmovapd 704(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 736(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,704(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm1,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,768(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
                "vmovapd 832(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 864(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,832(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm1,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
                "vmovapd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 928(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,896(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm1,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
                "vmovapd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 992(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,960(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm1,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_vmovapd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovapd instruction
 */
static void asm_copy_vmovapd_3(param_t *params) __attribute__((noinline));
static void asm_copy_vmovapd_3(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_vmovapd_3;"
                ".align 64,0x0;"
                "_copy_loop_vmovapd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovapd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovapd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovapd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "vmovapd 96(%%r10),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovapd 128(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 160(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovapd %%ymm1,128(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm2,160(%%r12);"NOP(NOPCOUNT)
                "add $1056,%%r10;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "vmovapd 192(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 224(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovapd 256(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "vmovapd %%ymm0,192(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,224(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovapd %%ymm2,256(%%r14);"NOP(NOPCOUNT)
                "add $1056,%%r12;"
                "vmovapd 288(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovapd 320(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 352(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovapd %%ymm1,320(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm2,352(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovapd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovapd 448(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovapd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovapd %%ymm2,448(%%r14);"NOP(NOPCOUNT)
                
                "vmovapd 480(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovapd 512(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 544(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,480(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovapd %%ymm1,512(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm2,544(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovapd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 608(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovapd 640(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovapd %%ymm0,576(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovapd %%ymm2,640(%%r14);"NOP(NOPCOUNT)
                
                "vmovapd 672(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovapd 704(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 736(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovapd %%ymm1,704(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm2,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovapd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovapd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovapd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                
                "vmovapd 864(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovapd 896(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 928(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovapd %%ymm1,896(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm2,928(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovapd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 992(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r13)
                "vmovapd 1024(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovapd %%ymm0,960(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,992(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r14)
                "vmovapd %%ymm2,1024(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_vmovapd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovapd instruction
 */
static void asm_copy_vmovapd_4(param_t *params) __attribute__((noinline));
static void asm_copy_vmovapd_4(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_vmovapd_4;"
                ".align 64,0x0;"
                "_copy_loop_vmovapd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovapd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 96(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovapd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovapd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovapd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 160(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmovapd 192(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 224(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovapd %%ymm0,128(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovapd %%ymm2,192(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovapd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovapd 320(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 352(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovapd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovapd %%ymm2,320(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovapd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovapd 448(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 480(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovapd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovapd %%ymm2,448(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovapd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovapd 576(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 608(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovapd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovapd %%ymm2,576(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovapd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 672(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovapd 704(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 736(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovapd %%ymm0,640(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovapd %%ymm2,704(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovapd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 864(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovapd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovapd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovapd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 928(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovapd 960(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 992(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovapd %%ymm0,896(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovapd %%ymm2,960(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_vmovapd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovapd instruction
 */
static void asm_copy_vmovapd_8(param_t *params) __attribute__((noinline));
static void asm_copy_vmovapd_8(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_vmovapd_8;"
                ".align 64,0x0;"
                "_copy_loop_vmovapd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovapd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 96(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovapd 128(%%r10),%%ymm4;"NOP(NOPCOUNT)
                "vmovapd 160(%%r10),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmovapd 192(%%r10),%%ymm6;"NOP(NOPCOUNT)
                "vmovapd 224(%%r10),%%ymm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovapd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovapd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovapd %%ymm4,128(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovapd %%ymm6,192(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm7,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovapd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovapd 320(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 352(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovapd 384(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovapd 416(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovapd 448(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovapd 480(%%r13),%%ymm7;"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovapd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovapd %%ymm2,320(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,352(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovapd %%ymm4,384(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovapd %%ymm6,448(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm7,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovapd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovapd 576(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 608(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovapd 640(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovapd 672(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovapd 704(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovapd 736(%%r13),%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovapd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovapd %%ymm2,576(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovapd %%ymm4,640(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovapd %%ymm6,704(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm7,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovapd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 864(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovapd 896(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovapd 928(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovapd 960(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovapd 992(%%r13),%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovapd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovapd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovapd %%ymm4,896(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovapd %%ymm6,960(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm7,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_vmovapd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movupd instruction
 */
static void asm_copy_movupd_1(param_t *params) __attribute__((noinline));
static void asm_copy_movupd_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movupd_1;"
                ".align 64,0x0;"
                "_copy_loop_movupd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movupd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movupd 16(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,16(%%r12);"NOP(NOPCOUNT)
                "movupd 32(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,32(%%r12);"NOP(NOPCOUNT)
                "movupd 48(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movupd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,64(%%r12);"NOP(NOPCOUNT)
                "movupd 80(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,80(%%r12);"NOP(NOPCOUNT)
                "movupd 96(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,96(%%r12);"NOP(NOPCOUNT)
                "movupd 112(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movupd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movupd 144(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,144(%%r14);"NOP(NOPCOUNT)
                "movupd 160(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,160(%%r14);"NOP(NOPCOUNT)
                "movupd 176(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movupd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movupd 208(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,208(%%r14);"NOP(NOPCOUNT)
                "movupd 224(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,224(%%r14);"NOP(NOPCOUNT)
                "movupd 240(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movupd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movupd 272(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,272(%%r14);"NOP(NOPCOUNT)
                "movupd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,288(%%r14);"NOP(NOPCOUNT)
                "movupd 304(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movupd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,320(%%r14);"NOP(NOPCOUNT)
                "movupd 336(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,336(%%r14);"NOP(NOPCOUNT)
                "movupd 352(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,352(%%r14);"NOP(NOPCOUNT)
                "movupd 368(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movupd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movupd 400(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,400(%%r14);"NOP(NOPCOUNT)
                "movupd 416(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,416(%%r14);"NOP(NOPCOUNT)
                "movupd 432(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movupd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,448(%%r14);"NOP(NOPCOUNT)
                "movupd 464(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,464(%%r14);"NOP(NOPCOUNT)
                "movupd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,480(%%r14);"NOP(NOPCOUNT)
                "movupd 496(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm0,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_movupd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movupd instruction
 */
static void asm_copy_movupd_2(param_t *params) __attribute__((noinline));
static void asm_copy_movupd_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movupd_2;"
                ".align 64,0x0;"
                "_copy_loop_movupd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movupd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,0(%%r12);"NOP(NOPCOUNT)"movupd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movupd 32(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd 48(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,32(%%r12);"NOP(NOPCOUNT)"movupd %%xmm1,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movupd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd 80(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,64(%%r12);"NOP(NOPCOUNT)"movupd %%xmm1,80(%%r12);"NOP(NOPCOUNT)
                "movupd 96(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd 112(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,96(%%r12);"NOP(NOPCOUNT)"movupd %%xmm1,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movupd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,128(%%r14);"NOP(NOPCOUNT)"movupd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movupd 160(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 176(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,160(%%r14);"NOP(NOPCOUNT)"movupd %%xmm1,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movupd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,192(%%r14);"NOP(NOPCOUNT)"movupd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movupd 224(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 240(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,224(%%r14);"NOP(NOPCOUNT)"movupd %%xmm1,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movupd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,256(%%r14);"NOP(NOPCOUNT)"movupd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movupd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 304(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,288(%%r14);"NOP(NOPCOUNT)"movupd %%xmm1,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movupd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 336(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,320(%%r14);"NOP(NOPCOUNT)"movupd %%xmm1,336(%%r14);"NOP(NOPCOUNT)
                "movupd 352(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 368(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,352(%%r14);"NOP(NOPCOUNT)"movupd %%xmm1,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movupd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,384(%%r14);"NOP(NOPCOUNT)"movupd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movupd 416(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 432(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,416(%%r14);"NOP(NOPCOUNT)"movupd %%xmm1,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movupd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 464(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,448(%%r14);"NOP(NOPCOUNT)"movupd %%xmm1,464(%%r14);"NOP(NOPCOUNT)
                "movupd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 496(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,480(%%r14);"NOP(NOPCOUNT)"movupd %%xmm1,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_movupd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movupd instruction
 */
static void asm_copy_movupd_3(param_t *params) __attribute__((noinline));
static void asm_copy_movupd_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movupd_3;"
                ".align 64,0x0;"
                "_copy_loop_movupd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movupd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movupd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movupd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "movupd 48(%%r10),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movupd 64(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd 80(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm0,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movupd %%xmm1,64(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm2,80(%%r12);"NOP(NOPCOUNT)
                "add $528,%%r10;"
                "movupd 96(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 112(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r13)
                "movupd 128(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm0,96(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,112(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movupd %%xmm2,128(%%r14);"NOP(NOPCOUNT)
                "add $528,%%r12;"
                "movupd 144(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 160(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 176(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm0,144(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,160(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,176(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,192,r13)
                "movupd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 224(%%r13),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movupd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,224(%%r14);"NOP(NOPCOUNT)
                
                "movupd 240(%%r13),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "movupd 256(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 272(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm0,240(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movupd %%xmm1,256(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,272(%%r14);"NOP(NOPCOUNT)
                
                "movupd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 304(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movupd 320(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm0,288(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movupd %%xmm2,320(%%r14);"NOP(NOPCOUNT)
                
                "movupd 336(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 352(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 368(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm0,336(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,352(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movupd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movupd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                
                "movupd 432(%%r13),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movupd 448(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 464(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm0,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movupd %%xmm1,448(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,464(%%r14);"NOP(NOPCOUNT)
                
                "movupd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 496(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "movupd 512(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm0,480(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,496(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "movupd %%xmm2,512(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_movupd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movupd instruction
 */
static void asm_copy_movupd_4(param_t *params) __attribute__((noinline));
static void asm_copy_movupd_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movupd_4;"
                ".align 64,0x0;"
                "_copy_loop_movupd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movupd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movupd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movupd 48(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movupd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)
                "movupd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movupd 80(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd 96(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movupd 112(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movupd %%xmm0,64(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm1,80(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm2,96(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm3,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movupd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 160(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 176(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movupd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,160(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "movupd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 224(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 240(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movupd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,224(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movupd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 288(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 304(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movupd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,288(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)
                "movupd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 336(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 352(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 368(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movupd %%xmm0,320(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,336(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,352(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movupd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 432(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movupd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)
                "movupd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 464(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 480(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 496(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movupd %%xmm0,448(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,464(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,480(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_movupd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movupd instruction
 */
static void asm_copy_movupd_8(param_t *params) __attribute__((noinline));
static void asm_copy_movupd_8(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movupd_8;"
                ".align 64,0x0;"
                "_copy_loop_movupd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movupd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movupd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movupd 48(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movupd 64(%%r10),%%xmm4;"NOP(NOPCOUNT)
                "movupd 80(%%r10),%%xmm5;"NOP(NOPCOUNT)
                "movupd 96(%%r10),%%xmm6;"NOP(NOPCOUNT)
                "movupd 112(%%r10),%%xmm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "movupd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movupd %%xmm4,64(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm5,80(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm6,96(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm7,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movupd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 160(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 176(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r13)
                "movupd 192(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movupd 208(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movupd 224(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movupd 240(%%r13),%%xmm7;"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,128,r14)
                "movupd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,160(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,176(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movupd %%xmm4,192(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,208(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm6,224(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm7,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movupd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 288(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 304(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movupd 320(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movupd 336(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movupd 352(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movupd 368(%%r13),%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r14)
                "movupd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,288(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movupd %%xmm4,320(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,336(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm6,352(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm7,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movupd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 432(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movupd 448(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movupd 464(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movupd 480(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movupd 496(%%r13),%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r14)
                "movupd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movupd %%xmm4,448(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,464(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm6,480(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm7,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_movupd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovupd instruction
 */
static void asm_copy_vmovupd_1(param_t *params) __attribute__((noinline));
static void asm_copy_vmovupd_1(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_vmovupd_1;"
                ".align 64,0x0;"
                "_copy_loop_vmovupd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "vmovupd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovupd 32(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "vmovupd 64(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,64(%%r12);"NOP(NOPCOUNT)
                "vmovupd 96(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
                "vmovupd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,128(%%r12);"NOP(NOPCOUNT)
                "vmovupd 160(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
                "vmovupd 192(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,192(%%r12);"NOP(NOPCOUNT)
                "vmovupd 224(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "vmovupd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovupd 288(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "vmovupd 320(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,320(%%r14);"NOP(NOPCOUNT)
                "vmovupd 352(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "vmovupd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovupd 416(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "vmovupd 448(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,448(%%r14);"NOP(NOPCOUNT)
                "vmovupd 480(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
                "vmovupd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovupd 544(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
                "vmovupd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,576(%%r14);"NOP(NOPCOUNT)
                "vmovupd 608(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
                "vmovupd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,640(%%r14);"NOP(NOPCOUNT)
                "vmovupd 672(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
                "vmovupd 704(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,704(%%r14);"NOP(NOPCOUNT)
                "vmovupd 736(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
                "vmovupd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovupd 800(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
                "vmovupd 832(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,832(%%r14);"NOP(NOPCOUNT)
                "vmovupd 864(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
                "vmovupd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,896(%%r14);"NOP(NOPCOUNT)
                "vmovupd 928(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
                "vmovupd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,960(%%r14);"NOP(NOPCOUNT)
                "vmovupd 992(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm0,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_vmovupd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovupd instruction
 */
static void asm_copy_vmovupd_2(param_t *params) __attribute__((noinline));
static void asm_copy_vmovupd_2(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_vmovupd_2;"
                ".align 64,0x0;"
                "_copy_loop_vmovupd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "vmovupd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,0(%%r12);"NOP(NOPCOUNT)"vmovupd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "vmovupd 64(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd 96(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,64(%%r12);"NOP(NOPCOUNT)"vmovupd %%ymm1,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
                "vmovupd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd 160(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,128(%%r12);"NOP(NOPCOUNT)"vmovupd %%ymm1,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
                "vmovupd 192(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd 224(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,192(%%r12);"NOP(NOPCOUNT)"vmovupd %%ymm1,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "vmovupd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,256(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "vmovupd 320(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 352(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,320(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm1,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "vmovupd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,384(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "vmovupd 448(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 480(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,448(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm1,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
                "vmovupd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,512(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
                "vmovupd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 608(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,576(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm1,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
                "vmovupd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 672(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,640(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm1,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
                "vmovupd 704(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 736(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,704(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm1,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
                "vmovupd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,768(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
                "vmovupd 832(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 864(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,832(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm1,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
                "vmovupd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 928(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,896(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm1,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
                "vmovupd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 992(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,960(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm1,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_vmovupd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovupd instruction
 */
static void asm_copy_vmovupd_3(param_t *params) __attribute__((noinline));
static void asm_copy_vmovupd_3(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_vmovupd_3;"
                ".align 64,0x0;"
                "_copy_loop_vmovupd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovupd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovupd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovupd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovupd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "vmovupd 96(%%r10),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovupd 128(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd 160(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovupd %%ymm1,128(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm2,160(%%r12);"NOP(NOPCOUNT)
                "add $1056,%%r10;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "vmovupd 192(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 224(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovupd 256(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "vmovupd %%ymm0,192(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,224(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovupd %%ymm2,256(%%r14);"NOP(NOPCOUNT)
                "add $1056,%%r12;"
                "vmovupd 288(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovupd 320(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd 352(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovupd %%ymm1,320(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm2,352(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovupd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovupd 448(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovupd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovupd %%ymm2,448(%%r14);"NOP(NOPCOUNT)
                
                "vmovupd 480(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovupd 512(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd 544(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,480(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovupd %%ymm1,512(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm2,544(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovupd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 608(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovupd 640(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovupd %%ymm0,576(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovupd %%ymm2,640(%%r14);"NOP(NOPCOUNT)
                
                "vmovupd 672(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovupd 704(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd 736(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovupd %%ymm1,704(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm2,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovupd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovupd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovupd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovupd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                
                "vmovupd 864(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovupd 896(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd 928(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovupd %%ymm1,896(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm2,928(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovupd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 992(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r13)
                "vmovupd 1024(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovupd %%ymm0,960(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,992(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r14)
                "vmovupd %%ymm2,1024(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_vmovupd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovupd instruction
 */
static void asm_copy_vmovupd_4(param_t *params) __attribute__((noinline));
static void asm_copy_vmovupd_4(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_vmovupd_4;"
                ".align 64,0x0;"
                "_copy_loop_vmovupd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovupd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovupd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 96(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovupd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovupd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovupd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 160(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmovupd 192(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 224(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovupd %%ymm0,128(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovupd %%ymm2,192(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovupd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovupd 320(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 352(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovupd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovupd %%ymm2,320(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovupd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovupd 448(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 480(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovupd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovupd %%ymm2,448(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovupd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovupd 576(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 608(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovupd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovupd %%ymm2,576(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovupd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 672(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovupd 704(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 736(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovupd %%ymm0,640(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovupd %%ymm2,704(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovupd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovupd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 864(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovupd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovupd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovupd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 928(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovupd 960(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 992(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovupd %%ymm0,896(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovupd %%ymm2,960(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_vmovupd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovupd instruction
 */
static void asm_copy_vmovupd_8(param_t *params) __attribute__((noinline));
static void asm_copy_vmovupd_8(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_vmovupd_8;"
                ".align 64,0x0;"
                "_copy_loop_vmovupd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovupd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovupd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 96(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovupd 128(%%r10),%%ymm4;"NOP(NOPCOUNT)
                "vmovupd 160(%%r10),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmovupd 192(%%r10),%%ymm6;"NOP(NOPCOUNT)
                "vmovupd 224(%%r10),%%ymm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovupd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovupd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovupd %%ymm4,128(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovupd %%ymm6,192(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm7,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovupd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovupd 320(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 352(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovupd 384(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovupd 416(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovupd 448(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovupd 480(%%r13),%%ymm7;"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovupd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovupd %%ymm2,320(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,352(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovupd %%ymm4,384(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovupd %%ymm6,448(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm7,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovupd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovupd 576(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 608(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovupd 640(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovupd 672(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovupd 704(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovupd 736(%%r13),%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovupd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovupd %%ymm2,576(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovupd %%ymm4,640(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovupd %%ymm6,704(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm7,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovupd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovupd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 864(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovupd 896(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovupd 928(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovupd 960(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovupd 992(%%r13),%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovupd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovupd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovupd %%ymm4,896(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovupd %%ymm6,960(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm7,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_vmovupd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov instruction
 */
static void asm_copy_mov_1(param_t *params) __attribute__((noinline));
static void asm_copy_mov_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_mov_1;"
                ".align 64,0x0;"
                "_copy_loop_mov_1:"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,0(%%rdi);"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,8(%%rdi);"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,16(%%rdi);"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,32(%%rdi);"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,48(%%rdi);"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,64(%%rdi);"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,72(%%rdi);"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,80(%%rdi);"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,96(%%rdi);"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,104(%%rdi);"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,112(%%rdi);"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,120(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _copy_loop_mov_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov instruction
 */
static void asm_copy_mov_2(param_t *params) __attribute__((noinline));
static void asm_copy_mov_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_mov_2;"
                ".align 64,0x0;"
                "_copy_loop_mov_2:"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,0(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,8(%%rdi);"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,16(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,32(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,48(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,64(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,72(%%rdi);"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,80(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,96(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,104(%%rdi);"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,112(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)PREFETCH(LINE_PREFETCH,128,rdi)
                "mov 128(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,128(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,136(%%rdi);"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,144(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,152(%%rdi);"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,160(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,168(%%rdi);"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,176(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)PREFETCH(LINE_PREFETCH,192,rdi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,192(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,200(%%rdi);"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,208(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,216(%%rdi);"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,224(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,232(%%rdi);"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,240(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _copy_loop_mov_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov instruction
 */
static void asm_copy_mov_3(param_t *params) __attribute__((noinline));
static void asm_copy_mov_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_mov_3;"
                ".align 64,0x0;"
                "_copy_loop_mov_3:"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r10;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,rdi)
                "mov %%r8,0(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,8(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,16(%%rdi);"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,24(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,32(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)
                "mov 64(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,48(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rdi)
                "mov %%r10,64(%%rdi);"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,72(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,80(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,96(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,104(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,112(%%rdi);"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)
                "mov 128(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rdi)
                "mov %%r9,128(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,136(%%rdi);"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,144(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,152(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,160(%%rdi);"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,168(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,176(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r10;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rdi)
                "mov %%r8,192(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,200(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,208(%%rdi);"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,216(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,224(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,232(%%rdi);"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rsi)
                "mov 256(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,240(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,248(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rdi)
                "mov %%r10,256(%%rdi);"NOP(NOPCOUNT)
                "add $264,%%rsi;"
                "add $264,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _copy_loop_mov_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov instruction
 */
static void asm_copy_mov_4(param_t *params) __attribute__((noinline));
static void asm_copy_mov_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_mov_4;"
                ".align 64,0x0;"
                "_copy_loop_mov_4:"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,rdi)
                "mov %%r8,0(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,8(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,16(%%rdi);"NOP(NOPCOUNT)
                "mov %%r11,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r11;"NOP(NOPCOUNT)
                "mov %%r8,32(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,40(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,48(%%rdi);"NOP(NOPCOUNT)
                "mov %%r11,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rdi)
                "mov %%r8,64(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,72(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,80(%%rdi);"NOP(NOPCOUNT)
                "mov %%r11,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r11;"NOP(NOPCOUNT)
                "mov %%r8,96(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,104(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,112(%%rdi);"NOP(NOPCOUNT)
                "mov %%r11,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)
                "mov 128(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rdi)
                "mov %%r8,128(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,136(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,144(%%rdi);"NOP(NOPCOUNT)
                "mov %%r11,152(%%rdi);"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r11;"NOP(NOPCOUNT)
                "mov %%r8,160(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,168(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,176(%%rdi);"NOP(NOPCOUNT)
                "mov %%r11,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rdi)
                "mov %%r8,192(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,200(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,208(%%rdi);"NOP(NOPCOUNT)
                "mov %%r11,216(%%rdi);"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r11;"NOP(NOPCOUNT)
                "mov %%r8,224(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,232(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,240(%%rdi);"NOP(NOPCOUNT)
                "mov %%r11,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _copy_loop_mov_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov_clflush instruction
 */
static void asm_copy_mov_clflush_1(param_t *params) __attribute__((noinline));
static void asm_copy_mov_clflush_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_mov_clflush_1;"
                ".align 64,0x0;"
                "_copy_loop_mov_clflush_1:"
                "clflush -384(%%rdi);""clflush -320(%%rdi);"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,0(%%rdi);"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,8(%%rdi);"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,16(%%rdi);"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,32(%%rdi);"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,48(%%rdi);"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,64(%%rdi);"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,72(%%rdi);"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,80(%%rdi);"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,96(%%rdi);"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,104(%%rdi);"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,112(%%rdi);"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r8,120(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _copy_loop_mov_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov_clflush instruction
 */
static void asm_copy_mov_clflush_2(param_t *params) __attribute__((noinline));
static void asm_copy_mov_clflush_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_mov_clflush_2;"
                ".align 64,0x0;"
                "_copy_loop_mov_clflush_2:"
                "clflush -384(%%rdi);""clflush -320(%%rdi);"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,0(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,8(%%rdi);"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,16(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,32(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,48(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,64(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,72(%%rdi);"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,80(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,96(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,104(%%rdi);"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,112(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)PREFETCH(LINE_PREFETCH,128,rdi)
                "mov 128(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,128(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,136(%%rdi);"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,144(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,152(%%rdi);"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,160(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,168(%%rdi);"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,176(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)PREFETCH(LINE_PREFETCH,192,rdi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,192(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,200(%%rdi);"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,208(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,216(%%rdi);"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,224(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,232(%%rdi);"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r8,240(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _copy_loop_mov_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov_clflush instruction
 */
static void asm_copy_mov_clflush_3(param_t *params) __attribute__((noinline));
static void asm_copy_mov_clflush_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_mov_clflush_3;"
                ".align 64,0x0;"
                "_copy_loop_mov_clflush_3:"
                "clflush -448(%%rdi);clflush -384(%%rdi);""clflush -320(%%rdi);"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r10;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,rdi)
                "mov %%r8,0(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,8(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,16(%%rdi);"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,24(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,32(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)
                "mov 64(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,48(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rdi)
                "mov %%r10,64(%%rdi);"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,72(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,80(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,96(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,104(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,112(%%rdi);"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)
                "mov 128(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rdi)
                "mov %%r9,128(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,136(%%rdi);"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,144(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,152(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,160(%%rdi);"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,168(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,176(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r10;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rdi)
                "mov %%r8,192(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,200(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,208(%%rdi);"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,216(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,224(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,232(%%rdi);"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rsi)
                "mov 256(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r8,240(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,248(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rdi)
                "mov %%r10,256(%%rdi);"NOP(NOPCOUNT)
                "add $264,%%rsi;"
                "add $264,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _copy_loop_mov_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov_clflush instruction
 */
static void asm_copy_mov_clflush_4(param_t *params) __attribute__((noinline));
static void asm_copy_mov_clflush_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_mov_clflush_4;"
                ".align 64,0x0;"
                "_copy_loop_mov_clflush_4:"
                "clflush -384(%%rdi);""clflush -320(%%rdi);"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,rdi)
                "mov %%r8,0(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,8(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,16(%%rdi);"NOP(NOPCOUNT)
                "mov %%r11,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r11;"NOP(NOPCOUNT)
                "mov %%r8,32(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,40(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,48(%%rdi);"NOP(NOPCOUNT)
                "mov %%r11,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rdi)
                "mov %%r8,64(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,72(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,80(%%rdi);"NOP(NOPCOUNT)
                "mov %%r11,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r11;"NOP(NOPCOUNT)
                "mov %%r8,96(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,104(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,112(%%rdi);"NOP(NOPCOUNT)
                "mov %%r11,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)
                "mov 128(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rdi)
                "mov %%r8,128(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,136(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,144(%%rdi);"NOP(NOPCOUNT)
                "mov %%r11,152(%%rdi);"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r11;"NOP(NOPCOUNT)
                "mov %%r8,160(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,168(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,176(%%rdi);"NOP(NOPCOUNT)
                "mov %%r11,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rdi)
                "mov %%r8,192(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,200(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,208(%%rdi);"NOP(NOPCOUNT)
                "mov %%r11,216(%%rdi);"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r11;"NOP(NOPCOUNT)
                "mov %%r8,224(%%rdi);"NOP(NOPCOUNT)
                "mov %%r9,232(%%rdi);"NOP(NOPCOUNT)
                "mov %%r10,240(%%rdi);"NOP(NOPCOUNT)
                "mov %%r11,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _copy_loop_mov_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movnti instruction
 */
static void asm_copy_movnti_1(param_t *params) __attribute__((noinline));
static void asm_copy_movnti_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movnti_1;"
                ".align 64,0x0;"
                "_copy_loop_movnti_1:"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r8,0(%%rdi);"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r8,8(%%rdi);"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r8,16(%%rdi);"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r8,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r8,32(%%rdi);"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r8,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r8,48(%%rdi);"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r8,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r8,64(%%rdi);"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r8,72(%%rdi);"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r8,80(%%rdi);"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r8,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r8,96(%%rdi);"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r8,104(%%rdi);"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r8,112(%%rdi);"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r8,120(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _copy_loop_movnti_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movnti instruction
 */
static void asm_copy_movnti_2(param_t *params) __attribute__((noinline));
static void asm_copy_movnti_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movnti_2;"
                ".align 64,0x0;"
                "_copy_loop_movnti_2:"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r8,0(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,8(%%rdi);"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r8,16(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r8,32(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r8,48(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r8,64(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,72(%%rdi);"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r8,80(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r8,96(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,104(%%rdi);"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r8,112(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)PREFETCH(LINE_PREFETCH,128,rdi)
                "mov 128(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r8,128(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,136(%%rdi);"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r8,144(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,152(%%rdi);"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r8,160(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,168(%%rdi);"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r8,176(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)PREFETCH(LINE_PREFETCH,192,rdi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r8,192(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,200(%%rdi);"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r8,208(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,216(%%rdi);"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r8,224(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,232(%%rdi);"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r8,240(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _copy_loop_movnti_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movnti instruction
 */
static void asm_copy_movnti_3(param_t *params) __attribute__((noinline));
static void asm_copy_movnti_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movnti_3;"
                ".align 64,0x0;"
                "_copy_loop_movnti_3:"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r10;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,rdi)
                "movnti %%r8,0(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,8(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r10,16(%%rdi);"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r8,24(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,32(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r10,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)
                "mov 64(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r8,48(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rdi)
                "movnti %%r10,64(%%rdi);"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r8,72(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,80(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r10,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r8,96(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,104(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r10,112(%%rdi);"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)
                "mov 128(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r8,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rdi)
                "movnti %%r9,128(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r10,136(%%rdi);"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r8,144(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,152(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r10,160(%%rdi);"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r8,168(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,176(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r10,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r10;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rdi)
                "movnti %%r8,192(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,200(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r10,208(%%rdi);"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r8,216(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,224(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r10,232(%%rdi);"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rsi)
                "mov 256(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r8,240(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,248(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rdi)
                "movnti %%r10,256(%%rdi);"NOP(NOPCOUNT)
                "add $264,%%rsi;"
                "add $264,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _copy_loop_movnti_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movnti instruction
 */
static void asm_copy_movnti_4(param_t *params) __attribute__((noinline));
static void asm_copy_movnti_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movnti_4;"
                ".align 64,0x0;"
                "_copy_loop_movnti_4:"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,rdi)
                "movnti %%r8,0(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,8(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r10,16(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r11,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r11;"NOP(NOPCOUNT)
                "movnti %%r8,32(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,40(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r10,48(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r11,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rdi)
                "movnti %%r8,64(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,72(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r10,80(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r11,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r11;"NOP(NOPCOUNT)
                "movnti %%r8,96(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,104(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r10,112(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r11,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)
                "mov 128(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rdi)
                "movnti %%r8,128(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,136(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r10,144(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r11,152(%%rdi);"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r11;"NOP(NOPCOUNT)
                "movnti %%r8,160(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,168(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r10,176(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r11,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rdi)
                "movnti %%r8,192(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,200(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r10,208(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r11,216(%%rdi);"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r11;"NOP(NOPCOUNT)
                "movnti %%r8,224(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r9,232(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r10,240(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r11,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _copy_loop_movnti_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movntpd instruction
 */
static void asm_copy_movntpd_1(param_t *params) __attribute__((noinline));
static void asm_copy_movntpd_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movntpd_1;"
                ".align 64,0x0;"
                "_copy_loop_movntpd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,16(%%r12);"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,32(%%r12);"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movapd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,64(%%r12);"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,80(%%r12);"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,96(%%r12);"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movapd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,144(%%r14);"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,160(%%r14);"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movapd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,208(%%r14);"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,224(%%r14);"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movapd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,272(%%r14);"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,288(%%r14);"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movapd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,320(%%r14);"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,336(%%r14);"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,352(%%r14);"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,400(%%r14);"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,416(%%r14);"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movapd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,448(%%r14);"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,464(%%r14);"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,480(%%r14);"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm0,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_movntpd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movntpd instruction
 */
static void asm_copy_movntpd_2(param_t *params) __attribute__((noinline));
static void asm_copy_movntpd_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movntpd_2;"
                ".align 64,0x0;"
                "_copy_loop_movntpd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,0(%%r12);"NOP(NOPCOUNT)"movntpd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd 48(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,32(%%r12);"NOP(NOPCOUNT)"movntpd %%xmm1,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movapd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd 80(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,64(%%r12);"NOP(NOPCOUNT)"movntpd %%xmm1,80(%%r12);"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd 112(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,96(%%r12);"NOP(NOPCOUNT)"movntpd %%xmm1,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movapd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,128(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 176(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,160(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm1,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movapd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,192(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 240(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,224(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm1,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movapd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,256(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 304(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,288(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm1,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movapd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 336(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,320(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm1,336(%%r14);"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 368(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,352(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm1,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,384(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 432(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,416(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm1,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movapd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 464(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,448(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm1,464(%%r14);"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 496(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,480(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm1,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_movntpd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movntpd instruction
 */
static void asm_copy_movntpd_3(param_t *params) __attribute__((noinline));
static void asm_copy_movntpd_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movntpd_3;"
                ".align 64,0x0;"
                "_copy_loop_movntpd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movntpd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "movapd 48(%%r10),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm0,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movntpd %%xmm1,64(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm2,80(%%r12);"NOP(NOPCOUNT)
                "add $528,%%r10;"
                "movapd 96(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 112(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm0,96(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,112(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movntpd %%xmm2,128(%%r14);"NOP(NOPCOUNT)
                "add $528,%%r12;"
                "movapd 144(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm0,144(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,160(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,176(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movntpd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,224(%%r14);"NOP(NOPCOUNT)
                
                "movapd 240(%%r13),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm0,240(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movntpd %%xmm1,256(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,272(%%r14);"NOP(NOPCOUNT)
                
                "movapd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm0,288(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movntpd %%xmm2,320(%%r14);"NOP(NOPCOUNT)
                
                "movapd 336(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm0,336(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,352(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movntpd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                
                "movapd 432(%%r13),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm0,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movntpd %%xmm1,448(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,464(%%r14);"NOP(NOPCOUNT)
                
                "movapd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "movapd 512(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm0,480(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,496(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "movntpd %%xmm2,512(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_movntpd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movntpd instruction
 */
static void asm_copy_movntpd_4(param_t *params) __attribute__((noinline));
static void asm_copy_movntpd_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movntpd_4;"
                ".align 64,0x0;"
                "_copy_loop_movntpd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movntpd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movntpd %%xmm0,64(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm1,80(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm2,96(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm3,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movntpd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,160(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movntpd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,224(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movntpd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,288(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movntpd %%xmm0,320(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,336(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,352(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movntpd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movntpd %%xmm0,448(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,464(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,480(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_movntpd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movntpd instruction
 */
static void asm_copy_movntpd_8(param_t *params) __attribute__((noinline));
static void asm_copy_movntpd_8(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_movntpd_8;"
                ".align 64,0x0;"
                "_copy_loop_movntpd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10),%%xmm4;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm5;"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm6;"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "movntpd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movntpd %%xmm4,64(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm5,80(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm6,96(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm7,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm7;"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,128,r14)
                "movntpd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,160(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,176(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movntpd %%xmm4,192(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,208(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm6,224(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm7,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r14)
                "movntpd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,288(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movntpd %%xmm4,320(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,336(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm6,352(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm7,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r14)
                "movntpd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movntpd %%xmm4,448(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,464(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm6,480(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm7,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_movntpd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovntpd instruction
 */
static void asm_copy_vmovntpd_1(param_t *params) __attribute__((noinline));
static void asm_copy_vmovntpd_1(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_vmovntpd_1;"
                ".align 64,0x0;"
                "_copy_loop_vmovntpd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovapd 32(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "vmovapd 64(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,64(%%r12);"NOP(NOPCOUNT)
                "vmovapd 96(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
                "vmovapd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,128(%%r12);"NOP(NOPCOUNT)
                "vmovapd 160(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
                "vmovapd 192(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,192(%%r12);"NOP(NOPCOUNT)
                "vmovapd 224(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "vmovapd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovapd 288(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "vmovapd 320(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,320(%%r14);"NOP(NOPCOUNT)
                "vmovapd 352(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "vmovapd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovapd 416(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "vmovapd 448(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,448(%%r14);"NOP(NOPCOUNT)
                "vmovapd 480(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
                "vmovapd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovapd 544(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
                "vmovapd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,576(%%r14);"NOP(NOPCOUNT)
                "vmovapd 608(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
                "vmovapd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,640(%%r14);"NOP(NOPCOUNT)
                "vmovapd 672(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
                "vmovapd 704(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,704(%%r14);"NOP(NOPCOUNT)
                "vmovapd 736(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovapd 800(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
                "vmovapd 832(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,832(%%r14);"NOP(NOPCOUNT)
                "vmovapd 864(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
                "vmovapd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,896(%%r14);"NOP(NOPCOUNT)
                "vmovapd 928(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
                "vmovapd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,960(%%r14);"NOP(NOPCOUNT)
                "vmovapd 992(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm0,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_vmovntpd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovntpd instruction
 */
static void asm_copy_vmovntpd_2(param_t *params) __attribute__((noinline));
static void asm_copy_vmovntpd_2(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_vmovntpd_2;"
                ".align 64,0x0;"
                "_copy_loop_vmovntpd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,0(%%r12);"NOP(NOPCOUNT)"vmovntpd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "vmovapd 64(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd 96(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,64(%%r12);"NOP(NOPCOUNT)"vmovntpd %%ymm1,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
                "vmovapd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd 160(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,128(%%r12);"NOP(NOPCOUNT)"vmovntpd %%ymm1,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
                "vmovapd 192(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd 224(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,192(%%r12);"NOP(NOPCOUNT)"vmovntpd %%ymm1,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "vmovapd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,256(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "vmovapd 320(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 352(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,320(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm1,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "vmovapd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,384(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "vmovapd 448(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 480(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,448(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm1,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
                "vmovapd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,512(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
                "vmovapd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 608(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,576(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm1,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
                "vmovapd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 672(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,640(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm1,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
                "vmovapd 704(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 736(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,704(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm1,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,768(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
                "vmovapd 832(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 864(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,832(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm1,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
                "vmovapd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 928(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,896(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm1,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
                "vmovapd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 992(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,960(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm1,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_vmovntpd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovntpd instruction
 */
static void asm_copy_vmovntpd_3(param_t *params) __attribute__((noinline));
static void asm_copy_vmovntpd_3(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_vmovntpd_3;"
                ".align 64,0x0;"
                "_copy_loop_vmovntpd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovapd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovntpd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovntpd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "vmovapd 96(%%r10),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovapd 128(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 160(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovntpd %%ymm1,128(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,160(%%r12);"NOP(NOPCOUNT)
                "add $1056,%%r10;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "vmovapd 192(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 224(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovapd 256(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "vmovntpd %%ymm0,192(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,224(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovntpd %%ymm2,256(%%r14);"NOP(NOPCOUNT)
                "add $1056,%%r12;"
                "vmovapd 288(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovapd 320(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 352(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovntpd %%ymm1,320(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,352(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovapd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovapd 448(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovntpd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovntpd %%ymm2,448(%%r14);"NOP(NOPCOUNT)
                
                "vmovapd 480(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovapd 512(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 544(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,480(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovntpd %%ymm1,512(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,544(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovapd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 608(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovapd 640(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovntpd %%ymm0,576(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovntpd %%ymm2,640(%%r14);"NOP(NOPCOUNT)
                
                "vmovapd 672(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovapd 704(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 736(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovntpd %%ymm1,704(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovapd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovntpd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovntpd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                
                "vmovapd 864(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovapd 896(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 928(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovntpd %%ymm1,896(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,928(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovapd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 992(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r13)
                "vmovapd 1024(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovntpd %%ymm0,960(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,992(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r14)
                "vmovntpd %%ymm2,1024(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_vmovntpd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovntpd instruction
 */
static void asm_copy_vmovntpd_4(param_t *params) __attribute__((noinline));
static void asm_copy_vmovntpd_4(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_vmovntpd_4;"
                ".align 64,0x0;"
                "_copy_loop_vmovntpd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovapd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 96(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovntpd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovntpd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovapd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 160(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmovapd 192(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 224(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovntpd %%ymm0,128(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovntpd %%ymm2,192(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovapd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovapd 320(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 352(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovntpd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovntpd %%ymm2,320(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovapd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovapd 448(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 480(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovntpd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovntpd %%ymm2,448(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovapd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovapd 576(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 608(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovntpd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovntpd %%ymm2,576(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovapd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 672(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovapd 704(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 736(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovntpd %%ymm0,640(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovntpd %%ymm2,704(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovapd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 864(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovntpd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovntpd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovapd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 928(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovapd 960(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 992(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovntpd %%ymm0,896(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovntpd %%ymm2,960(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_vmovntpd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovntpd instruction
 */
static void asm_copy_vmovntpd_8(param_t *params) __attribute__((noinline));
static void asm_copy_vmovntpd_8(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _copy_loop_vmovntpd_8;"
                ".align 64,0x0;"
                "_copy_loop_vmovntpd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovapd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 96(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovapd 128(%%r10),%%ymm4;"NOP(NOPCOUNT)
                "vmovapd 160(%%r10),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmovapd 192(%%r10),%%ymm6;"NOP(NOPCOUNT)
                "vmovapd 224(%%r10),%%ymm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovntpd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovntpd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovntpd %%ymm4,128(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovntpd %%ymm6,192(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm7,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovapd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovapd 320(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 352(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovapd 384(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovapd 416(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovapd 448(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovapd 480(%%r13),%%ymm7;"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovntpd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovntpd %%ymm2,320(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,352(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovntpd %%ymm4,384(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovntpd %%ymm6,448(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm7,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovapd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovapd 576(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 608(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovapd 640(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovapd 672(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovapd 704(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovapd 736(%%r13),%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovntpd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovntpd %%ymm2,576(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovntpd %%ymm4,640(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovntpd %%ymm6,704(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm7,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovapd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 864(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovapd 896(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovapd 928(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovapd 960(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovapd 992(%%r13),%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovntpd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovntpd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovntpd %%ymm4,896(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovntpd %%ymm6,960(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm7,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _copy_loop_vmovntpd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movapd instruction
 */
static void asm_scale_movapd_1(param_t *params) __attribute__((noinline));
static void asm_scale_movapd_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
                "movddup (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movapd_1;"
                ".align 64,0x0;"
                "_scale_loop_movapd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movapd 0(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,16(%%r12);"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,32(%%r12);"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movapd 64(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,64(%%r12);"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,80(%%r12);"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,96(%%r12);"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movapd 128(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,144(%%r14);"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,160(%%r14);"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movapd 192(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,208(%%r14);"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,224(%%r14);"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movapd 256(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,272(%%r14);"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,288(%%r14);"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movapd 320(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,320(%%r14);"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,336(%%r14);"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,352(%%r14);"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movapd 384(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,400(%%r14);"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,416(%%r14);"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movapd 448(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,448(%%r14);"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,464(%%r14);"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,480(%%r14);"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movapd %%xmm0,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_movapd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movapd instruction
 */
static void asm_scale_movapd_2(param_t *params) __attribute__((noinline));
static void asm_scale_movapd_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
                "movddup (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movapd_2;"
                ".align 64,0x0;"
                "_scale_loop_movapd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movapd 0(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,32(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm1,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movapd 64(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,64(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm1,80(%%r12);"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,96(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm1,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movapd 128(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,160(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movapd 192(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,224(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movapd 256(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,288(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movapd 320(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,320(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,336(%%r14);"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,352(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movapd 384(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,416(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movapd 448(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,448(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,464(%%r14);"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm0,480(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_movapd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movapd instruction
 */
static void asm_scale_movapd_3(param_t *params) __attribute__((noinline));
static void asm_scale_movapd_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
                "movddup (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movapd_3;"
                ".align 64,0x0;"
                "_scale_loop_movapd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movapd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "movapd 48(%%r10), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 80(%%r10), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm0,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movapd %%xmm1,64(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm2,80(%%r12);"NOP(NOPCOUNT)
                "add $528,%%r10;"
                "movapd 96(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 112(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm0,96(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,112(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movapd %%xmm2,128(%%r14);"NOP(NOPCOUNT)
                "add $528,%%r12;"
                "movapd 144(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 160(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 176(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm0,144(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,160(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,176(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 208(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 224(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movapd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,224(%%r14);"NOP(NOPCOUNT)
                
                "movapd 240(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 272(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm0,240(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movapd %%xmm1,256(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,272(%%r14);"NOP(NOPCOUNT)
                
                "movapd 288(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 304(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm0,288(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movapd %%xmm2,320(%%r14);"NOP(NOPCOUNT)
                
                "movapd 336(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 352(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 368(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm0,336(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,352(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movapd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                
                "movapd 432(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 464(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm0,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movapd %%xmm1,448(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,464(%%r14);"NOP(NOPCOUNT)
                
                "movapd 480(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 496(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "movapd 512(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm0,480(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,496(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "movapd %%xmm2,512(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_movapd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movapd instruction
 */
static void asm_scale_movapd_4(param_t *params) __attribute__((noinline));
static void asm_scale_movapd_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
                "movddup (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movapd_4;"
                ".align 64,0x0;"
                "_scale_loop_movapd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movapd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movapd %%xmm0,64(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm1,80(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm2,96(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm3,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movapd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,160(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movapd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,224(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movapd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,288(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movapd %%xmm0,320(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,336(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,352(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movapd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movapd %%xmm0,448(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,464(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,480(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_movapd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movapd instruction
 */
static void asm_scale_movapd_8(param_t *params) __attribute__((noinline));
static void asm_scale_movapd_8(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
                "movddup (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movapd_8;"
                ".align 64,0x0;"
                "_scale_loop_movapd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10),%%xmm4;mulpd %%xmm15,%%xmm4;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm5;mulpd %%xmm15,%%xmm5;"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm6;mulpd %%xmm15,%%xmm6;"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm7;mulpd %%xmm15,%%xmm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "movapd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movapd %%xmm4,64(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm5,80(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm6,96(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm7,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13),%%xmm4;mulpd %%xmm15,%%xmm4;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm5;mulpd %%xmm15,%%xmm5;"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm6;mulpd %%xmm15,%%xmm6;"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm7;mulpd %%xmm15,%%xmm7;"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,128,r14)
                "movapd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,160(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,176(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movapd %%xmm4,192(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,208(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm6,224(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm7,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13),%%xmm4;mulpd %%xmm15,%%xmm4;"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm5;mulpd %%xmm15,%%xmm5;"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm6;mulpd %%xmm15,%%xmm6;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm7;mulpd %%xmm15,%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r14)
                "movapd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,288(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movapd %%xmm4,320(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,336(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm6,352(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm7,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13),%%xmm4;mulpd %%xmm15,%%xmm4;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm5;mulpd %%xmm15,%%xmm5;"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm6;mulpd %%xmm15,%%xmm6;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm7;mulpd %%xmm15,%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r14)
                "movapd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movapd %%xmm4,448(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,464(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm6,480(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm7,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_movapd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovapd instruction
 */
static void asm_scale_vmovapd_1(param_t *params) __attribute__((noinline));
static void asm_scale_vmovapd_1(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
		"movddup (%%rax),%%xmm15;"
                "vinsertf128 $0, %%xmm15, %%ymm15, %%ymm15;"
                "vinsertf128 $1, %%xmm15, %%ymm15, %%ymm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_vmovapd_1;"
                ".align 64,0x0;"
                "_scale_loop_vmovapd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
		"vmulpd 0(%%r10),%%ymm15,%%ymm0;vmovapd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
		"vmulpd 32(%%r10),%%ymm15,%%ymm0;vmovapd %%ymm0,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
		"vmulpd 64(%%r10),%%ymm15,%%ymm0;vmovapd %%ymm0,64(%%r12);"NOP(NOPCOUNT)
		"vmulpd 96(%%r10),%%ymm15,%%ymm0;vmovapd %%ymm0,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
		"vmulpd 128(%%r10),%%ymm15,%%ymm0;vmovapd %%ymm0,128(%%r12);"NOP(NOPCOUNT)
		"vmulpd 160(%%r10),%%ymm15,%%ymm0;vmovapd %%ymm0,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
		"vmulpd 192(%%r10),%%ymm15,%%ymm0;vmovapd %%ymm0,192(%%r12);"NOP(NOPCOUNT)
		"vmulpd 224(%%r10),%%ymm15,%%ymm0;vmovapd %%ymm0,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
		"vmulpd 256(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
		"vmulpd 288(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
		"vmulpd 320(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,320(%%r14);"NOP(NOPCOUNT)
		"vmulpd 352(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
		"vmulpd 384(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
		"vmulpd 416(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
		"vmulpd 448(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,448(%%r14);"NOP(NOPCOUNT)
		"vmulpd 480(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
		"vmulpd 512(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
		"vmulpd 544(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
		"vmulpd 576(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,576(%%r14);"NOP(NOPCOUNT)
		"vmulpd 608(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
		"vmulpd 640(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,640(%%r14);"NOP(NOPCOUNT)
		"vmulpd 672(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
		"vmulpd 704(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,704(%%r14);"NOP(NOPCOUNT)
		"vmulpd 736(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
		"vmulpd 768(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
		"vmulpd 800(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
		"vmulpd 832(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,832(%%r14);"NOP(NOPCOUNT)
		"vmulpd 864(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
		"vmulpd 896(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,896(%%r14);"NOP(NOPCOUNT)
		"vmulpd 928(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
		"vmulpd 960(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,960(%%r14);"NOP(NOPCOUNT)
		"vmulpd 992(%%r13),%%ymm15,%%ymm0;vmovapd %%ymm0,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_vmovapd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovapd instruction
 */
static void asm_scale_vmovapd_2(param_t *params) __attribute__((noinline));
static void asm_scale_vmovapd_2(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
		"movddup (%%rax),%%xmm15;"
                "vinsertf128 $0, %%xmm15, %%ymm15, %%ymm15;"
                "vinsertf128 $1, %%xmm15, %%ymm15, %%ymm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_vmovapd_2;"
                ".align 64,0x0;"
                "_scale_loop_vmovapd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "vmulpd 0(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 32(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "vmulpd 64(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 96(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,64(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
                "vmulpd 128(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 160(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,128(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
                "vmulpd 192(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 224(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,192(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "vmulpd 256(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 288(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "vmulpd 320(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 352(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,320(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "vmulpd 384(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 416(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "vmulpd 448(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 480(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,448(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
                "vmulpd 512(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 544(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
                "vmulpd 576(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 608(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,576(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
                "vmulpd 640(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 672(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,640(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
                "vmulpd 704(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 736(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,704(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
                "vmulpd 768(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 800(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
                "vmulpd 832(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 864(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,832(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
                "vmulpd 896(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 928(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,896(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
                "vmulpd 960(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 992(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,960(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_vmovapd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovapd instruction
 */
static void asm_scale_vmovapd_3(param_t *params) __attribute__((noinline));
static void asm_scale_vmovapd_3(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
		"movddup (%%rax),%%xmm15;"
                "vinsertf128 $0, %%xmm15, %%ymm15, %%ymm15;"
                "vinsertf128 $1, %%xmm15, %%ymm15, %%ymm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_vmovapd_3;"
                ".align 64,0x0;"
                "_scale_loop_vmovapd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmulpd 0(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 32(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmulpd 64(%%r10),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovapd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovapd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "vmulpd 96(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmulpd 128(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmulpd 160(%%r10),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovapd %%ymm1,128(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm2,160(%%r12);"NOP(NOPCOUNT)
                "add $1056,%%r10;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "vmulpd 192(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 224(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmulpd 256(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "vmovapd %%ymm0,192(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,224(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovapd %%ymm2,256(%%r14);"NOP(NOPCOUNT)
                "add $1056,%%r12;"
                "vmulpd 288(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmulpd 320(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmulpd 352(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovapd %%ymm1,320(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm2,352(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmulpd 384(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 416(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmulpd 448(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovapd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovapd %%ymm2,448(%%r14);"NOP(NOPCOUNT)
                
                "vmulpd 480(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmulpd 512(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmulpd 544(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,480(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovapd %%ymm1,512(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm2,544(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmulpd 576(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 608(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmulpd 640(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovapd %%ymm0,576(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovapd %%ymm2,640(%%r14);"NOP(NOPCOUNT)
                
                "vmulpd 672(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmulpd 704(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmulpd 736(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovapd %%ymm1,704(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm2,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmulpd 768(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 800(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmulpd 832(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovapd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovapd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                
                "vmulpd 864(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmulpd 896(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmulpd 928(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmovapd %%ymm0,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovapd %%ymm1,896(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm2,928(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmulpd 960(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 992(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r13)
                "vmulpd 1024(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovapd %%ymm0,960(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,992(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r14)
                "vmovapd %%ymm2,1024(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_vmovapd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovapd instruction
 */
static void asm_scale_vmovapd_4(param_t *params) __attribute__((noinline));
static void asm_scale_vmovapd_4(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
		"movddup (%%rax),%%xmm15;"
                "vinsertf128 $0, %%xmm15, %%ymm15, %%ymm15;"
                "vinsertf128 $1, %%xmm15, %%ymm15, %%ymm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_vmovapd_4;"
                ".align 64,0x0;"
                "_scale_loop_vmovapd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmulpd 0(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 32(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmulpd 64(%%r10),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 96(%%r10),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovapd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovapd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmulpd 128(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 160(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmulpd 192(%%r10),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 224(%%r10),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovapd %%ymm0,128(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovapd %%ymm2,192(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmulpd 256(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 288(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmulpd 320(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 352(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovapd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovapd %%ymm2,320(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmulpd 384(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 416(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmulpd 448(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 480(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovapd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovapd %%ymm2,448(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmulpd 512(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 544(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmulpd 576(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 608(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovapd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovapd %%ymm2,576(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmulpd 640(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 672(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmulpd 704(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 736(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovapd %%ymm0,640(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovapd %%ymm2,704(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmulpd 768(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 800(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmulpd 832(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 864(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovapd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovapd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmulpd 896(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 928(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmulpd 960(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 992(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovapd %%ymm0,896(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovapd %%ymm2,960(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_vmovapd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovapd instruction
 */
static void asm_scale_vmovapd_8(param_t *params) __attribute__((noinline));
static void asm_scale_vmovapd_8(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
		"movddup (%%rax),%%xmm15;"
                "vinsertf128 $0, %%xmm15, %%ymm15, %%ymm15;"
                "vinsertf128 $1, %%xmm15, %%ymm15, %%ymm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_vmovapd_8;"
                ".align 64,0x0;"
                "_scale_loop_vmovapd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmulpd 0(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 32(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmulpd 64(%%r10),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 96(%%r10),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmulpd 128(%%r10),%%ymm15,%%ymm4;"NOP(NOPCOUNT)
                "vmulpd 160(%%r10),%%ymm15,%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmulpd 192(%%r10),%%ymm15,%%ymm6;"NOP(NOPCOUNT)
                "vmulpd 224(%%r10),%%ymm15,%%ymm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovapd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovapd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovapd %%ymm4,128(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovapd %%ymm6,192(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm7,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmulpd 256(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 288(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmulpd 320(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 352(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmulpd 384(%%r13),%%ymm15,%%ymm4;"NOP(NOPCOUNT)
                "vmulpd 416(%%r13),%%ymm15,%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmulpd 448(%%r13),%%ymm15,%%ymm6;"NOP(NOPCOUNT)
                "vmulpd 480(%%r13),%%ymm15,%%ymm7;"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovapd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovapd %%ymm2,320(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,352(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovapd %%ymm4,384(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovapd %%ymm6,448(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm7,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmulpd 512(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 544(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmulpd 576(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 608(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmulpd 640(%%r13),%%ymm15,%%ymm4;"NOP(NOPCOUNT)
                "vmulpd 672(%%r13),%%ymm15,%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmulpd 704(%%r13),%%ymm15,%%ymm6;"NOP(NOPCOUNT)
                "vmulpd 736(%%r13),%%ymm15,%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovapd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovapd %%ymm2,576(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovapd %%ymm4,640(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovapd %%ymm6,704(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm7,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmulpd 768(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 800(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmulpd 832(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 864(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmulpd 896(%%r13),%%ymm15,%%ymm4;"NOP(NOPCOUNT)
                "vmulpd 928(%%r13),%%ymm15,%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmulpd 960(%%r13),%%ymm15,%%ymm6;"NOP(NOPCOUNT)
                "vmulpd 992(%%r13),%%ymm15,%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovapd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovapd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovapd %%ymm4,896(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovapd %%ymm6,960(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm7,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_vmovapd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movupd instruction
 */
static void asm_scale_movupd_1(param_t *params) __attribute__((noinline));
static void asm_scale_movupd_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
                "movddup (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movupd_1;"
                ".align 64,0x0;"
                "_scale_loop_movupd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movupd 0(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movupd 16(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,16(%%r12);"NOP(NOPCOUNT)
                "movupd 32(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,32(%%r12);"NOP(NOPCOUNT)
                "movupd 48(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movupd 64(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,64(%%r12);"NOP(NOPCOUNT)
                "movupd 80(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,80(%%r12);"NOP(NOPCOUNT)
                "movupd 96(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,96(%%r12);"NOP(NOPCOUNT)
                "movupd 112(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movupd 128(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movupd 144(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,144(%%r14);"NOP(NOPCOUNT)
                "movupd 160(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,160(%%r14);"NOP(NOPCOUNT)
                "movupd 176(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movupd 192(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movupd 208(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,208(%%r14);"NOP(NOPCOUNT)
                "movupd 224(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,224(%%r14);"NOP(NOPCOUNT)
                "movupd 240(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movupd 256(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movupd 272(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,272(%%r14);"NOP(NOPCOUNT)
                "movupd 288(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,288(%%r14);"NOP(NOPCOUNT)
                "movupd 304(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movupd 320(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,320(%%r14);"NOP(NOPCOUNT)
                "movupd 336(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,336(%%r14);"NOP(NOPCOUNT)
                "movupd 352(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,352(%%r14);"NOP(NOPCOUNT)
                "movupd 368(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movupd 384(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movupd 400(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,400(%%r14);"NOP(NOPCOUNT)
                "movupd 416(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,416(%%r14);"NOP(NOPCOUNT)
                "movupd 432(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movupd 448(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,448(%%r14);"NOP(NOPCOUNT)
                "movupd 464(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,464(%%r14);"NOP(NOPCOUNT)
                "movupd 480(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,480(%%r14);"NOP(NOPCOUNT)
                "movupd 496(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movupd %%xmm0,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_movupd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movupd instruction
 */
static void asm_scale_movupd_2(param_t *params) __attribute__((noinline));
static void asm_scale_movupd_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
                "movddup (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movupd_2;"
                ".align 64,0x0;"
                "_scale_loop_movupd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movupd 0(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 16(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movupd 32(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 48(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,32(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm1,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movupd 64(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 80(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,64(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm1,80(%%r12);"NOP(NOPCOUNT)
                "movupd 96(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 112(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,96(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm1,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movupd 128(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 144(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movupd 160(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 176(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,160(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movupd 192(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 208(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movupd 224(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 240(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,224(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movupd 256(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 272(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movupd 288(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 304(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,288(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movupd 320(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 336(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,320(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,336(%%r14);"NOP(NOPCOUNT)
                "movupd 352(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 368(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,352(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movupd 384(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 400(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movupd 416(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 432(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,416(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movupd 448(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 464(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,448(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,464(%%r14);"NOP(NOPCOUNT)
                "movupd 480(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 496(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm0,480(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_movupd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movupd instruction
 */
static void asm_scale_movupd_3(param_t *params) __attribute__((noinline));
static void asm_scale_movupd_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
                "movddup (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movupd_3;"
                ".align 64,0x0;"
                "_scale_loop_movupd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movupd 0(%%r10), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 16(%%r10), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 32(%%r10), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movupd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "movupd 48(%%r10), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movupd 64(%%r10), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 80(%%r10), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm0,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movupd %%xmm1,64(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm2,80(%%r12);"NOP(NOPCOUNT)
                "add $528,%%r10;"
                "movupd 96(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 112(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r13)
                "movupd 128(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm0,96(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,112(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movupd %%xmm2,128(%%r14);"NOP(NOPCOUNT)
                "add $528,%%r12;"
                "movupd 144(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 160(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 176(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm0,144(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,160(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,176(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,192,r13)
                "movupd 192(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 208(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 224(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movupd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,224(%%r14);"NOP(NOPCOUNT)
                
                "movupd 240(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "movupd 256(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 272(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm0,240(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movupd %%xmm1,256(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,272(%%r14);"NOP(NOPCOUNT)
                
                "movupd 288(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 304(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movupd 320(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm0,288(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movupd %%xmm2,320(%%r14);"NOP(NOPCOUNT)
                
                "movupd 336(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 352(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 368(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm0,336(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,352(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movupd 384(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 400(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 416(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movupd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                
                "movupd 432(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movupd 448(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 464(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm0,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movupd %%xmm1,448(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,464(%%r14);"NOP(NOPCOUNT)
                
                "movupd 480(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 496(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "movupd 512(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm0,480(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,496(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "movupd %%xmm2,512(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_movupd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movupd instruction
 */
static void asm_scale_movupd_4(param_t *params) __attribute__((noinline));
static void asm_scale_movupd_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
                "movddup (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movupd_4;"
                ".align 64,0x0;"
                "_scale_loop_movupd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movupd 0(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 16(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 32(%%r10),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd 48(%%r10),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movupd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)
                "movupd 64(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 80(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 96(%%r10),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd 112(%%r10),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movupd %%xmm0,64(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm1,80(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm2,96(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm3,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movupd 128(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 144(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 160(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd 176(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movupd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,160(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "movupd 192(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 208(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 224(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd 240(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movupd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,224(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movupd 256(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 272(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 288(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd 304(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movupd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,288(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)
                "movupd 320(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 336(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 352(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd 368(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movupd %%xmm0,320(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,336(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,352(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movupd 384(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 400(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 416(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd 432(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movupd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)
                "movupd 448(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 464(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 480(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd 496(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movupd %%xmm0,448(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,464(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,480(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_movupd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movupd instruction
 */
static void asm_scale_movupd_8(param_t *params) __attribute__((noinline));
static void asm_scale_movupd_8(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
                "movddup (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movupd_8;"
                ".align 64,0x0;"
                "_scale_loop_movupd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movupd 0(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 16(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 32(%%r10),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd 48(%%r10),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movupd 64(%%r10),%%xmm4;mulpd %%xmm15,%%xmm4;"NOP(NOPCOUNT)
                "movupd 80(%%r10),%%xmm5;mulpd %%xmm15,%%xmm5;"NOP(NOPCOUNT)
                "movupd 96(%%r10),%%xmm6;mulpd %%xmm15,%%xmm6;"NOP(NOPCOUNT)
                "movupd 112(%%r10),%%xmm7;mulpd %%xmm15,%%xmm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "movupd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movupd %%xmm4,64(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm5,80(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm6,96(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm7,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movupd 128(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 144(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 160(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd 176(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r13)
                "movupd 192(%%r13),%%xmm4;mulpd %%xmm15,%%xmm4;"NOP(NOPCOUNT)
                "movupd 208(%%r13),%%xmm5;mulpd %%xmm15,%%xmm5;"NOP(NOPCOUNT)
                "movupd 224(%%r13),%%xmm6;mulpd %%xmm15,%%xmm6;"NOP(NOPCOUNT)
                "movupd 240(%%r13),%%xmm7;mulpd %%xmm15,%%xmm7;"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,128,r14)
                "movupd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,160(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,176(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movupd %%xmm4,192(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,208(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm6,224(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm7,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movupd 256(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 272(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 288(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd 304(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movupd 320(%%r13),%%xmm4;mulpd %%xmm15,%%xmm4;"NOP(NOPCOUNT)
                "movupd 336(%%r13),%%xmm5;mulpd %%xmm15,%%xmm5;"NOP(NOPCOUNT)
                "movupd 352(%%r13),%%xmm6;mulpd %%xmm15,%%xmm6;"NOP(NOPCOUNT)
                "movupd 368(%%r13),%%xmm7;mulpd %%xmm15,%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r14)
                "movupd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,288(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movupd %%xmm4,320(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,336(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm6,352(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm7,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movupd 384(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movupd 400(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movupd 416(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movupd 432(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movupd 448(%%r13),%%xmm4;mulpd %%xmm15,%%xmm4;"NOP(NOPCOUNT)
                "movupd 464(%%r13),%%xmm5;mulpd %%xmm15,%%xmm5;"NOP(NOPCOUNT)
                "movupd 480(%%r13),%%xmm6;mulpd %%xmm15,%%xmm6;"NOP(NOPCOUNT)
                "movupd 496(%%r13),%%xmm7;mulpd %%xmm15,%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r14)
                "movupd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movupd %%xmm4,448(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,464(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm6,480(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm7,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_movupd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovupd instruction
 */
static void asm_scale_vmovupd_1(param_t *params) __attribute__((noinline));
static void asm_scale_vmovupd_1(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
		"movddup (%%rax),%%xmm15;"
                "vinsertf128 $0, %%xmm15, %%ymm15, %%ymm15;"
                "vinsertf128 $1, %%xmm15, %%ymm15, %%ymm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_vmovupd_1;"
                ".align 64,0x0;"
                "_scale_loop_vmovupd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
		"vmulpd 0(%%r10),%%ymm15,%%ymm0;vmovupd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
		"vmulpd 32(%%r10),%%ymm15,%%ymm0;vmovupd %%ymm0,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
		"vmulpd 64(%%r10),%%ymm15,%%ymm0;vmovupd %%ymm0,64(%%r12);"NOP(NOPCOUNT)
		"vmulpd 96(%%r10),%%ymm15,%%ymm0;vmovupd %%ymm0,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
		"vmulpd 128(%%r10),%%ymm15,%%ymm0;vmovupd %%ymm0,128(%%r12);"NOP(NOPCOUNT)
		"vmulpd 160(%%r10),%%ymm15,%%ymm0;vmovupd %%ymm0,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
		"vmulpd 192(%%r10),%%ymm15,%%ymm0;vmovupd %%ymm0,192(%%r12);"NOP(NOPCOUNT)
		"vmulpd 224(%%r10),%%ymm15,%%ymm0;vmovupd %%ymm0,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
		"vmulpd 256(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
		"vmulpd 288(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
		"vmulpd 320(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,320(%%r14);"NOP(NOPCOUNT)
		"vmulpd 352(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
		"vmulpd 384(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
		"vmulpd 416(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
		"vmulpd 448(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,448(%%r14);"NOP(NOPCOUNT)
		"vmulpd 480(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
		"vmulpd 512(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
		"vmulpd 544(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
		"vmulpd 576(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,576(%%r14);"NOP(NOPCOUNT)
		"vmulpd 608(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
		"vmulpd 640(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,640(%%r14);"NOP(NOPCOUNT)
		"vmulpd 672(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
		"vmulpd 704(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,704(%%r14);"NOP(NOPCOUNT)
		"vmulpd 736(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
		"vmulpd 768(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
		"vmulpd 800(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
		"vmulpd 832(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,832(%%r14);"NOP(NOPCOUNT)
		"vmulpd 864(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
		"vmulpd 896(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,896(%%r14);"NOP(NOPCOUNT)
		"vmulpd 928(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
		"vmulpd 960(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,960(%%r14);"NOP(NOPCOUNT)
		"vmulpd 992(%%r13),%%ymm15,%%ymm0;vmovupd %%ymm0,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_vmovupd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovupd instruction
 */
static void asm_scale_vmovupd_2(param_t *params) __attribute__((noinline));
static void asm_scale_vmovupd_2(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
		"movddup (%%rax),%%xmm15;"
                "vinsertf128 $0, %%xmm15, %%ymm15, %%ymm15;"
                "vinsertf128 $1, %%xmm15, %%ymm15, %%ymm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_vmovupd_2;"
                ".align 64,0x0;"
                "_scale_loop_vmovupd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "vmulpd 0(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 32(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "vmulpd 64(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 96(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,64(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
                "vmulpd 128(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 160(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,128(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
                "vmulpd 192(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 224(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,192(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "vmulpd 256(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 288(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "vmulpd 320(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 352(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,320(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "vmulpd 384(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 416(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "vmulpd 448(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 480(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,448(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
                "vmulpd 512(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 544(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
                "vmulpd 576(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 608(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,576(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
                "vmulpd 640(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 672(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,640(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
                "vmulpd 704(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 736(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,704(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
                "vmulpd 768(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 800(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
                "vmulpd 832(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 864(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,832(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
                "vmulpd 896(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 928(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,896(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
                "vmulpd 960(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 992(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,960(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_vmovupd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovupd instruction
 */
static void asm_scale_vmovupd_3(param_t *params) __attribute__((noinline));
static void asm_scale_vmovupd_3(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
		"movddup (%%rax),%%xmm15;"
                "vinsertf128 $0, %%xmm15, %%ymm15, %%ymm15;"
                "vinsertf128 $1, %%xmm15, %%ymm15, %%ymm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_vmovupd_3;"
                ".align 64,0x0;"
                "_scale_loop_vmovupd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmulpd 0(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 32(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmulpd 64(%%r10),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovupd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovupd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "vmulpd 96(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmulpd 128(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmulpd 160(%%r10),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovupd %%ymm1,128(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm2,160(%%r12);"NOP(NOPCOUNT)
                "add $1056,%%r10;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "vmulpd 192(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 224(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmulpd 256(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "vmovupd %%ymm0,192(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,224(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovupd %%ymm2,256(%%r14);"NOP(NOPCOUNT)
                "add $1056,%%r12;"
                "vmulpd 288(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmulpd 320(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmulpd 352(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovupd %%ymm1,320(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm2,352(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmulpd 384(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 416(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmulpd 448(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovupd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovupd %%ymm2,448(%%r14);"NOP(NOPCOUNT)
                
                "vmulpd 480(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmulpd 512(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmulpd 544(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,480(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovupd %%ymm1,512(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm2,544(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmulpd 576(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 608(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmulpd 640(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovupd %%ymm0,576(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovupd %%ymm2,640(%%r14);"NOP(NOPCOUNT)
                
                "vmulpd 672(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmulpd 704(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmulpd 736(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovupd %%ymm1,704(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm2,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmulpd 768(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 800(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmulpd 832(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovupd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovupd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                
                "vmulpd 864(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmulpd 896(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmulpd 928(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmovupd %%ymm0,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovupd %%ymm1,896(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm2,928(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmulpd 960(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 992(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r13)
                "vmulpd 1024(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovupd %%ymm0,960(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,992(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r14)
                "vmovupd %%ymm2,1024(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_vmovupd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovupd instruction
 */
static void asm_scale_vmovupd_4(param_t *params) __attribute__((noinline));
static void asm_scale_vmovupd_4(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
		"movddup (%%rax),%%xmm15;"
                "vinsertf128 $0, %%xmm15, %%ymm15, %%ymm15;"
                "vinsertf128 $1, %%xmm15, %%ymm15, %%ymm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_vmovupd_4;"
                ".align 64,0x0;"
                "_scale_loop_vmovupd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmulpd 0(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 32(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmulpd 64(%%r10),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 96(%%r10),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovupd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovupd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmulpd 128(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 160(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmulpd 192(%%r10),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 224(%%r10),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovupd %%ymm0,128(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovupd %%ymm2,192(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmulpd 256(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 288(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmulpd 320(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 352(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovupd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovupd %%ymm2,320(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmulpd 384(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 416(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmulpd 448(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 480(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovupd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovupd %%ymm2,448(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmulpd 512(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 544(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmulpd 576(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 608(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovupd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovupd %%ymm2,576(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmulpd 640(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 672(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmulpd 704(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 736(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovupd %%ymm0,640(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovupd %%ymm2,704(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmulpd 768(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 800(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmulpd 832(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 864(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovupd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovupd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmulpd 896(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 928(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmulpd 960(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 992(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovupd %%ymm0,896(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovupd %%ymm2,960(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_vmovupd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovupd instruction
 */
static void asm_scale_vmovupd_8(param_t *params) __attribute__((noinline));
static void asm_scale_vmovupd_8(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
		"movddup (%%rax),%%xmm15;"
                "vinsertf128 $0, %%xmm15, %%ymm15, %%ymm15;"
                "vinsertf128 $1, %%xmm15, %%ymm15, %%ymm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_vmovupd_8;"
                ".align 64,0x0;"
                "_scale_loop_vmovupd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmulpd 0(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 32(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmulpd 64(%%r10),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 96(%%r10),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmulpd 128(%%r10),%%ymm15,%%ymm4;"NOP(NOPCOUNT)
                "vmulpd 160(%%r10),%%ymm15,%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmulpd 192(%%r10),%%ymm15,%%ymm6;"NOP(NOPCOUNT)
                "vmulpd 224(%%r10),%%ymm15,%%ymm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovupd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovupd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovupd %%ymm4,128(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovupd %%ymm6,192(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm7,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmulpd 256(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 288(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmulpd 320(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 352(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmulpd 384(%%r13),%%ymm15,%%ymm4;"NOP(NOPCOUNT)
                "vmulpd 416(%%r13),%%ymm15,%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmulpd 448(%%r13),%%ymm15,%%ymm6;"NOP(NOPCOUNT)
                "vmulpd 480(%%r13),%%ymm15,%%ymm7;"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovupd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovupd %%ymm2,320(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,352(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovupd %%ymm4,384(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovupd %%ymm6,448(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm7,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmulpd 512(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 544(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmulpd 576(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 608(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmulpd 640(%%r13),%%ymm15,%%ymm4;"NOP(NOPCOUNT)
                "vmulpd 672(%%r13),%%ymm15,%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmulpd 704(%%r13),%%ymm15,%%ymm6;"NOP(NOPCOUNT)
                "vmulpd 736(%%r13),%%ymm15,%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovupd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovupd %%ymm2,576(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovupd %%ymm4,640(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovupd %%ymm6,704(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm7,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmulpd 768(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 800(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmulpd 832(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 864(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmulpd 896(%%r13),%%ymm15,%%ymm4;"NOP(NOPCOUNT)
                "vmulpd 928(%%r13),%%ymm15,%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmulpd 960(%%r13),%%ymm15,%%ymm6;"NOP(NOPCOUNT)
                "vmulpd 992(%%r13),%%ymm15,%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovupd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovupd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovupd %%ymm4,896(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovupd %%ymm6,960(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm7,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_vmovupd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov instruction
 */
static void asm_scale_mov_1(param_t *params) __attribute__((noinline));
static void asm_scale_mov_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"
                "movq (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_mov_1;"
                ".align 64,0x0;"
                "_scale_loop_mov_1:"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "movq 0(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,0(%%rdi);"NOP(NOPCOUNT)
                "movq 8(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,8(%%rdi);"NOP(NOPCOUNT)
                "movq 16(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,16(%%rdi);"NOP(NOPCOUNT)
                "movq 24(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,24(%%rdi);"NOP(NOPCOUNT)
                "movq 32(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,32(%%rdi);"NOP(NOPCOUNT)
                "movq 40(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,40(%%rdi);"NOP(NOPCOUNT)
                "movq 48(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,48(%%rdi);"NOP(NOPCOUNT)
                "movq 56(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "movq 64(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,64(%%rdi);"NOP(NOPCOUNT)
                "movq 72(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,72(%%rdi);"NOP(NOPCOUNT)
                "movq 80(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,80(%%rdi);"NOP(NOPCOUNT)
                "movq 88(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,88(%%rdi);"NOP(NOPCOUNT)
                "movq 96(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,96(%%rdi);"NOP(NOPCOUNT)
                "movq 104(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,104(%%rdi);"NOP(NOPCOUNT)
                "movq 112(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,112(%%rdi);"NOP(NOPCOUNT)
                "movq 120(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,120(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _scale_loop_mov_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov instruction
 */
static void asm_scale_mov_2(param_t *params) __attribute__((noinline));
static void asm_scale_mov_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"
                "movq (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_mov_2;"
                ".align 64,0x0;"
                "_scale_loop_mov_2:"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "movq 0(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 8(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,0(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,8(%%rdi);"NOP(NOPCOUNT)
                "movq 16(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 24(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,16(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,24(%%rdi);"NOP(NOPCOUNT)
                "movq 32(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 40(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,32(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,40(%%rdi);"NOP(NOPCOUNT)
                "movq 48(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 56(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,48(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "movq 64(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 72(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,64(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,72(%%rdi);"NOP(NOPCOUNT)
                "movq 80(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 88(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,80(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,88(%%rdi);"NOP(NOPCOUNT)
                "movq 96(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 104(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,96(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,104(%%rdi);"NOP(NOPCOUNT)
                "movq 112(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 120(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,112(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)PREFETCH(LINE_PREFETCH,128,rdi)
                "movq 128(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 136(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,128(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,136(%%rdi);"NOP(NOPCOUNT)
                "movq 144(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 152(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,144(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,152(%%rdi);"NOP(NOPCOUNT)
                "movq 160(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 168(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,160(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,168(%%rdi);"NOP(NOPCOUNT)
                "movq 176(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 184(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,176(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)PREFETCH(LINE_PREFETCH,192,rdi)
                "movq 192(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 200(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,192(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,200(%%rdi);"NOP(NOPCOUNT)
                "movq 208(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 216(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,208(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,216(%%rdi);"NOP(NOPCOUNT)
                "movq 224(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 232(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,224(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,232(%%rdi);"NOP(NOPCOUNT)
                "movq 240(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 248(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,240(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _scale_loop_mov_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov instruction
 */
static void asm_scale_mov_3(param_t *params) __attribute__((noinline));
static void asm_scale_mov_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"
                "movq (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_mov_3;"
                ".align 64,0x0;"
                "_scale_loop_mov_3:"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "movq 0(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 8(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 16(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                PREFETCH(LINE_PREFETCH,0,rdi)
                "movq %%xmm0, 0(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 8(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 16(%%rdi);"NOP(NOPCOUNT)
                "movq 24(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 32(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 40(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 24(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 32(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 40(%%rdi);"NOP(NOPCOUNT)
                "movq 48(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 56(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                PREFETCH(LINE_PREFETCH,64,rsi)
                "movq 64(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 48(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rdi)
                "movq %%xmm2, 64(%%rdi);"NOP(NOPCOUNT)
                "movq 72(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 80(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 88(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 72(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 80(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 88(%%rdi);"NOP(NOPCOUNT)
                "movq 96(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 104(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 112(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 96(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 104(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 112(%%rdi);"NOP(NOPCOUNT)
                "movq 120(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                PREFETCH(LINE_PREFETCH,128,rsi)
                "movq 128(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 136(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rdi)
                "movq %%xmm1, 128(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 136(%%rdi);"NOP(NOPCOUNT)
                "movq 144(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 152(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 160(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 144(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 152(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 160(%%rdi);"NOP(NOPCOUNT)
                "movq 168(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 176(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 184(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 168(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 176(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "movq 192(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 200(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 208(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                PREFETCH(LINE_PREFETCH,192,rdi)
                "movq %%xmm0, 192(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 200(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 208(%%rdi);"NOP(NOPCOUNT)
                "movq 216(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 224(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 232(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 216(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 224(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 232(%%rdi);"NOP(NOPCOUNT)
                "movq 240(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 248(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                PREFETCH(LINE_PREFETCH,256,rsi)
                "movq 256(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 240(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 248(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rdi)
                "movq %%xmm2, 256(%%rdi);"NOP(NOPCOUNT)
                "add $264,%%rsi;"
                "add $264,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _scale_loop_mov_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov instruction
 */
static void asm_scale_mov_4(param_t *params) __attribute__((noinline));
static void asm_scale_mov_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"
                "movq (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_mov_4;"
                ".align 64,0x0;"
                "_scale_loop_mov_4:"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "movq 0(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 8(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 16(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 24(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                PREFETCH(LINE_PREFETCH,0,rdi)
                "movq %%xmm0,0(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,8(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2,16(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3,24(%%rdi);"NOP(NOPCOUNT)
                "movq 32(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 40(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 48(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 56(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                "movq %%xmm0,32(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,40(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2,48(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)
                "movq 64(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 72(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 80(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 88(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                PREFETCH(LINE_PREFETCH,64,rdi)
                "movq %%xmm0,64(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,72(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2,80(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3,88(%%rdi);"NOP(NOPCOUNT)
                "movq 96(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 104(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 112(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 120(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                "movq %%xmm0,96(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,104(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2,112(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)
                "movq 128(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 136(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 144(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 152(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                PREFETCH(LINE_PREFETCH,128,rdi)
                "movq %%xmm0,128(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,136(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2,144(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3,152(%%rdi);"NOP(NOPCOUNT)
                "movq 160(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 168(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 176(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 184(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                "movq %%xmm0,160(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,168(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2,176(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "movq 192(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 200(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 208(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 216(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                PREFETCH(LINE_PREFETCH,192,rdi)
                "movq %%xmm0,192(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,200(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2,208(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3,216(%%rdi);"NOP(NOPCOUNT)
                "movq 224(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 232(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 240(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 248(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                "movq %%xmm0,224(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,232(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2,240(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _scale_loop_mov_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov_clflush instruction
 */
static void asm_scale_mov_clflush_1(param_t *params) __attribute__((noinline));
static void asm_scale_mov_clflush_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"
                "movq (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_mov_clflush_1;"
                ".align 64,0x0;"
                "_scale_loop_mov_clflush_1:"
                "clflush -384(%%rdi);""clflush -320(%%rdi);"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "movq 0(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,0(%%rdi);"NOP(NOPCOUNT)
                "movq 8(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,8(%%rdi);"NOP(NOPCOUNT)
                "movq 16(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,16(%%rdi);"NOP(NOPCOUNT)
                "movq 24(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,24(%%rdi);"NOP(NOPCOUNT)
                "movq 32(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,32(%%rdi);"NOP(NOPCOUNT)
                "movq 40(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,40(%%rdi);"NOP(NOPCOUNT)
                "movq 48(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,48(%%rdi);"NOP(NOPCOUNT)
                "movq 56(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "movq 64(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,64(%%rdi);"NOP(NOPCOUNT)
                "movq 72(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,72(%%rdi);"NOP(NOPCOUNT)
                "movq 80(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,80(%%rdi);"NOP(NOPCOUNT)
                "movq 88(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,88(%%rdi);"NOP(NOPCOUNT)
                "movq 96(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,96(%%rdi);"NOP(NOPCOUNT)
                "movq 104(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,104(%%rdi);"NOP(NOPCOUNT)
                "movq 112(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,112(%%rdi);"NOP(NOPCOUNT)
                "movq 120(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,120(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _scale_loop_mov_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov_clflush instruction
 */
static void asm_scale_mov_clflush_2(param_t *params) __attribute__((noinline));
static void asm_scale_mov_clflush_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"
                "movq (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_mov_clflush_2;"
                ".align 64,0x0;"
                "_scale_loop_mov_clflush_2:"
                "clflush -384(%%rdi);""clflush -320(%%rdi);"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "movq 0(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 8(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,0(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,8(%%rdi);"NOP(NOPCOUNT)
                "movq 16(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 24(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,16(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,24(%%rdi);"NOP(NOPCOUNT)
                "movq 32(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 40(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,32(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,40(%%rdi);"NOP(NOPCOUNT)
                "movq 48(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 56(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,48(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "movq 64(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 72(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,64(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,72(%%rdi);"NOP(NOPCOUNT)
                "movq 80(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 88(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,80(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,88(%%rdi);"NOP(NOPCOUNT)
                "movq 96(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 104(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,96(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,104(%%rdi);"NOP(NOPCOUNT)
                "movq 112(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 120(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,112(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)PREFETCH(LINE_PREFETCH,128,rdi)
                "movq 128(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 136(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,128(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,136(%%rdi);"NOP(NOPCOUNT)
                "movq 144(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 152(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,144(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,152(%%rdi);"NOP(NOPCOUNT)
                "movq 160(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 168(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,160(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,168(%%rdi);"NOP(NOPCOUNT)
                "movq 176(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 184(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,176(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)PREFETCH(LINE_PREFETCH,192,rdi)
                "movq 192(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 200(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,192(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,200(%%rdi);"NOP(NOPCOUNT)
                "movq 208(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 216(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,208(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,216(%%rdi);"NOP(NOPCOUNT)
                "movq 224(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 232(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,224(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,232(%%rdi);"NOP(NOPCOUNT)
                "movq 240(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 248(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,240(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _scale_loop_mov_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov_clflush instruction
 */
static void asm_scale_mov_clflush_3(param_t *params) __attribute__((noinline));
static void asm_scale_mov_clflush_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"
                "movq (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_mov_clflush_3;"
                ".align 64,0x0;"
                "_scale_loop_mov_clflush_3:"
                "clflush -448(%%rdi);clflush -384(%%rdi);""clflush -320(%%rdi);"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "movq 0(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 8(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 16(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                PREFETCH(LINE_PREFETCH,0,rdi)
                "movq %%xmm0, 0(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 8(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 16(%%rdi);"NOP(NOPCOUNT)
                "movq 24(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 32(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 40(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 24(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 32(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 40(%%rdi);"NOP(NOPCOUNT)
                "movq 48(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 56(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                PREFETCH(LINE_PREFETCH,64,rsi)
                "movq 64(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 48(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rdi)
                "movq %%xmm2, 64(%%rdi);"NOP(NOPCOUNT)
                "movq 72(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 80(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 88(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 72(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 80(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 88(%%rdi);"NOP(NOPCOUNT)
                "movq 96(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 104(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 112(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 96(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 104(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 112(%%rdi);"NOP(NOPCOUNT)
                "movq 120(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                PREFETCH(LINE_PREFETCH,128,rsi)
                "movq 128(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 136(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rdi)
                "movq %%xmm1, 128(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 136(%%rdi);"NOP(NOPCOUNT)
                "movq 144(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 152(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 160(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 144(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 152(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 160(%%rdi);"NOP(NOPCOUNT)
                "movq 168(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 176(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 184(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 168(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 176(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "movq 192(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 200(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 208(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                PREFETCH(LINE_PREFETCH,192,rdi)
                "movq %%xmm0, 192(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 200(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 208(%%rdi);"NOP(NOPCOUNT)
                "movq 216(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 224(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 232(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 216(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 224(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, 232(%%rdi);"NOP(NOPCOUNT)
                "movq 240(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 248(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                PREFETCH(LINE_PREFETCH,256,rsi)
                "movq 256(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, 240(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, 248(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rdi)
                "movq %%xmm2, 256(%%rdi);"NOP(NOPCOUNT)
                "add $264,%%rsi;"
                "add $264,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _scale_loop_mov_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov_clflush instruction
 */
static void asm_scale_mov_clflush_4(param_t *params) __attribute__((noinline));
static void asm_scale_mov_clflush_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"
                "movq (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_mov_clflush_4;"
                ".align 64,0x0;"
                "_scale_loop_mov_clflush_4:"
                "clflush -384(%%rdi);""clflush -320(%%rdi);"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "movq 0(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 8(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 16(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 24(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                PREFETCH(LINE_PREFETCH,0,rdi)
                "movq %%xmm0,0(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,8(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2,16(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3,24(%%rdi);"NOP(NOPCOUNT)
                "movq 32(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 40(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 48(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 56(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                "movq %%xmm0,32(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,40(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2,48(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)
                "movq 64(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 72(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 80(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 88(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                PREFETCH(LINE_PREFETCH,64,rdi)
                "movq %%xmm0,64(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,72(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2,80(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3,88(%%rdi);"NOP(NOPCOUNT)
                "movq 96(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 104(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 112(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 120(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                "movq %%xmm0,96(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,104(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2,112(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)
                "movq 128(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 136(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 144(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 152(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                PREFETCH(LINE_PREFETCH,128,rdi)
                "movq %%xmm0,128(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,136(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2,144(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3,152(%%rdi);"NOP(NOPCOUNT)
                "movq 160(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 168(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 176(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 184(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                "movq %%xmm0,160(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,168(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2,176(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "movq 192(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 200(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 208(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 216(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                PREFETCH(LINE_PREFETCH,192,rdi)
                "movq %%xmm0,192(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,200(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2,208(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3,216(%%rdi);"NOP(NOPCOUNT)
                "movq 224(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 232(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 240(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 248(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                "movq %%xmm0,224(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,232(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2,240(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _scale_loop_mov_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movnti instruction
 */
static void asm_scale_movnti_1(param_t *params) __attribute__((noinline));
static void asm_scale_movnti_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"
                "movq (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movnti_1;"
                ".align 64,0x0;"
                "_scale_loop_movnti_1:"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "movq 0(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,%%r8; movnti %%r8,0(%%rdi);"NOP(NOPCOUNT)
                "movq 8(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,%%r8; movnti %%r8,8(%%rdi);"NOP(NOPCOUNT)
                "movq 16(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,%%r8; movnti %%r8,16(%%rdi);"NOP(NOPCOUNT)
                "movq 24(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,%%r8; movnti %%r8,24(%%rdi);"NOP(NOPCOUNT)
                "movq 32(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,%%r8; movnti %%r8,32(%%rdi);"NOP(NOPCOUNT)
                "movq 40(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,%%r8; movnti %%r8,40(%%rdi);"NOP(NOPCOUNT)
                "movq 48(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,%%r8; movnti %%r8,48(%%rdi);"NOP(NOPCOUNT)
                "movq 56(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,%%r8; movnti %%r8,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "movq 64(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,%%r8; movnti %%r8,64(%%rdi);"NOP(NOPCOUNT)
                "movq 72(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,%%r8; movnti %%r8,72(%%rdi);"NOP(NOPCOUNT)
                "movq 80(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,%%r8; movnti %%r8,80(%%rdi);"NOP(NOPCOUNT)
                "movq 88(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,%%r8; movnti %%r8,88(%%rdi);"NOP(NOPCOUNT)
                "movq 96(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,%%r8; movnti %%r8,96(%%rdi);"NOP(NOPCOUNT)
                "movq 104(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,%%r8; movnti %%r8,104(%%rdi);"NOP(NOPCOUNT)
                "movq 112(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,%%r8; movnti %%r8,112(%%rdi);"NOP(NOPCOUNT)
                "movq 120(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;movq %%xmm0,%%r8; movnti %%r8,120(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _scale_loop_movnti_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movnti instruction
 */
static void asm_scale_movnti_2(param_t *params) __attribute__((noinline));
static void asm_scale_movnti_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"
                "movq (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movnti_2;"
                ".align 64,0x0;"
                "_scale_loop_movnti_2:"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "movq 0(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 8(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,%%r8; movnti %%r8,0(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,%%r9; movnti %%r9,8(%%rdi);"NOP(NOPCOUNT)
                "movq 16(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 24(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,%%r8; movnti %%r8,16(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,%%r9; movnti %%r9,24(%%rdi);"NOP(NOPCOUNT)
                "movq 32(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 40(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,%%r8; movnti %%r8,32(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,%%r9; movnti %%r9,40(%%rdi);"NOP(NOPCOUNT)
                "movq 48(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 56(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,%%r8; movnti %%r8,48(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,%%r9; movnti %%r9,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "movq 64(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 72(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,%%r8; movnti %%r8,64(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,%%r9; movnti %%r9,72(%%rdi);"NOP(NOPCOUNT)
                "movq 80(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 88(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,%%r8; movnti %%r8,80(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,%%r9; movnti %%r9,88(%%rdi);"NOP(NOPCOUNT)
                "movq 96(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 104(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,%%r8; movnti %%r8,96(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,%%r9; movnti %%r9,104(%%rdi);"NOP(NOPCOUNT)
                "movq 112(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 120(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,%%r8; movnti %%r8,112(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,%%r9; movnti %%r9,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)PREFETCH(LINE_PREFETCH,128,rdi)
                "movq 128(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 136(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,%%r8; movnti %%r8,128(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,%%r9; movnti %%r9,136(%%rdi);"NOP(NOPCOUNT)
                "movq 144(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 152(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,%%r8; movnti %%r8,144(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,%%r9; movnti %%r9,152(%%rdi);"NOP(NOPCOUNT)
                "movq 160(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 168(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,%%r8; movnti %%r8,160(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,%%r9; movnti %%r9,168(%%rdi);"NOP(NOPCOUNT)
                "movq 176(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 184(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,%%r8; movnti %%r8,176(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,%%r9; movnti %%r9,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)PREFETCH(LINE_PREFETCH,192,rdi)
                "movq 192(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 200(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,%%r8; movnti %%r8,192(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,%%r9; movnti %%r9,200(%%rdi);"NOP(NOPCOUNT)
                "movq 208(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 216(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,%%r8; movnti %%r8,208(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,%%r9; movnti %%r9,216(%%rdi);"NOP(NOPCOUNT)
                "movq 224(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 232(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,%%r8; movnti %%r8,224(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,%%r9; movnti %%r9,232(%%rdi);"NOP(NOPCOUNT)
                "movq 240(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 248(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq %%xmm0,%%r8; movnti %%r8,240(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1,%%r9; movnti %%r9,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _scale_loop_movnti_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movnti instruction
 */
static void asm_scale_movnti_3(param_t *params) __attribute__((noinline));
static void asm_scale_movnti_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"
                "movq (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movnti_3;"
                ".align 64,0x0;"
                "_scale_loop_movnti_3:"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "movq 0(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 8(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 16(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                PREFETCH(LINE_PREFETCH,0,rdi)
                "movq %%xmm0, %%r8; movnti %%r8, 0(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9, 8(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, %%r10; movnti %%r10, 16(%%rdi);"NOP(NOPCOUNT)
                "movq 24(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 32(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 40(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, %%r8; movnti %%r8, 24(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9, 32(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, %%r10; movnti %%r10, 40(%%rdi);"NOP(NOPCOUNT)
                "movq 48(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 56(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                PREFETCH(LINE_PREFETCH,64,rsi)
                "movq 64(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, %%r8; movnti %%r8, 48(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9, 56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rdi)
                "movq %%xmm2, %%r10; movnti %%r10, 64(%%rdi);"NOP(NOPCOUNT)
                "movq 72(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 80(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 88(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, %%r8; movnti %%r8, 72(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9, 80(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, %%r10; movnti %%r10, 88(%%rdi);"NOP(NOPCOUNT)
                "movq 96(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 104(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 112(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, %%r8; movnti %%r8, 96(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9, 104(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, %%r10; movnti %%r10, 112(%%rdi);"NOP(NOPCOUNT)
                "movq 120(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                PREFETCH(LINE_PREFETCH,128,rsi)
                "movq 128(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 136(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, %%r8; movnti %%r8, 120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rdi)
                "movq %%xmm1, %%r9; movnti %%r9, 128(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, %%r10; movnti %%r10, 136(%%rdi);"NOP(NOPCOUNT)
                "movq 144(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 152(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 160(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, %%r8; movnti %%r8, 144(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9, 152(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, %%r10; movnti %%r10, 160(%%rdi);"NOP(NOPCOUNT)
                "movq 168(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 176(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 184(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, %%r8; movnti %%r8, 168(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9, 176(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, %%r10; movnti %%r10, 184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "movq 192(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 200(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 208(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                PREFETCH(LINE_PREFETCH,192,rdi)
                "movq %%xmm0, %%r8; movnti %%r8, 192(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9, 200(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, %%r10; movnti %%r10, 208(%%rdi);"NOP(NOPCOUNT)
                "movq 216(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 224(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 232(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, %%r8; movnti %%r8, 216(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9, 224(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, %%r10; movnti %%r10, 232(%%rdi);"NOP(NOPCOUNT)
                "movq 240(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 248(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                PREFETCH(LINE_PREFETCH,256,rsi)
                "movq 256(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq %%xmm0, %%r8; movnti %%r8, 240(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9, 248(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rdi)
                "movq %%xmm2, %%r10; movnti %%r10, 256(%%rdi);"NOP(NOPCOUNT)
                "add $264,%%rsi;"
                "add $264,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _scale_loop_movnti_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movnti instruction
 */
static void asm_scale_movnti_4(param_t *params) __attribute__((noinline));
static void asm_scale_movnti_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"
                "movq (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movnti_4;"
                ".align 64,0x0;"
                "_scale_loop_movnti_4:"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "movq 0(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 8(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 16(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 24(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                PREFETCH(LINE_PREFETCH,0,rdi)
                "movq %%xmm0, %%r8; movnti %%r8,0(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9,8(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, %%r10; movnti %%r10,16(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3, %%r11; movnti %%r11,24(%%rdi);"NOP(NOPCOUNT)
                "movq 32(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 40(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 48(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 56(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                "movq %%xmm0, %%r8; movnti %%r8,32(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9,40(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, %%r10; movnti %%r10,48(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3, %%r11; movnti %%r11,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)
                "movq 64(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 72(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 80(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 88(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                PREFETCH(LINE_PREFETCH,64,rdi)
                "movq %%xmm0, %%r8; movnti %%r8,64(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9,72(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, %%r10; movnti %%r10,80(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3, %%r11; movnti %%r11,88(%%rdi);"NOP(NOPCOUNT)
                "movq 96(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 104(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 112(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 120(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                "movq %%xmm0, %%r8; movnti %%r8,96(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9,104(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, %%r10; movnti %%r10,112(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3, %%r11; movnti %%r11,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)
                "movq 128(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 136(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 144(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 152(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                PREFETCH(LINE_PREFETCH,128,rdi)
                "movq %%xmm0, %%r8; movnti %%r8,128(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9,136(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, %%r10; movnti %%r10,144(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3, %%r11; movnti %%r11,152(%%rdi);"NOP(NOPCOUNT)
                "movq 160(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 168(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 176(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 184(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                "movq %%xmm0, %%r8; movnti %%r8,160(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9,168(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, %%r10; movnti %%r10,176(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3, %%r11; movnti %%r11,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "movq 192(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 200(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 208(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 216(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                PREFETCH(LINE_PREFETCH,192,rdi)
                "movq %%xmm0, %%r8; movnti %%r8,192(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9,200(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, %%r10; movnti %%r10,208(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3, %%r11; movnti %%r11,216(%%rdi);"NOP(NOPCOUNT)
                "movq 224(%%rsi),%%xmm0;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm0;"
                "movq 232(%%rsi),%%xmm1;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm1;"
                "movq 240(%%rsi),%%xmm2;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm2;"
                "movq 248(%%rsi),%%xmm3;"NOP(NOPCOUNT)"mulsd %%xmm15,%%xmm3;"
                "movq %%xmm0, %%r8; movnti %%r8,224(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm1, %%r9; movnti %%r9,232(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm2, %%r10; movnti %%r10,240(%%rdi);"NOP(NOPCOUNT)
                "movq %%xmm3, %%r11; movnti %%r11,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _scale_loop_movnti_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movntpd instruction
 */
static void asm_scale_movntpd_1(param_t *params) __attribute__((noinline));
static void asm_scale_movntpd_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
                "movddup (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movntpd_1;"
                ".align 64,0x0;"
                "_scale_loop_movntpd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movapd 0(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,16(%%r12);"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,32(%%r12);"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movapd 64(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,64(%%r12);"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,80(%%r12);"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,96(%%r12);"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movapd 128(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,144(%%r14);"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,160(%%r14);"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movapd 192(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,208(%%r14);"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,224(%%r14);"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movapd 256(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,272(%%r14);"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,288(%%r14);"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movapd 320(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,320(%%r14);"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,336(%%r14);"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,352(%%r14);"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movapd 384(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,400(%%r14);"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,416(%%r14);"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movapd 448(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,448(%%r14);"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,464(%%r14);"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,480(%%r14);"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;movntpd %%xmm0,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_movntpd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movntpd instruction
 */
static void asm_scale_movntpd_2(param_t *params) __attribute__((noinline));
static void asm_scale_movntpd_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
                "movddup (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movntpd_2;"
                ".align 64,0x0;"
                "_scale_loop_movntpd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movapd 0(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,32(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm1,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movapd 64(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,64(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm1,80(%%r12);"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,96(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm1,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movapd 128(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,160(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movapd 192(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,224(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movapd 256(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,288(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movapd 320(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,320(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,336(%%r14);"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,352(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movapd 384(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,416(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movapd 448(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,448(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,464(%%r14);"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm0,480(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_movntpd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movntpd instruction
 */
static void asm_scale_movntpd_3(param_t *params) __attribute__((noinline));
static void asm_scale_movntpd_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
                "movddup (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movntpd_3;"
                ".align 64,0x0;"
                "_scale_loop_movntpd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movntpd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "movapd 48(%%r10), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 80(%%r10), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm0,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movntpd %%xmm1,64(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm2,80(%%r12);"NOP(NOPCOUNT)
                "add $528,%%r10;"
                "movapd 96(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 112(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm0,96(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,112(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movntpd %%xmm2,128(%%r14);"NOP(NOPCOUNT)
                "add $528,%%r12;"
                "movapd 144(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 160(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 176(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm0,144(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,160(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,176(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 208(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 224(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movntpd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,224(%%r14);"NOP(NOPCOUNT)
                
                "movapd 240(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 272(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm0,240(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movntpd %%xmm1,256(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,272(%%r14);"NOP(NOPCOUNT)
                
                "movapd 288(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 304(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm0,288(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movntpd %%xmm2,320(%%r14);"NOP(NOPCOUNT)
                
                "movapd 336(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 352(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 368(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm0,336(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,352(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movntpd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                
                "movapd 432(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 464(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm0,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movntpd %%xmm1,448(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,464(%%r14);"NOP(NOPCOUNT)
                
                "movapd 480(%%r13), %%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 496(%%r13), %%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "movapd 512(%%r13), %%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm0,480(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,496(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "movntpd %%xmm2,512(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_movntpd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movntpd instruction
 */
static void asm_scale_movntpd_4(param_t *params) __attribute__((noinline));
static void asm_scale_movntpd_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
                "movddup (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movntpd_4;"
                ".align 64,0x0;"
                "_scale_loop_movntpd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movntpd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movntpd %%xmm0,64(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm1,80(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm2,96(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm3,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movntpd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,160(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movntpd %%xmm0,192(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,224(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movntpd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,288(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movntpd %%xmm0,320(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,336(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,352(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movntpd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movntpd %%xmm0,448(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,464(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,480(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_movntpd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movntpd instruction
 */
static void asm_scale_movntpd_8(param_t *params) __attribute__((noinline));
static void asm_scale_movntpd_8(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
                "movddup (%%rax),%%xmm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_movntpd_8;"
                ".align 64,0x0;"
                "_scale_loop_movntpd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10),%%xmm4;mulpd %%xmm15,%%xmm4;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm5;mulpd %%xmm15,%%xmm5;"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm6;mulpd %%xmm15,%%xmm6;"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm7;mulpd %%xmm15,%%xmm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "movntpd %%xmm0,0(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm2,32(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movntpd %%xmm4,64(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm5,80(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm6,96(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm7,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13),%%xmm4;mulpd %%xmm15,%%xmm4;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm5;mulpd %%xmm15,%%xmm5;"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm6;mulpd %%xmm15,%%xmm6;"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm7;mulpd %%xmm15,%%xmm7;"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,128,r14)
                "movntpd %%xmm0,128(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,160(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,176(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movntpd %%xmm4,192(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,208(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm6,224(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm7,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13),%%xmm4;mulpd %%xmm15,%%xmm4;"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm5;mulpd %%xmm15,%%xmm5;"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm6;mulpd %%xmm15,%%xmm6;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm7;mulpd %%xmm15,%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r14)
                "movntpd %%xmm0,256(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,288(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movntpd %%xmm4,320(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,336(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm6,352(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm7,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13),%%xmm0;mulpd %%xmm15,%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;mulpd %%xmm15,%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm2;mulpd %%xmm15,%%xmm2;"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm3;mulpd %%xmm15,%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13),%%xmm4;mulpd %%xmm15,%%xmm4;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm5;mulpd %%xmm15,%%xmm5;"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm6;mulpd %%xmm15,%%xmm6;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm7;mulpd %%xmm15,%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r14)
                "movntpd %%xmm0,384(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm2,416(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movntpd %%xmm4,448(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,464(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm6,480(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm7,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_movntpd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovntpd instruction
 */
static void asm_scale_vmovntpd_1(param_t *params) __attribute__((noinline));
static void asm_scale_vmovntpd_1(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
		"movddup (%%rax),%%xmm15;"
                "vinsertf128 $0, %%xmm15, %%ymm15, %%ymm15;"
                "vinsertf128 $1, %%xmm15, %%ymm15, %%ymm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_vmovntpd_1;"
                ".align 64,0x0;"
                "_scale_loop_vmovntpd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
		"vmulpd 0(%%r10),%%ymm15,%%ymm0;vmovntpd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
		"vmulpd 32(%%r10),%%ymm15,%%ymm0;vmovntpd %%ymm0,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
		"vmulpd 64(%%r10),%%ymm15,%%ymm0;vmovntpd %%ymm0,64(%%r12);"NOP(NOPCOUNT)
		"vmulpd 96(%%r10),%%ymm15,%%ymm0;vmovntpd %%ymm0,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
		"vmulpd 128(%%r10),%%ymm15,%%ymm0;vmovntpd %%ymm0,128(%%r12);"NOP(NOPCOUNT)
		"vmulpd 160(%%r10),%%ymm15,%%ymm0;vmovntpd %%ymm0,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
		"vmulpd 192(%%r10),%%ymm15,%%ymm0;vmovntpd %%ymm0,192(%%r12);"NOP(NOPCOUNT)
		"vmulpd 224(%%r10),%%ymm15,%%ymm0;vmovntpd %%ymm0,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
		"vmulpd 256(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
		"vmulpd 288(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
		"vmulpd 320(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,320(%%r14);"NOP(NOPCOUNT)
		"vmulpd 352(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
		"vmulpd 384(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
		"vmulpd 416(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
		"vmulpd 448(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,448(%%r14);"NOP(NOPCOUNT)
		"vmulpd 480(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
		"vmulpd 512(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
		"vmulpd 544(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
		"vmulpd 576(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,576(%%r14);"NOP(NOPCOUNT)
		"vmulpd 608(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
		"vmulpd 640(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,640(%%r14);"NOP(NOPCOUNT)
		"vmulpd 672(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
		"vmulpd 704(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,704(%%r14);"NOP(NOPCOUNT)
		"vmulpd 736(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
		"vmulpd 768(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
		"vmulpd 800(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
		"vmulpd 832(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,832(%%r14);"NOP(NOPCOUNT)
		"vmulpd 864(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
		"vmulpd 896(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,896(%%r14);"NOP(NOPCOUNT)
		"vmulpd 928(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
		"vmulpd 960(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,960(%%r14);"NOP(NOPCOUNT)
		"vmulpd 992(%%r13),%%ymm15,%%ymm0;vmovntpd %%ymm0,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_vmovntpd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovntpd instruction
 */
static void asm_scale_vmovntpd_2(param_t *params) __attribute__((noinline));
static void asm_scale_vmovntpd_2(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
		"movddup (%%rax),%%xmm15;"
                "vinsertf128 $0, %%xmm15, %%ymm15, %%ymm15;"
                "vinsertf128 $1, %%xmm15, %%ymm15, %%ymm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_vmovntpd_2;"
                ".align 64,0x0;"
                "_scale_loop_vmovntpd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "vmulpd 0(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 32(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "vmulpd 64(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 96(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,64(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
                "vmulpd 128(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 160(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,128(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
                "vmulpd 192(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 224(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,192(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "vmulpd 256(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 288(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "vmulpd 320(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 352(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,320(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "vmulpd 384(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 416(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "vmulpd 448(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 480(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,448(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
                "vmulpd 512(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 544(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
                "vmulpd 576(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 608(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,576(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
                "vmulpd 640(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 672(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,640(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
                "vmulpd 704(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 736(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,704(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
                "vmulpd 768(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 800(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
                "vmulpd 832(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 864(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,832(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
                "vmulpd 896(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 928(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,896(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
                "vmulpd 960(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 992(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,960(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_vmovntpd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovntpd instruction
 */
static void asm_scale_vmovntpd_3(param_t *params) __attribute__((noinline));
static void asm_scale_vmovntpd_3(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
		"movddup (%%rax),%%xmm15;"
                "vinsertf128 $0, %%xmm15, %%ymm15, %%ymm15;"
                "vinsertf128 $1, %%xmm15, %%ymm15, %%ymm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_vmovntpd_3;"
                ".align 64,0x0;"
                "_scale_loop_vmovntpd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmulpd 0(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 32(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmulpd 64(%%r10),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovntpd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovntpd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "vmulpd 96(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmulpd 128(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmulpd 160(%%r10),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovntpd %%ymm1,128(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,160(%%r12);"NOP(NOPCOUNT)
                "add $1056,%%r10;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "vmulpd 192(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 224(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmulpd 256(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "vmovntpd %%ymm0,192(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,224(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovntpd %%ymm2,256(%%r14);"NOP(NOPCOUNT)
                "add $1056,%%r12;"
                "vmulpd 288(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmulpd 320(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmulpd 352(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovntpd %%ymm1,320(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,352(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmulpd 384(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 416(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmulpd 448(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovntpd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovntpd %%ymm2,448(%%r14);"NOP(NOPCOUNT)
                
                "vmulpd 480(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmulpd 512(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmulpd 544(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,480(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovntpd %%ymm1,512(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,544(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmulpd 576(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 608(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmulpd 640(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovntpd %%ymm0,576(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovntpd %%ymm2,640(%%r14);"NOP(NOPCOUNT)
                
                "vmulpd 672(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmulpd 704(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmulpd 736(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovntpd %%ymm1,704(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmulpd 768(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 800(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmulpd 832(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovntpd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovntpd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                
                "vmulpd 864(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmulpd 896(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                "vmulpd 928(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmovntpd %%ymm0,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovntpd %%ymm1,896(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,928(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmulpd 960(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 992(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r13)
                "vmulpd 1024(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovntpd %%ymm0,960(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,992(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r14)
                "vmovntpd %%ymm2,1024(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_vmovntpd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovntpd instruction
 */
static void asm_scale_vmovntpd_4(param_t *params) __attribute__((noinline));
static void asm_scale_vmovntpd_4(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
		"movddup (%%rax),%%xmm15;"
                "vinsertf128 $0, %%xmm15, %%ymm15, %%ymm15;"
                "vinsertf128 $1, %%xmm15, %%ymm15, %%ymm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_vmovntpd_4;"
                ".align 64,0x0;"
                "_scale_loop_vmovntpd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmulpd 0(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 32(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmulpd 64(%%r10),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 96(%%r10),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovntpd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovntpd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmulpd 128(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 160(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmulpd 192(%%r10),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 224(%%r10),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovntpd %%ymm0,128(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovntpd %%ymm2,192(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmulpd 256(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 288(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmulpd 320(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 352(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovntpd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovntpd %%ymm2,320(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmulpd 384(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 416(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmulpd 448(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 480(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovntpd %%ymm0,384(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovntpd %%ymm2,448(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmulpd 512(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 544(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmulpd 576(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 608(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovntpd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovntpd %%ymm2,576(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmulpd 640(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 672(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmulpd 704(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 736(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovntpd %%ymm0,640(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovntpd %%ymm2,704(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmulpd 768(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 800(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmulpd 832(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 864(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovntpd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovntpd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmulpd 896(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 928(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmulpd 960(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 992(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovntpd %%ymm0,896(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovntpd %%ymm2,960(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_vmovntpd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovntpd instruction
 */
static void asm_scale_vmovntpd_8(param_t *params) __attribute__((noinline));
static void asm_scale_vmovntpd_8(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RAX: factor (used for scaling operation)
     *         RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"
		"movddup (%%rax),%%xmm15;"
                "vinsertf128 $0, %%xmm15, %%ymm15, %%ymm15;"
                "vinsertf128 $1, %%xmm15, %%ymm15, %%ymm15;"

                TIMESTAMP
                SERIALIZE
                "jmp _scale_loop_vmovntpd_8;"
                ".align 64,0x0;"
                "_scale_loop_vmovntpd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmulpd 0(%%r10),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 32(%%r10),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmulpd 64(%%r10),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 96(%%r10),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmulpd 128(%%r10),%%ymm15,%%ymm4;"NOP(NOPCOUNT)
                "vmulpd 160(%%r10),%%ymm15,%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmulpd 192(%%r10),%%ymm15,%%ymm6;"NOP(NOPCOUNT)
                "vmulpd 224(%%r10),%%ymm15,%%ymm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovntpd %%ymm0,0(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovntpd %%ymm2,64(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovntpd %%ymm4,128(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovntpd %%ymm6,192(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm7,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmulpd 256(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 288(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmulpd 320(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 352(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmulpd 384(%%r13),%%ymm15,%%ymm4;"NOP(NOPCOUNT)
                "vmulpd 416(%%r13),%%ymm15,%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmulpd 448(%%r13),%%ymm15,%%ymm6;"NOP(NOPCOUNT)
                "vmulpd 480(%%r13),%%ymm15,%%ymm7;"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovntpd %%ymm0,256(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovntpd %%ymm2,320(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,352(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovntpd %%ymm4,384(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovntpd %%ymm6,448(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm7,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmulpd 512(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 544(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmulpd 576(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 608(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmulpd 640(%%r13),%%ymm15,%%ymm4;"NOP(NOPCOUNT)
                "vmulpd 672(%%r13),%%ymm15,%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmulpd 704(%%r13),%%ymm15,%%ymm6;"NOP(NOPCOUNT)
                "vmulpd 736(%%r13),%%ymm15,%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovntpd %%ymm0,512(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovntpd %%ymm2,576(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovntpd %%ymm4,640(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovntpd %%ymm6,704(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm7,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmulpd 768(%%r13),%%ymm15,%%ymm0;"NOP(NOPCOUNT)
                "vmulpd 800(%%r13),%%ymm15,%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmulpd 832(%%r13),%%ymm15,%%ymm2;"NOP(NOPCOUNT)
                "vmulpd 864(%%r13),%%ymm15,%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmulpd 896(%%r13),%%ymm15,%%ymm4;"NOP(NOPCOUNT)
                "vmulpd 928(%%r13),%%ymm15,%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmulpd 960(%%r13),%%ymm15,%%ymm6;"NOP(NOPCOUNT)
                "vmulpd 992(%%r13),%%ymm15,%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovntpd %%ymm0,768(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovntpd %%ymm2,832(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovntpd %%ymm4,896(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovntpd %%ymm6,960(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm7,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _scale_loop_vmovntpd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "a" (&(params->factor)), "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movapd instruction
 */
static void asm_indep_movapd_1(param_t *params) __attribute__((noinline));
static void asm_indep_movapd_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movapd_1;"
                ".align 64,0x0;"
                "_indep_loop_movapd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,0(%%r12);"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,32(%%r12);"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movapd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,64(%%r12);"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,80(%%r12);"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,96(%%r12);"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movapd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,128(%%r14);"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,160(%%r14);"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movapd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,192(%%r14);"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,224(%%r14);"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movapd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,256(%%r14);"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,288(%%r14);"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movapd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,320(%%r14);"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,336(%%r14);"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,352(%%r14);"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,384(%%r14);"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,416(%%r14);"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movapd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,448(%%r14);"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,464(%%r14);"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,480(%%r14);"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd %%xmm1,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_movapd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movapd instruction
 */
static void asm_indep_movapd_2(param_t *params) __attribute__((noinline));
static void asm_indep_movapd_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movapd_2;"
                ".align 64,0x0;"
                "_indep_loop_movapd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm2,0(%%r12);"NOP(NOPCOUNT)"movapd %%xmm3,16(%%r12);"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd 48(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm2,32(%%r12);"NOP(NOPCOUNT)"movapd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movapd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd 80(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm2,64(%%r12);"NOP(NOPCOUNT)"movapd %%xmm3,80(%%r12);"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd 112(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm2,96(%%r12);"NOP(NOPCOUNT)"movapd %%xmm3,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movapd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm2,128(%%r14);"NOP(NOPCOUNT)"movapd %%xmm3,144(%%r14);"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 176(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm2,160(%%r14);"NOP(NOPCOUNT)"movapd %%xmm3,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movapd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm2,192(%%r14);"NOP(NOPCOUNT)"movapd %%xmm3,208(%%r14);"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 240(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm2,224(%%r14);"NOP(NOPCOUNT)"movapd %%xmm3,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movapd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm2,256(%%r14);"NOP(NOPCOUNT)"movapd %%xmm3,272(%%r14);"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 304(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm2,288(%%r14);"NOP(NOPCOUNT)"movapd %%xmm3,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movapd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 336(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm2,320(%%r14);"NOP(NOPCOUNT)"movapd %%xmm3,336(%%r14);"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 368(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm2,352(%%r14);"NOP(NOPCOUNT)"movapd %%xmm3,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm2,384(%%r14);"NOP(NOPCOUNT)"movapd %%xmm3,400(%%r14);"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 432(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm2,416(%%r14);"NOP(NOPCOUNT)"movapd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movapd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 464(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm2,448(%%r14);"NOP(NOPCOUNT)"movapd %%xmm3,464(%%r14);"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 496(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd %%xmm2,480(%%r14);"NOP(NOPCOUNT)"movapd %%xmm3,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_movapd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movapd instruction
 */
static void asm_indep_movapd_3(param_t *params) __attribute__((noinline));
static void asm_indep_movapd_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movapd_3;"
                ".align 64,0x0;"
                "_indep_loop_movapd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movapd %%xmm3,0(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm4,16(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm5,32(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "movapd 48(%%r10),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movapd %%xmm4,64(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm5,80(%%r12);"NOP(NOPCOUNT)
                "add $528,%%r10;"
                "movapd 96(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 112(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm3,96(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm4,112(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movapd %%xmm5,128(%%r14);"NOP(NOPCOUNT)
                "add $528,%%r12;"
                "movapd 144(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm3,144(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm4,160(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,176(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movapd %%xmm3,192(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm4,208(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,224(%%r14);"NOP(NOPCOUNT)
                
                "movapd 240(%%r13),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm3,240(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movapd %%xmm4,256(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,272(%%r14);"NOP(NOPCOUNT)
                
                "movapd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm3,288(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm4,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movapd %%xmm5,320(%%r14);"NOP(NOPCOUNT)
                
                "movapd 336(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm3,336(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm4,352(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movapd %%xmm3,384(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm4,400(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,416(%%r14);"NOP(NOPCOUNT)
                
                "movapd 432(%%r13),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movapd %%xmm4,448(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,464(%%r14);"NOP(NOPCOUNT)
                
                "movapd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "movapd 512(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd %%xmm3,480(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm4,496(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "movapd %%xmm5,512(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_movapd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movapd instruction
 */
static void asm_indep_movapd_4(param_t *params) __attribute__((noinline));
static void asm_indep_movapd_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movapd_4;"
                ".align 64,0x0;"
                "_indep_loop_movapd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movapd %%xmm4,0(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm5,16(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm6,32(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm7,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movapd %%xmm4,64(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm5,80(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm6,96(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm7,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movapd %%xmm4,128(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,144(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm6,160(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm7,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movapd %%xmm4,192(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,208(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm6,224(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm7,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movapd %%xmm4,256(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,272(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm6,288(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm7,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movapd %%xmm4,320(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,336(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm6,352(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm7,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movapd %%xmm4,384(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,400(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm6,416(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm7,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movapd %%xmm4,448(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm5,464(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm6,480(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm7,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_movapd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movapd instruction
 */
static void asm_indep_movapd_8(param_t *params) __attribute__((noinline));
static void asm_indep_movapd_8(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movapd_8;"
                ".align 64,0x0;"
                "_indep_loop_movapd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10),%%xmm4;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm5;"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm6;"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "movapd %%xmm8,0(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm9,16(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm10,32(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm11,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movapd %%xmm12,64(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm13,80(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm14,96(%%r12);"NOP(NOPCOUNT)
                "movapd %%xmm15,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm7;"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,128,r14)
                "movapd %%xmm8,128(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm9,144(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm10,160(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm11,176(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movapd %%xmm12,192(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm13,208(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm14,224(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm15,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r14)
                "movapd %%xmm8,256(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm9,272(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm10,288(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm11,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movapd %%xmm12,320(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm13,336(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm14,352(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm15,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r14)
                "movapd %%xmm8,384(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm9,400(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm10,416(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm11,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movapd %%xmm12,448(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm13,464(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm14,480(%%r14);"NOP(NOPCOUNT)
                "movapd %%xmm15,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_movapd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovapd instruction
 */
static void asm_indep_vmovapd_1(param_t *params) __attribute__((noinline));
static void asm_indep_vmovapd_1(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_vmovapd_1;"
                ".align 64,0x0;"
                "_indep_loop_vmovapd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,0(%%r12);"NOP(NOPCOUNT)
                "vmovapd 32(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "vmovapd 64(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,64(%%r12);"NOP(NOPCOUNT)
                "vmovapd 96(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
                "vmovapd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,128(%%r12);"NOP(NOPCOUNT)
                "vmovapd 160(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
                "vmovapd 192(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,192(%%r12);"NOP(NOPCOUNT)
                "vmovapd 224(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "vmovapd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,256(%%r14);"NOP(NOPCOUNT)
                "vmovapd 288(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "vmovapd 320(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,320(%%r14);"NOP(NOPCOUNT)
                "vmovapd 352(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "vmovapd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,384(%%r14);"NOP(NOPCOUNT)
                "vmovapd 416(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "vmovapd 448(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,448(%%r14);"NOP(NOPCOUNT)
                "vmovapd 480(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
                "vmovapd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,512(%%r14);"NOP(NOPCOUNT)
                "vmovapd 544(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
                "vmovapd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,576(%%r14);"NOP(NOPCOUNT)
                "vmovapd 608(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
                "vmovapd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,640(%%r14);"NOP(NOPCOUNT)
                "vmovapd 672(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
                "vmovapd 704(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,704(%%r14);"NOP(NOPCOUNT)
                "vmovapd 736(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,768(%%r14);"NOP(NOPCOUNT)
                "vmovapd 800(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
                "vmovapd 832(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,832(%%r14);"NOP(NOPCOUNT)
                "vmovapd 864(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
                "vmovapd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,896(%%r14);"NOP(NOPCOUNT)
                "vmovapd 928(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
                "vmovapd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,960(%%r14);"NOP(NOPCOUNT)
                "vmovapd 992(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd %%ymm1,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_vmovapd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovapd instruction
 */
static void asm_indep_vmovapd_2(param_t *params) __attribute__((noinline));
static void asm_indep_vmovapd_2(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_vmovapd_2;"
                ".align 64,0x0;"
                "_indep_loop_vmovapd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm2,0(%%r12);"NOP(NOPCOUNT)"vmovapd %%ymm3,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "vmovapd 64(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd 96(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm2,64(%%r12);"NOP(NOPCOUNT)"vmovapd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
                "vmovapd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd 160(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm2,128(%%r12);"NOP(NOPCOUNT)"vmovapd %%ymm3,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
                "vmovapd 192(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd 224(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm2,192(%%r12);"NOP(NOPCOUNT)"vmovapd %%ymm3,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "vmovapd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm2,256(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm3,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "vmovapd 320(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 352(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm2,320(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm3,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "vmovapd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm2,384(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm3,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "vmovapd 448(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 480(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm2,448(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm3,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
                "vmovapd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm2,512(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm3,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
                "vmovapd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 608(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm2,576(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm3,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
                "vmovapd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 672(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm2,640(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm3,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
                "vmovapd 704(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 736(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm2,704(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm3,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm2,768(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm3,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
                "vmovapd 832(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 864(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm2,832(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
                "vmovapd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 928(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm2,896(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm3,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
                "vmovapd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 992(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd %%ymm2,960(%%r14);"NOP(NOPCOUNT)"vmovapd %%ymm3,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_vmovapd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovapd instruction
 */
static void asm_indep_vmovapd_3(param_t *params) __attribute__((noinline));
static void asm_indep_vmovapd_3(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_vmovapd_3;"
                ".align 64,0x0;"
                "_indep_loop_vmovapd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovapd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovapd %%ymm3,0(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm4,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovapd %%ymm5,64(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "vmovapd 96(%%r10),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovapd 128(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 160(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovapd %%ymm4,128(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,160(%%r12);"NOP(NOPCOUNT)
                "add $1056,%%r10;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "vmovapd 192(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 224(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovapd 256(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "vmovapd %%ymm3,192(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm4,224(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovapd %%ymm5,256(%%r14);"NOP(NOPCOUNT)
                "add $1056,%%r12;"
                "vmovapd 288(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovapd 320(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 352(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd %%ymm3,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovapd %%ymm4,320(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,352(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovapd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovapd 448(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovapd %%ymm3,384(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm4,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovapd %%ymm5,448(%%r14);"NOP(NOPCOUNT)
                
                "vmovapd 480(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovapd 512(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 544(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd %%ymm3,480(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovapd %%ymm4,512(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,544(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovapd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 608(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovapd 640(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovapd %%ymm3,576(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm4,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovapd %%ymm5,640(%%r14);"NOP(NOPCOUNT)
                
                "vmovapd 672(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovapd 704(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 736(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd %%ymm3,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovapd %%ymm4,704(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovapd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovapd %%ymm3,768(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm4,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovapd %%ymm5,832(%%r14);"NOP(NOPCOUNT)
                
                "vmovapd 864(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovapd 896(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 928(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovapd %%ymm4,896(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,928(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovapd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 992(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r13)
                "vmovapd 1024(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovapd %%ymm3,960(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm4,992(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r14)
                "vmovapd %%ymm5,1024(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_vmovapd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovapd instruction
 */
static void asm_indep_vmovapd_4(param_t *params) __attribute__((noinline));
static void asm_indep_vmovapd_4(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_vmovapd_4;"
                ".align 64,0x0;"
                "_indep_loop_vmovapd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovapd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 96(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovapd %%ymm4,0(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovapd %%ymm6,64(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm7,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovapd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 160(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmovapd 192(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 224(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovapd %%ymm4,128(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovapd %%ymm6,192(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm7,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovapd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovapd 320(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 352(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovapd %%ymm4,256(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovapd %%ymm6,320(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm7,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovapd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovapd 448(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 480(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovapd %%ymm4,384(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovapd %%ymm6,448(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm7,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovapd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovapd 576(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 608(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovapd %%ymm4,512(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovapd %%ymm6,576(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm7,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovapd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 672(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovapd 704(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 736(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovapd %%ymm4,640(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovapd %%ymm6,704(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm7,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovapd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 864(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovapd %%ymm4,768(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovapd %%ymm6,832(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm7,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovapd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 928(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovapd 960(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 992(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovapd %%ymm4,896(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm5,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovapd %%ymm6,960(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm7,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_vmovapd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovapd instruction
 */
static void asm_indep_vmovapd_8(param_t *params) __attribute__((noinline));
static void asm_indep_vmovapd_8(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_vmovapd_8;"
                ".align 64,0x0;"
                "_indep_loop_vmovapd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovapd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 96(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovapd 128(%%r10),%%ymm4;"NOP(NOPCOUNT)
                "vmovapd 160(%%r10),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmovapd 192(%%r10),%%ymm6;"NOP(NOPCOUNT)
                "vmovapd 224(%%r10),%%ymm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovapd %%ymm8,0(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm9,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovapd %%ymm10,64(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm11,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovapd %%ymm12,128(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm13,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovapd %%ymm14,192(%%r12);"NOP(NOPCOUNT)
                "vmovapd %%ymm15,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovapd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovapd 320(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 352(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovapd 384(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovapd 416(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovapd 448(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovapd 480(%%r13),%%ymm7;"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovapd %%ymm8,256(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm9,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovapd %%ymm10,320(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm11,352(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovapd %%ymm12,384(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm13,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovapd %%ymm14,448(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm15,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovapd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovapd 576(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 608(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovapd 640(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovapd 672(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovapd 704(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovapd 736(%%r13),%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovapd %%ymm8,512(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm9,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovapd %%ymm10,576(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm11,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovapd %%ymm12,640(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm13,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovapd %%ymm14,704(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm15,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovapd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 864(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovapd 896(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovapd 928(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovapd 960(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovapd 992(%%r13),%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovapd %%ymm8,768(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm9,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovapd %%ymm10,832(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm11,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovapd %%ymm12,896(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm13,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovapd %%ymm14,960(%%r14);"NOP(NOPCOUNT)
                "vmovapd %%ymm15,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_vmovapd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movupd instruction
 */
static void asm_indep_movupd_1(param_t *params) __attribute__((noinline));
static void asm_indep_movupd_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movupd_1;"
                ".align 64,0x0;"
                "_indep_loop_movupd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movupd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,0(%%r12);"NOP(NOPCOUNT)
                "movupd 16(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movupd 32(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,32(%%r12);"NOP(NOPCOUNT)
                "movupd 48(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movupd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,64(%%r12);"NOP(NOPCOUNT)
                "movupd 80(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,80(%%r12);"NOP(NOPCOUNT)
                "movupd 96(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,96(%%r12);"NOP(NOPCOUNT)
                "movupd 112(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movupd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,128(%%r14);"NOP(NOPCOUNT)
                "movupd 144(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movupd 160(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,160(%%r14);"NOP(NOPCOUNT)
                "movupd 176(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movupd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,192(%%r14);"NOP(NOPCOUNT)
                "movupd 208(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movupd 224(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,224(%%r14);"NOP(NOPCOUNT)
                "movupd 240(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movupd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,256(%%r14);"NOP(NOPCOUNT)
                "movupd 272(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movupd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,288(%%r14);"NOP(NOPCOUNT)
                "movupd 304(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movupd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,320(%%r14);"NOP(NOPCOUNT)
                "movupd 336(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,336(%%r14);"NOP(NOPCOUNT)
                "movupd 352(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,352(%%r14);"NOP(NOPCOUNT)
                "movupd 368(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movupd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,384(%%r14);"NOP(NOPCOUNT)
                "movupd 400(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movupd 416(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,416(%%r14);"NOP(NOPCOUNT)
                "movupd 432(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movupd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,448(%%r14);"NOP(NOPCOUNT)
                "movupd 464(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,464(%%r14);"NOP(NOPCOUNT)
                "movupd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,480(%%r14);"NOP(NOPCOUNT)
                "movupd 496(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd %%xmm1,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_movupd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movupd instruction
 */
static void asm_indep_movupd_2(param_t *params) __attribute__((noinline));
static void asm_indep_movupd_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movupd_2;"
                ".align 64,0x0;"
                "_indep_loop_movupd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movupd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm2,0(%%r12);"NOP(NOPCOUNT)"movupd %%xmm3,16(%%r12);"NOP(NOPCOUNT)
                "movupd 32(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd 48(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm2,32(%%r12);"NOP(NOPCOUNT)"movupd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movupd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd 80(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm2,64(%%r12);"NOP(NOPCOUNT)"movupd %%xmm3,80(%%r12);"NOP(NOPCOUNT)
                "movupd 96(%%r10),%%xmm0;"NOP(NOPCOUNT)"movupd 112(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm2,96(%%r12);"NOP(NOPCOUNT)"movupd %%xmm3,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movupd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm2,128(%%r14);"NOP(NOPCOUNT)"movupd %%xmm3,144(%%r14);"NOP(NOPCOUNT)
                "movupd 160(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 176(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm2,160(%%r14);"NOP(NOPCOUNT)"movupd %%xmm3,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movupd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm2,192(%%r14);"NOP(NOPCOUNT)"movupd %%xmm3,208(%%r14);"NOP(NOPCOUNT)
                "movupd 224(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 240(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm2,224(%%r14);"NOP(NOPCOUNT)"movupd %%xmm3,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movupd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm2,256(%%r14);"NOP(NOPCOUNT)"movupd %%xmm3,272(%%r14);"NOP(NOPCOUNT)
                "movupd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 304(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm2,288(%%r14);"NOP(NOPCOUNT)"movupd %%xmm3,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movupd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 336(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm2,320(%%r14);"NOP(NOPCOUNT)"movupd %%xmm3,336(%%r14);"NOP(NOPCOUNT)
                "movupd 352(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 368(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm2,352(%%r14);"NOP(NOPCOUNT)"movupd %%xmm3,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movupd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm2,384(%%r14);"NOP(NOPCOUNT)"movupd %%xmm3,400(%%r14);"NOP(NOPCOUNT)
                "movupd 416(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 432(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm2,416(%%r14);"NOP(NOPCOUNT)"movupd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movupd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 464(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm2,448(%%r14);"NOP(NOPCOUNT)"movupd %%xmm3,464(%%r14);"NOP(NOPCOUNT)
                "movupd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)"movupd 496(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd %%xmm2,480(%%r14);"NOP(NOPCOUNT)"movupd %%xmm3,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_movupd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movupd instruction
 */
static void asm_indep_movupd_3(param_t *params) __attribute__((noinline));
static void asm_indep_movupd_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movupd_3;"
                ".align 64,0x0;"
                "_indep_loop_movupd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movupd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movupd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movupd %%xmm3,0(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm4,16(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm5,32(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "movupd 48(%%r10),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movupd 64(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd 80(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movupd %%xmm4,64(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm5,80(%%r12);"NOP(NOPCOUNT)
                "add $528,%%r10;"
                "movupd 96(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 112(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r13)
                "movupd 128(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm3,96(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm4,112(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movupd %%xmm5,128(%%r14);"NOP(NOPCOUNT)
                "add $528,%%r12;"
                "movupd 144(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 160(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 176(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm3,144(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm4,160(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,176(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,192,r13)
                "movupd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 224(%%r13),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movupd %%xmm3,192(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm4,208(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,224(%%r14);"NOP(NOPCOUNT)
                
                "movupd 240(%%r13),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "movupd 256(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 272(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm3,240(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movupd %%xmm4,256(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,272(%%r14);"NOP(NOPCOUNT)
                
                "movupd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 304(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movupd 320(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm3,288(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm4,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movupd %%xmm5,320(%%r14);"NOP(NOPCOUNT)
                
                "movupd 336(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 352(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 368(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm3,336(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm4,352(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movupd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movupd %%xmm3,384(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm4,400(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,416(%%r14);"NOP(NOPCOUNT)
                
                "movupd 432(%%r13),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movupd 448(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 464(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movupd %%xmm4,448(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,464(%%r14);"NOP(NOPCOUNT)
                
                "movupd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 496(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "movupd 512(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd %%xmm3,480(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm4,496(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "movupd %%xmm5,512(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_movupd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movupd instruction
 */
static void asm_indep_movupd_4(param_t *params) __attribute__((noinline));
static void asm_indep_movupd_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movupd_4;"
                ".align 64,0x0;"
                "_indep_loop_movupd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movupd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movupd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movupd 48(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movupd %%xmm4,0(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm5,16(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm6,32(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm7,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)
                "movupd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movupd 80(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd 96(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movupd 112(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movupd %%xmm4,64(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm5,80(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm6,96(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm7,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movupd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 160(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 176(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movupd %%xmm4,128(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,144(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm6,160(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm7,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "movupd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 224(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 240(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movupd %%xmm4,192(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,208(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm6,224(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm7,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movupd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 288(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 304(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movupd %%xmm4,256(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,272(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm6,288(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm7,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)
                "movupd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 336(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 352(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 368(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movupd %%xmm4,320(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,336(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm6,352(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm7,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movupd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 432(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movupd %%xmm4,384(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,400(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm6,416(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm7,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)
                "movupd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 464(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 480(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 496(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movupd %%xmm4,448(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm5,464(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm6,480(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm7,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_movupd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movupd instruction
 */
static void asm_indep_movupd_8(param_t *params) __attribute__((noinline));
static void asm_indep_movupd_8(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movupd_8;"
                ".align 64,0x0;"
                "_indep_loop_movupd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movupd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movupd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movupd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movupd 48(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movupd 64(%%r10),%%xmm4;"NOP(NOPCOUNT)
                "movupd 80(%%r10),%%xmm5;"NOP(NOPCOUNT)
                "movupd 96(%%r10),%%xmm6;"NOP(NOPCOUNT)
                "movupd 112(%%r10),%%xmm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "movupd %%xmm8,0(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm9,16(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm10,32(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm11,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movupd %%xmm12,64(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm13,80(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm14,96(%%r12);"NOP(NOPCOUNT)
                "movupd %%xmm15,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movupd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 160(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 176(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r13)
                "movupd 192(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movupd 208(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movupd 224(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movupd 240(%%r13),%%xmm7;"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,128,r14)
                "movupd %%xmm8,128(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm9,144(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm10,160(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm11,176(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movupd %%xmm12,192(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm13,208(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm14,224(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm15,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movupd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 288(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 304(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movupd 320(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movupd 336(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movupd 352(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movupd 368(%%r13),%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r14)
                "movupd %%xmm8,256(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm9,272(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm10,288(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm11,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movupd %%xmm12,320(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm13,336(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm14,352(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm15,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movupd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movupd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movupd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movupd 432(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movupd 448(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movupd 464(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movupd 480(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movupd 496(%%r13),%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r14)
                "movupd %%xmm8,384(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm9,400(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm10,416(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm11,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movupd %%xmm12,448(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm13,464(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm14,480(%%r14);"NOP(NOPCOUNT)
                "movupd %%xmm15,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_movupd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovupd instruction
 */
static void asm_indep_vmovupd_1(param_t *params) __attribute__((noinline));
static void asm_indep_vmovupd_1(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_vmovupd_1;"
                ".align 64,0x0;"
                "_indep_loop_vmovupd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "vmovupd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,0(%%r12);"NOP(NOPCOUNT)
                "vmovupd 32(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "vmovupd 64(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,64(%%r12);"NOP(NOPCOUNT)
                "vmovupd 96(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
                "vmovupd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,128(%%r12);"NOP(NOPCOUNT)
                "vmovupd 160(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
                "vmovupd 192(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,192(%%r12);"NOP(NOPCOUNT)
                "vmovupd 224(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "vmovupd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,256(%%r14);"NOP(NOPCOUNT)
                "vmovupd 288(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "vmovupd 320(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,320(%%r14);"NOP(NOPCOUNT)
                "vmovupd 352(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "vmovupd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,384(%%r14);"NOP(NOPCOUNT)
                "vmovupd 416(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "vmovupd 448(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,448(%%r14);"NOP(NOPCOUNT)
                "vmovupd 480(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
                "vmovupd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,512(%%r14);"NOP(NOPCOUNT)
                "vmovupd 544(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
                "vmovupd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,576(%%r14);"NOP(NOPCOUNT)
                "vmovupd 608(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
                "vmovupd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,640(%%r14);"NOP(NOPCOUNT)
                "vmovupd 672(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
                "vmovupd 704(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,704(%%r14);"NOP(NOPCOUNT)
                "vmovupd 736(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
                "vmovupd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,768(%%r14);"NOP(NOPCOUNT)
                "vmovupd 800(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
                "vmovupd 832(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,832(%%r14);"NOP(NOPCOUNT)
                "vmovupd 864(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
                "vmovupd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,896(%%r14);"NOP(NOPCOUNT)
                "vmovupd 928(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
                "vmovupd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,960(%%r14);"NOP(NOPCOUNT)
                "vmovupd 992(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd %%ymm1,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_vmovupd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovupd instruction
 */
static void asm_indep_vmovupd_2(param_t *params) __attribute__((noinline));
static void asm_indep_vmovupd_2(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_vmovupd_2;"
                ".align 64,0x0;"
                "_indep_loop_vmovupd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "vmovupd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm2,0(%%r12);"NOP(NOPCOUNT)"vmovupd %%ymm3,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "vmovupd 64(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd 96(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm2,64(%%r12);"NOP(NOPCOUNT)"vmovupd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
                "vmovupd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd 160(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm2,128(%%r12);"NOP(NOPCOUNT)"vmovupd %%ymm3,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
                "vmovupd 192(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovupd 224(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm2,192(%%r12);"NOP(NOPCOUNT)"vmovupd %%ymm3,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "vmovupd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm2,256(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm3,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "vmovupd 320(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 352(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm2,320(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm3,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "vmovupd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm2,384(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm3,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "vmovupd 448(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 480(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm2,448(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm3,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
                "vmovupd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm2,512(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm3,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
                "vmovupd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 608(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm2,576(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm3,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
                "vmovupd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 672(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm2,640(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm3,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
                "vmovupd 704(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 736(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm2,704(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm3,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
                "vmovupd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm2,768(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm3,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
                "vmovupd 832(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 864(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm2,832(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
                "vmovupd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 928(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm2,896(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm3,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
                "vmovupd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovupd 992(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd %%ymm2,960(%%r14);"NOP(NOPCOUNT)"vmovupd %%ymm3,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_vmovupd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovupd instruction
 */
static void asm_indep_vmovupd_3(param_t *params) __attribute__((noinline));
static void asm_indep_vmovupd_3(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_vmovupd_3;"
                ".align 64,0x0;"
                "_indep_loop_vmovupd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovupd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovupd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovupd %%ymm3,0(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm4,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovupd %%ymm5,64(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "vmovupd 96(%%r10),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovupd 128(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd 160(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovupd %%ymm4,128(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,160(%%r12);"NOP(NOPCOUNT)
                "add $1056,%%r10;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "vmovupd 192(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 224(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovupd 256(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "vmovupd %%ymm3,192(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm4,224(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovupd %%ymm5,256(%%r14);"NOP(NOPCOUNT)
                "add $1056,%%r12;"
                "vmovupd 288(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovupd 320(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd 352(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd %%ymm3,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovupd %%ymm4,320(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,352(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovupd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovupd 448(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovupd %%ymm3,384(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm4,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovupd %%ymm5,448(%%r14);"NOP(NOPCOUNT)
                
                "vmovupd 480(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovupd 512(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd 544(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd %%ymm3,480(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovupd %%ymm4,512(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,544(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovupd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 608(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovupd 640(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovupd %%ymm3,576(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm4,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovupd %%ymm5,640(%%r14);"NOP(NOPCOUNT)
                
                "vmovupd 672(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovupd 704(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd 736(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd %%ymm3,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovupd %%ymm4,704(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovupd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovupd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovupd %%ymm3,768(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm4,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovupd %%ymm5,832(%%r14);"NOP(NOPCOUNT)
                
                "vmovupd 864(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovupd 896(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovupd 928(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovupd %%ymm4,896(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,928(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovupd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 992(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r13)
                "vmovupd 1024(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovupd %%ymm3,960(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm4,992(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r14)
                "vmovupd %%ymm5,1024(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_vmovupd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovupd instruction
 */
static void asm_indep_vmovupd_4(param_t *params) __attribute__((noinline));
static void asm_indep_vmovupd_4(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_vmovupd_4;"
                ".align 64,0x0;"
                "_indep_loop_vmovupd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovupd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovupd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 96(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovupd %%ymm4,0(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovupd %%ymm6,64(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm7,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovupd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 160(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmovupd 192(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 224(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovupd %%ymm4,128(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovupd %%ymm6,192(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm7,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovupd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovupd 320(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 352(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovupd %%ymm4,256(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovupd %%ymm6,320(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm7,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovupd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovupd 448(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 480(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovupd %%ymm4,384(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovupd %%ymm6,448(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm7,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovupd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovupd 576(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 608(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovupd %%ymm4,512(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovupd %%ymm6,576(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm7,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovupd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 672(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovupd 704(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 736(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovupd %%ymm4,640(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovupd %%ymm6,704(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm7,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovupd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovupd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 864(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovupd %%ymm4,768(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovupd %%ymm6,832(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm7,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovupd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 928(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovupd 960(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 992(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovupd %%ymm4,896(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm5,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovupd %%ymm6,960(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm7,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_vmovupd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovupd instruction
 */
static void asm_indep_vmovupd_8(param_t *params) __attribute__((noinline));
static void asm_indep_vmovupd_8(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_vmovupd_8;"
                ".align 64,0x0;"
                "_indep_loop_vmovupd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovupd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovupd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 96(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovupd 128(%%r10),%%ymm4;"NOP(NOPCOUNT)
                "vmovupd 160(%%r10),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmovupd 192(%%r10),%%ymm6;"NOP(NOPCOUNT)
                "vmovupd 224(%%r10),%%ymm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovupd %%ymm8,0(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm9,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovupd %%ymm10,64(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm11,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovupd %%ymm12,128(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm13,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovupd %%ymm14,192(%%r12);"NOP(NOPCOUNT)
                "vmovupd %%ymm15,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovupd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovupd 320(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 352(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovupd 384(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovupd 416(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovupd 448(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovupd 480(%%r13),%%ymm7;"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovupd %%ymm8,256(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm9,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovupd %%ymm10,320(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm11,352(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovupd %%ymm12,384(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm13,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovupd %%ymm14,448(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm15,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovupd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovupd 576(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 608(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovupd 640(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovupd 672(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovupd 704(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovupd 736(%%r13),%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovupd %%ymm8,512(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm9,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovupd %%ymm10,576(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm11,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovupd %%ymm12,640(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm13,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovupd %%ymm14,704(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm15,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovupd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovupd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovupd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovupd 864(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovupd 896(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovupd 928(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovupd 960(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovupd 992(%%r13),%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovupd %%ymm8,768(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm9,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovupd %%ymm10,832(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm11,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovupd %%ymm12,896(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm13,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovupd %%ymm14,960(%%r14);"NOP(NOPCOUNT)
                "vmovupd %%ymm15,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_vmovupd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov instruction
 */
static void asm_indep_mov_1(param_t *params) __attribute__((noinline));
static void asm_indep_mov_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_mov_1;"
                ".align 64,0x0;"
                "_indep_loop_mov_1:"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,0(%%rdi);"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,8(%%rdi);"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,16(%%rdi);"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,32(%%rdi);"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,48(%%rdi);"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,64(%%rdi);"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,72(%%rdi);"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,80(%%rdi);"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,96(%%rdi);"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,104(%%rdi);"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,112(%%rdi);"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,120(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _indep_loop_mov_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov instruction
 */
static void asm_indep_mov_2(param_t *params) __attribute__((noinline));
static void asm_indep_mov_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_mov_2;"
                ".align 64,0x0;"
                "_indep_loop_mov_2:"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,0(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,8(%%rdi);"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,16(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,32(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,48(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,64(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,72(%%rdi);"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,80(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,96(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,104(%%rdi);"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,112(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)PREFETCH(LINE_PREFETCH,128,rdi)
                "mov 128(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,128(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,136(%%rdi);"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,144(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,152(%%rdi);"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,160(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,168(%%rdi);"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,176(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)PREFETCH(LINE_PREFETCH,192,rdi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,192(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,200(%%rdi);"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,208(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,216(%%rdi);"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,224(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,232(%%rdi);"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,240(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _indep_loop_mov_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov instruction
 */
static void asm_indep_mov_3(param_t *params) __attribute__((noinline));
static void asm_indep_mov_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_mov_3;"
                ".align 64,0x0;"
                "_indep_loop_mov_3:"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r10;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,rdi)
                "mov %%r12,0(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,8(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,16(%%rdi);"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,24(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,32(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)
                "mov 64(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,48(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rdi)
                "mov %%r14,64(%%rdi);"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,72(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,80(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,96(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,104(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,112(%%rdi);"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)
                "mov 128(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rdi)
                "mov %%r13,128(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,136(%%rdi);"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,144(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,152(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,160(%%rdi);"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,168(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,176(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r10;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rdi)
                "mov %%r12,192(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,200(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,208(%%rdi);"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,216(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,224(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,232(%%rdi);"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rsi)
                "mov 256(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,240(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,248(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rdi)
                "mov %%r14,256(%%rdi);"NOP(NOPCOUNT)
                "add $264,%%rsi;"
                "add $264,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _indep_loop_mov_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov instruction
 */
static void asm_indep_mov_4(param_t *params) __attribute__((noinline));
static void asm_indep_mov_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_mov_4;"
                ".align 64,0x0;"
                "_indep_loop_mov_4:"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,rdi)
                "mov %%r12,0(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,8(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,16(%%rdi);"NOP(NOPCOUNT)
                "mov %%r15,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r11;"NOP(NOPCOUNT)
                "mov %%r12,32(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,40(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,48(%%rdi);"NOP(NOPCOUNT)
                "mov %%r15,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rdi)
                "mov %%r12,64(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,72(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,80(%%rdi);"NOP(NOPCOUNT)
                "mov %%r15,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r11;"NOP(NOPCOUNT)
                "mov %%r12,96(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,104(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,112(%%rdi);"NOP(NOPCOUNT)
                "mov %%r15,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)
                "mov 128(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rdi)
                "mov %%r12,128(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,136(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,144(%%rdi);"NOP(NOPCOUNT)
                "mov %%r15,152(%%rdi);"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r11;"NOP(NOPCOUNT)
                "mov %%r12,160(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,168(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,176(%%rdi);"NOP(NOPCOUNT)
                "mov %%r15,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rdi)
                "mov %%r12,192(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,200(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,208(%%rdi);"NOP(NOPCOUNT)
                "mov %%r15,216(%%rdi);"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r11;"NOP(NOPCOUNT)
                "mov %%r12,224(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,232(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,240(%%rdi);"NOP(NOPCOUNT)
                "mov %%r15,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _indep_loop_mov_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov_clflush instruction
 */
static void asm_indep_mov_clflush_1(param_t *params) __attribute__((noinline));
static void asm_indep_mov_clflush_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_mov_clflush_1;"
                ".align 64,0x0;"
                "_indep_loop_mov_clflush_1:"
                "clflush -384(%%rdi);""clflush -320(%%rdi);"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,0(%%rdi);"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,8(%%rdi);"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,16(%%rdi);"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,32(%%rdi);"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,48(%%rdi);"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,64(%%rdi);"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,72(%%rdi);"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,80(%%rdi);"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,96(%%rdi);"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,104(%%rdi);"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,112(%%rdi);"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r8;"NOP(NOPCOUNT)"mov %%r12,120(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _indep_loop_mov_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov_clflush instruction
 */
static void asm_indep_mov_clflush_2(param_t *params) __attribute__((noinline));
static void asm_indep_mov_clflush_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_mov_clflush_2;"
                ".align 64,0x0;"
                "_indep_loop_mov_clflush_2:"
                "clflush -384(%%rdi);""clflush -320(%%rdi);"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,0(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,8(%%rdi);"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,16(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,32(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,48(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,64(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,72(%%rdi);"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,80(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,96(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,104(%%rdi);"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,112(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)PREFETCH(LINE_PREFETCH,128,rdi)
                "mov 128(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,128(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,136(%%rdi);"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,144(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,152(%%rdi);"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,160(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,168(%%rdi);"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,176(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)PREFETCH(LINE_PREFETCH,192,rdi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,192(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,200(%%rdi);"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,208(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,216(%%rdi);"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,224(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,232(%%rdi);"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov %%r12,240(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _indep_loop_mov_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov_clflush instruction
 */
static void asm_indep_mov_clflush_3(param_t *params) __attribute__((noinline));
static void asm_indep_mov_clflush_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_mov_clflush_3;"
                ".align 64,0x0;"
                "_indep_loop_mov_clflush_3:"
                "clflush -448(%%rdi);clflush -384(%%rdi);""clflush -320(%%rdi);"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r10;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,rdi)
                "mov %%r12,0(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,8(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,16(%%rdi);"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,24(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,32(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)
                "mov 64(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,48(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rdi)
                "mov %%r14,64(%%rdi);"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,72(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,80(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,96(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,104(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,112(%%rdi);"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)
                "mov 128(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rdi)
                "mov %%r13,128(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,136(%%rdi);"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,144(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,152(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,160(%%rdi);"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,168(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,176(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r10;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rdi)
                "mov %%r12,192(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,200(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,208(%%rdi);"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,216(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,224(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,232(%%rdi);"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rsi)
                "mov 256(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov %%r12,240(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,248(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rdi)
                "mov %%r14,256(%%rdi);"NOP(NOPCOUNT)
                "add $264,%%rsi;"
                "add $264,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _indep_loop_mov_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using mov_clflush instruction
 */
static void asm_indep_mov_clflush_4(param_t *params) __attribute__((noinline));
static void asm_indep_mov_clflush_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_mov_clflush_4;"
                ".align 64,0x0;"
                "_indep_loop_mov_clflush_4:"
                "clflush -384(%%rdi);""clflush -320(%%rdi);"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,rdi)
                "mov %%r12,0(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,8(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,16(%%rdi);"NOP(NOPCOUNT)
                "mov %%r15,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r11;"NOP(NOPCOUNT)
                "mov %%r12,32(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,40(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,48(%%rdi);"NOP(NOPCOUNT)
                "mov %%r15,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rdi)
                "mov %%r12,64(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,72(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,80(%%rdi);"NOP(NOPCOUNT)
                "mov %%r15,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r11;"NOP(NOPCOUNT)
                "mov %%r12,96(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,104(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,112(%%rdi);"NOP(NOPCOUNT)
                "mov %%r15,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)
                "mov 128(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rdi)
                "mov %%r12,128(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,136(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,144(%%rdi);"NOP(NOPCOUNT)
                "mov %%r15,152(%%rdi);"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r11;"NOP(NOPCOUNT)
                "mov %%r12,160(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,168(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,176(%%rdi);"NOP(NOPCOUNT)
                "mov %%r15,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rdi)
                "mov %%r12,192(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,200(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,208(%%rdi);"NOP(NOPCOUNT)
                "mov %%r15,216(%%rdi);"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r11;"NOP(NOPCOUNT)
                "mov %%r12,224(%%rdi);"NOP(NOPCOUNT)
                "mov %%r13,232(%%rdi);"NOP(NOPCOUNT)
                "mov %%r14,240(%%rdi);"NOP(NOPCOUNT)
                "mov %%r15,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _indep_loop_mov_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movnti instruction
 */
static void asm_indep_movnti_1(param_t *params) __attribute__((noinline));
static void asm_indep_movnti_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movnti_1;"
                ".align 64,0x0;"
                "_indep_loop_movnti_1:"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r12,0(%%rdi);"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r12,8(%%rdi);"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r12,16(%%rdi);"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r12,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r12,32(%%rdi);"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r12,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r12,48(%%rdi);"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r12,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r12,64(%%rdi);"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r12,72(%%rdi);"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r12,80(%%rdi);"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r12,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r12,96(%%rdi);"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r12,104(%%rdi);"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r12,112(%%rdi);"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r8;"NOP(NOPCOUNT)"movnti %%r12,120(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _indep_loop_movnti_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movnti instruction
 */
static void asm_indep_movnti_2(param_t *params) __attribute__((noinline));
static void asm_indep_movnti_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movnti_2;"
                ".align 64,0x0;"
                "_indep_loop_movnti_2:"
                PREFETCH(LINE_PREFETCH,0,rsi)PREFETCH(LINE_PREFETCH,0,rdi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r12,0(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,8(%%rdi);"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r12,16(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r12,32(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r12,48(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)PREFETCH(LINE_PREFETCH,64,rdi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r12,64(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,72(%%rdi);"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r12,80(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r12,96(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,104(%%rdi);"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r12,112(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)PREFETCH(LINE_PREFETCH,128,rdi)
                "mov 128(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r12,128(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,136(%%rdi);"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r12,144(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,152(%%rdi);"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r12,160(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,168(%%rdi);"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r12,176(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)PREFETCH(LINE_PREFETCH,192,rdi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r12,192(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,200(%%rdi);"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r12,208(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,216(%%rdi);"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r12,224(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,232(%%rdi);"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r9;"NOP(NOPCOUNT)
                "movnti %%r12,240(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _indep_loop_movnti_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movnti instruction
 */
static void asm_indep_movnti_3(param_t *params) __attribute__((noinline));
static void asm_indep_movnti_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movnti_3;"
                ".align 64,0x0;"
                "_indep_loop_movnti_3:"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r10;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,rdi)
                "movnti %%r12,0(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,8(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r14,16(%%rdi);"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r12,24(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,32(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r14,40(%%rdi);"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)
                "mov 64(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r12,48(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rdi)
                "movnti %%r14,64(%%rdi);"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r12,72(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,80(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r14,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r12,96(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,104(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r14,112(%%rdi);"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r8;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)
                "mov 128(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r12,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rdi)
                "movnti %%r13,128(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r14,136(%%rdi);"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r12,144(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,152(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r14,160(%%rdi);"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r12,168(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,176(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r14,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r10;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rdi)
                "movnti %%r12,192(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,200(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r14,208(%%rdi);"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r12,216(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,224(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r14,232(%%rdi);"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r9;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rsi)
                "mov 256(%%rsi),%%r10;"NOP(NOPCOUNT)
                "movnti %%r12,240(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,248(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,rdi)
                "movnti %%r14,256(%%rdi);"NOP(NOPCOUNT)
                "add $264,%%rsi;"
                "add $264,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _indep_loop_movnti_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movnti instruction
 */
static void asm_indep_movnti_4(param_t *params) __attribute__((noinline));
static void asm_indep_movnti_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%rsi;"
                "mov %%rdx,%%rdi;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movnti_4;"
                ".align 64,0x0;"
                "_indep_loop_movnti_4:"
                PREFETCH(LINE_PREFETCH,0,rsi)
                "mov 0(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 8(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 16(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 24(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,rdi)
                "movnti %%r12,0(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,8(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r14,16(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r15,24(%%rdi);"NOP(NOPCOUNT)
                "mov 32(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 40(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 48(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 56(%%rsi),%%r11;"NOP(NOPCOUNT)
                "movnti %%r12,32(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,40(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r14,48(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r15,56(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rsi)
                "mov 64(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 72(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 80(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 88(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,rdi)
                "movnti %%r12,64(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,72(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r14,80(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r15,88(%%rdi);"NOP(NOPCOUNT)
                "mov 96(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 104(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 112(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 120(%%rsi),%%r11;"NOP(NOPCOUNT)
                "movnti %%r12,96(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,104(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r14,112(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r15,120(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rsi)
                "mov 128(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 136(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 144(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 152(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,rdi)
                "movnti %%r12,128(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,136(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r14,144(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r15,152(%%rdi);"NOP(NOPCOUNT)
                "mov 160(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 168(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 176(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 184(%%rsi),%%r11;"NOP(NOPCOUNT)
                "movnti %%r12,160(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,168(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r14,176(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r15,184(%%rdi);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rsi)
                "mov 192(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 200(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 208(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 216(%%rsi),%%r11;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,rdi)
                "movnti %%r12,192(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,200(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r14,208(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r15,216(%%rdi);"NOP(NOPCOUNT)
                "mov 224(%%rsi),%%r8;"NOP(NOPCOUNT)
                "mov 232(%%rsi),%%r9;"NOP(NOPCOUNT)
                "mov 240(%%rsi),%%r10;"NOP(NOPCOUNT)
                "mov 248(%%rsi),%%r11;"NOP(NOPCOUNT)
                "movnti %%r12,224(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r13,232(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r14,240(%%rdi);"NOP(NOPCOUNT)
                "movnti %%r15,248(%%rdi);"NOP(NOPCOUNT)
                "add $256,%%rsi;"
                "add $256,%%rdi;"

                "sub $1,%%rcx;"
                "jnz _indep_loop_movnti_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movntpd instruction
 */
static void asm_indep_movntpd_1(param_t *params) __attribute__((noinline));
static void asm_indep_movntpd_1(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movntpd_1;"
                ".align 64,0x0;"
                "_indep_loop_movntpd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,0(%%r12);"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,16(%%r12);"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,32(%%r12);"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movapd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,64(%%r12);"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,80(%%r12);"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,96(%%r12);"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movapd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,128(%%r14);"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,144(%%r14);"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,160(%%r14);"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movapd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,192(%%r14);"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,208(%%r14);"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,224(%%r14);"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movapd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,256(%%r14);"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,272(%%r14);"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,288(%%r14);"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movapd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,320(%%r14);"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,336(%%r14);"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,352(%%r14);"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,384(%%r14);"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,400(%%r14);"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,416(%%r14);"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movapd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,448(%%r14);"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,464(%%r14);"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,480(%%r14);"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm0;"NOP(NOPCOUNT)"movntpd %%xmm1,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_movntpd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movntpd instruction
 */
static void asm_indep_movntpd_2(param_t *params) __attribute__((noinline));
static void asm_indep_movntpd_2(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movntpd_2;"
                ".align 64,0x0;"
                "_indep_loop_movntpd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm2,0(%%r12);"NOP(NOPCOUNT)"movntpd %%xmm3,16(%%r12);"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd 48(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm2,32(%%r12);"NOP(NOPCOUNT)"movntpd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "movapd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd 80(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm2,64(%%r12);"NOP(NOPCOUNT)"movntpd %%xmm3,80(%%r12);"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm0;"NOP(NOPCOUNT)"movapd 112(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm2,96(%%r12);"NOP(NOPCOUNT)"movntpd %%xmm3,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)PREFETCH(LINE_PREFETCH,128,r14)
                "movapd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm2,128(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm3,144(%%r14);"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 176(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm2,160(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm3,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)PREFETCH(LINE_PREFETCH,192,r14)
                "movapd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm2,192(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm3,208(%%r14);"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 240(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm2,224(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm3,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "movapd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm2,256(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm3,272(%%r14);"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 304(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm2,288(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm3,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "movapd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 336(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm2,320(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm3,336(%%r14);"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 368(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm2,352(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm3,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm2,384(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm3,400(%%r14);"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 432(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm2,416(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "movapd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 464(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm2,448(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm3,464(%%r14);"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)"movapd 496(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movntpd %%xmm2,480(%%r14);"NOP(NOPCOUNT)"movntpd %%xmm3,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_movntpd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movntpd instruction
 */
static void asm_indep_movntpd_3(param_t *params) __attribute__((noinline));
static void asm_indep_movntpd_3(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movntpd_3;"
                ".align 64,0x0;"
                "_indep_loop_movntpd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movntpd %%xmm3,0(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm4,16(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm5,32(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "movapd 48(%%r10),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm3,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movntpd %%xmm4,64(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm5,80(%%r12);"NOP(NOPCOUNT)
                "add $528,%%r10;"
                "movapd 96(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 112(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm3,96(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm4,112(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movntpd %%xmm5,128(%%r14);"NOP(NOPCOUNT)
                "add $528,%%r12;"
                "movapd 144(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm3,144(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm4,160(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,176(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movntpd %%xmm3,192(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm4,208(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,224(%%r14);"NOP(NOPCOUNT)
                
                "movapd 240(%%r13),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm3,240(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movntpd %%xmm4,256(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,272(%%r14);"NOP(NOPCOUNT)
                
                "movapd 288(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm3,288(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm4,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movntpd %%xmm5,320(%%r14);"NOP(NOPCOUNT)
                
                "movapd 336(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm3,336(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm4,352(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movntpd %%xmm3,384(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm4,400(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,416(%%r14);"NOP(NOPCOUNT)
                
                "movapd 432(%%r13),%%xmm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm3,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movntpd %%xmm4,448(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,464(%%r14);"NOP(NOPCOUNT)
                
                "movapd 480(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "movapd 512(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movntpd %%xmm3,480(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm4,496(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "movntpd %%xmm5,512(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_movntpd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movntpd instruction
 */
static void asm_indep_movntpd_4(param_t *params) __attribute__((noinline));
static void asm_indep_movntpd_4(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movntpd_4;"
                ".align 64,0x0;"
                "_indep_loop_movntpd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "movntpd %%xmm4,0(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm5,16(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm6,32(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm7,48(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movntpd %%xmm4,64(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm5,80(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm6,96(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm7,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r14)
                "movntpd %%xmm4,128(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,144(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm6,160(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm7,176(%%r14);"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movntpd %%xmm4,192(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,208(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm6,224(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm7,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "movntpd %%xmm4,256(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,272(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm6,288(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm7,304(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movntpd %%xmm4,320(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,336(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm6,352(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm7,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "movntpd %%xmm4,384(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,400(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm6,416(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm7,432(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movntpd %%xmm4,448(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm5,464(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm6,480(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm7,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_movntpd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using movntpd instruction
 */
static void asm_indep_movntpd_8(param_t *params) __attribute__((noinline));
static void asm_indep_movntpd_8(param_t *params)
{
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_movntpd_8;"
                ".align 64,0x0;"
                "_indep_loop_movntpd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "movapd 0(%%r10),%%xmm0;"NOP(NOPCOUNT)
                "movapd 16(%%r10),%%xmm1;"NOP(NOPCOUNT)
                "movapd 32(%%r10),%%xmm2;"NOP(NOPCOUNT)
                "movapd 48(%%r10),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "movapd 64(%%r10),%%xmm4;"NOP(NOPCOUNT)
                "movapd 80(%%r10),%%xmm5;"NOP(NOPCOUNT)
                "movapd 96(%%r10),%%xmm6;"NOP(NOPCOUNT)
                "movapd 112(%%r10),%%xmm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "movntpd %%xmm8,0(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm9,16(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm10,32(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm11,48(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "movntpd %%xmm12,64(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm13,80(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm14,96(%%r12);"NOP(NOPCOUNT)
                "movntpd %%xmm15,112(%%r12);"NOP(NOPCOUNT)
                "add $512,%%r10;"
                PREFETCH(LINE_PREFETCH,128,r13)
                "movapd 128(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 144(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 160(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 176(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r13)
                "movapd 192(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movapd 208(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movapd 224(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movapd 240(%%r13),%%xmm7;"NOP(NOPCOUNT)
                "add $512,%%r12;"
                PREFETCH(LINE_PREFETCH,128,r14)
                "movntpd %%xmm8,128(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm9,144(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm10,160(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm11,176(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "movntpd %%xmm12,192(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm13,208(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm14,224(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm15,240(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r13)
                "movapd 256(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 272(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 288(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 304(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "movapd 320(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movapd 336(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movapd 352(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movapd 368(%%r13),%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,256,r14)
                "movntpd %%xmm8,256(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm9,272(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm10,288(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm11,304(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "movntpd %%xmm12,320(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm13,336(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm14,352(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm15,368(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "movapd 384(%%r13),%%xmm0;"NOP(NOPCOUNT)
                "movapd 400(%%r13),%%xmm1;"NOP(NOPCOUNT)
                "movapd 416(%%r13),%%xmm2;"NOP(NOPCOUNT)
                "movapd 432(%%r13),%%xmm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "movapd 448(%%r13),%%xmm4;"NOP(NOPCOUNT)
                "movapd 464(%%r13),%%xmm5;"NOP(NOPCOUNT)
                "movapd 480(%%r13),%%xmm6;"NOP(NOPCOUNT)
                "movapd 496(%%r13),%%xmm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r14)
                "movntpd %%xmm8,384(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm9,400(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm10,416(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm11,432(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "movntpd %%xmm12,448(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm13,464(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm14,480(%%r14);"NOP(NOPCOUNT)
                "movntpd %%xmm15,496(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_movntpd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovntpd instruction
 */
static void asm_indep_vmovntpd_1(param_t *params) __attribute__((noinline));
static void asm_indep_vmovntpd_1(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_vmovntpd_1;"
                ".align 64,0x0;"
                "_indep_loop_vmovntpd_1:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,0(%%r12);"NOP(NOPCOUNT)
                "vmovapd 32(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "vmovapd 64(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,64(%%r12);"NOP(NOPCOUNT)
                "vmovapd 96(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
                "vmovapd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,128(%%r12);"NOP(NOPCOUNT)
                "vmovapd 160(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
                "vmovapd 192(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,192(%%r12);"NOP(NOPCOUNT)
                "vmovapd 224(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "vmovapd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,256(%%r14);"NOP(NOPCOUNT)
                "vmovapd 288(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "vmovapd 320(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,320(%%r14);"NOP(NOPCOUNT)
                "vmovapd 352(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "vmovapd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,384(%%r14);"NOP(NOPCOUNT)
                "vmovapd 416(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "vmovapd 448(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,448(%%r14);"NOP(NOPCOUNT)
                "vmovapd 480(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
                "vmovapd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,512(%%r14);"NOP(NOPCOUNT)
                "vmovapd 544(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
                "vmovapd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,576(%%r14);"NOP(NOPCOUNT)
                "vmovapd 608(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
                "vmovapd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,640(%%r14);"NOP(NOPCOUNT)
                "vmovapd 672(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
                "vmovapd 704(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,704(%%r14);"NOP(NOPCOUNT)
                "vmovapd 736(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,768(%%r14);"NOP(NOPCOUNT)
                "vmovapd 800(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
                "vmovapd 832(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,832(%%r14);"NOP(NOPCOUNT)
                "vmovapd 864(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
                "vmovapd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,896(%%r14);"NOP(NOPCOUNT)
                "vmovapd 928(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
                "vmovapd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,960(%%r14);"NOP(NOPCOUNT)
                "vmovapd 992(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovntpd %%ymm1,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_vmovntpd_1;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovntpd instruction
 */
static void asm_indep_vmovntpd_2(param_t *params) __attribute__((noinline));
static void asm_indep_vmovntpd_2(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_vmovntpd_2;"
                ".align 64,0x0;"
                "_indep_loop_vmovntpd_2:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)PREFETCH(LINE_PREFETCH,0,r12)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,0(%%r12);"NOP(NOPCOUNT)"vmovntpd %%ymm3,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)PREFETCH(LINE_PREFETCH,64,r12)
                "vmovapd 64(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd 96(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,64(%%r12);"NOP(NOPCOUNT)"vmovntpd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)PREFETCH(LINE_PREFETCH,128,r12)
                "vmovapd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd 160(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,128(%%r12);"NOP(NOPCOUNT)"vmovntpd %%ymm3,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)PREFETCH(LINE_PREFETCH,192,r12)
                "vmovapd 192(%%r10),%%ymm0;"NOP(NOPCOUNT)"vmovapd 224(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,192(%%r12);"NOP(NOPCOUNT)"vmovntpd %%ymm3,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)PREFETCH(LINE_PREFETCH,256,r14)
                "vmovapd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,256(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm3,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)PREFETCH(LINE_PREFETCH,320,r14)
                "vmovapd 320(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 352(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,320(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm3,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)PREFETCH(LINE_PREFETCH,384,r14)
                "vmovapd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,384(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm3,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)PREFETCH(LINE_PREFETCH,448,r14)
                "vmovapd 448(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 480(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,448(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm3,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)PREFETCH(LINE_PREFETCH,512,r14)
                "vmovapd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,512(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm3,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)PREFETCH(LINE_PREFETCH,576,r14)
                "vmovapd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 608(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,576(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm3,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)PREFETCH(LINE_PREFETCH,640,r14)
                "vmovapd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 672(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,640(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm3,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)PREFETCH(LINE_PREFETCH,704,r14)
                "vmovapd 704(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 736(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,704(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm3,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)PREFETCH(LINE_PREFETCH,768,r14)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,768(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm3,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)PREFETCH(LINE_PREFETCH,832,r14)
                "vmovapd 832(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 864(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,832(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)PREFETCH(LINE_PREFETCH,896,r14)
                "vmovapd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 928(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,896(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm3,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)PREFETCH(LINE_PREFETCH,960,r14)
                "vmovapd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)"vmovapd 992(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovntpd %%ymm2,960(%%r14);"NOP(NOPCOUNT)"vmovntpd %%ymm3,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_vmovntpd_2;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovntpd instruction
 */
static void asm_indep_vmovntpd_3(param_t *params) __attribute__((noinline));
static void asm_indep_vmovntpd_3(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_vmovntpd_3;"
                ".align 64,0x0;"
                "_indep_loop_vmovntpd_3:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovapd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovntpd %%ymm3,0(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm4,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovntpd %%ymm5,64(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                "vmovapd 96(%%r10),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovapd 128(%%r10),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 160(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovntpd %%ymm4,128(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,160(%%r12);"NOP(NOPCOUNT)
                "add $1056,%%r10;"
                PREFETCH(LINE_PREFETCH,192,r13)
                "vmovapd 192(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 224(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovapd 256(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r14)
                "vmovntpd %%ymm3,192(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm4,224(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovntpd %%ymm5,256(%%r14);"NOP(NOPCOUNT)
                "add $1056,%%r12;"
                "vmovapd 288(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovapd 320(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 352(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovntpd %%ymm4,320(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,352(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovapd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovapd 448(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovntpd %%ymm3,384(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm4,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovntpd %%ymm5,448(%%r14);"NOP(NOPCOUNT)
                
                "vmovapd 480(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovapd 512(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 544(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,480(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovntpd %%ymm4,512(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,544(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovapd 576(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 608(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovapd 640(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovntpd %%ymm3,576(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm4,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovntpd %%ymm5,640(%%r14);"NOP(NOPCOUNT)
                
                "vmovapd 672(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovapd 704(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 736(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovntpd %%ymm4,704(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovapd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovntpd %%ymm3,768(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm4,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovntpd %%ymm5,832(%%r14);"NOP(NOPCOUNT)
                
                "vmovapd 864(%%r13),%%ymm0;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovapd 896(%%r13),%%ymm1;"NOP(NOPCOUNT)
                "vmovapd 928(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovntpd %%ymm3,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovntpd %%ymm4,896(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,928(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovapd 960(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 992(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r13)
                "vmovapd 1024(%%r13),%%ymm2;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovntpd %%ymm3,960(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm4,992(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,1024,r14)
                "vmovntpd %%ymm5,1024(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_vmovntpd_3;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovntpd instruction
 */
static void asm_indep_vmovntpd_4(param_t *params) __attribute__((noinline));
static void asm_indep_vmovntpd_4(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_vmovntpd_4;"
                ".align 64,0x0;"
                "_indep_loop_vmovntpd_4:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovapd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 96(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovntpd %%ymm4,0(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovntpd %%ymm6,64(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm7,96(%%r12);"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovapd 128(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 160(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmovapd 192(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 224(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovntpd %%ymm4,128(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovntpd %%ymm6,192(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm7,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovapd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovapd 320(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 352(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovntpd %%ymm4,256(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovntpd %%ymm6,320(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm7,352(%%r14);"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovapd 384(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 416(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovapd 448(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 480(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovntpd %%ymm4,384(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovntpd %%ymm6,448(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm7,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovapd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovapd 576(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 608(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovntpd %%ymm4,512(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovntpd %%ymm6,576(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm7,608(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovapd 640(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 672(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovapd 704(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 736(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovntpd %%ymm4,640(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovntpd %%ymm6,704(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm7,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovapd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 864(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovntpd %%ymm4,768(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovntpd %%ymm6,832(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm7,864(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovapd 896(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 928(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovapd 960(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 992(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovntpd %%ymm4,896(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm5,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovntpd %%ymm6,960(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm7,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_vmovntpd_4;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}


/** assembler implementation of bandwidth measurement using vmovntpd instruction
 */
static void asm_indep_vmovntpd_8(param_t *params) __attribute__((noinline));
static void asm_indep_vmovntpd_8(param_t *params)
{
   int i;

   //wait for transition to AVX frequency
   if (AVX_STARTUP_REG_OPS) for(i=0;i<AVX_STARTUP_REG_OPS;i++){
     __asm__ __volatile__("vmovdqa %%ymm0, %%ymm1;"::: "xmm0", "xmm1");
   }
    #ifdef USE_PAPI
    if (params->num_events) PAPI_reset(params->Eventset);
    #endif
    /*
     * Input:  RBX: addr1 (pointer to the source buffer)
     *         RCX: passes (number of loop iterations)
     *         RDX: addr2 (pointer to destination buffer)
     * Output: RAX: stop timestamp - start timestamp
     */
    __asm__ __volatile__(
                "sub $16,%%rsp;"	//fix unexplainable stack pointer bug
                "mov %%rbx,%%r10;"
                "mov %%rdx,%%r12;"

                TIMESTAMP
                SERIALIZE
                "jmp _indep_loop_vmovntpd_8;"
                ".align 64,0x0;"
                "_indep_loop_vmovntpd_8:"
                "mov %%r10, %%r13;"
                PREFETCH(LINE_PREFETCH,0,r10)
                "vmovapd 0(%%r10),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 32(%%r10),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r10)
                "vmovapd 64(%%r10),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 96(%%r10),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r10)
                "vmovapd 128(%%r10),%%ymm4;"NOP(NOPCOUNT)
                "vmovapd 160(%%r10),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r10)
                "vmovapd 192(%%r10),%%ymm6;"NOP(NOPCOUNT)
                "vmovapd 224(%%r10),%%ymm7;"NOP(NOPCOUNT)
                "mov %%r12, %%r14;"
                PREFETCH(LINE_PREFETCH,0,r12)
                "vmovntpd %%ymm8,0(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm9,32(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,64,r12)
                "vmovntpd %%ymm10,64(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm11,96(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,128,r12)
                "vmovntpd %%ymm12,128(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm13,160(%%r12);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,192,r12)
                "vmovntpd %%ymm14,192(%%r12);"NOP(NOPCOUNT)
                "vmovntpd %%ymm15,224(%%r12);"NOP(NOPCOUNT)
                "add $1024,%%r10;"
                PREFETCH(LINE_PREFETCH,256,r13)
                "vmovapd 256(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 288(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r13)
                "vmovapd 320(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 352(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r13)
                "vmovapd 384(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovapd 416(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r13)
                "vmovapd 448(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovapd 480(%%r13),%%ymm7;"NOP(NOPCOUNT)
                "add $1024,%%r12;"
                PREFETCH(LINE_PREFETCH,256,r14)
                "vmovntpd %%ymm8,256(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm9,288(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,320,r14)
                "vmovntpd %%ymm10,320(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm11,352(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,384,r14)
                "vmovntpd %%ymm12,384(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm13,416(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,448,r14)
                "vmovntpd %%ymm14,448(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm15,480(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r13)
                "vmovapd 512(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 544(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r13)
                "vmovapd 576(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 608(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r13)
                "vmovapd 640(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovapd 672(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r13)
                "vmovapd 704(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovapd 736(%%r13),%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,512,r14)
                "vmovntpd %%ymm8,512(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm9,544(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,576,r14)
                "vmovntpd %%ymm10,576(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm11,608(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,640,r14)
                "vmovntpd %%ymm12,640(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm13,672(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,704,r14)
                "vmovntpd %%ymm14,704(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm15,736(%%r14);"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r13)
                "vmovapd 768(%%r13),%%ymm0;"NOP(NOPCOUNT)
                "vmovapd 800(%%r13),%%ymm1;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r13)
                "vmovapd 832(%%r13),%%ymm2;"NOP(NOPCOUNT)
                "vmovapd 864(%%r13),%%ymm3;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r13)
                "vmovapd 896(%%r13),%%ymm4;"NOP(NOPCOUNT)
                "vmovapd 928(%%r13),%%ymm5;"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r13)
                "vmovapd 960(%%r13),%%ymm6;"NOP(NOPCOUNT)
                "vmovapd 992(%%r13),%%ymm7;"NOP(NOPCOUNT)
                
                PREFETCH(LINE_PREFETCH,768,r14)
                "vmovntpd %%ymm8,768(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm9,800(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,832,r14)
                "vmovntpd %%ymm10,832(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm11,864(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,896,r14)
                "vmovntpd %%ymm12,896(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm13,928(%%r14);"NOP(NOPCOUNT)
                PREFETCH(LINE_PREFETCH,960,r14)
                "vmovntpd %%ymm14,960(%%r14);"NOP(NOPCOUNT)
                "vmovntpd %%ymm15,992(%%r14);"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _indep_loop_vmovntpd_8;"

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                "sub %%rbx,%%rax;"
                "add $16,%%rsp;"	//fix unexplainable stack pointer bug
                : "=a" (params->rax)
                : "b"(params->addr_1), "c" (params->passes), "d" (params->addr_2)
                : "%r10", "%r12", "%r13", "%r14", "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15", "memory", "memory"

    );             
    #ifdef USE_PAPI
    if (params->num_events) PAPI_read(params->Eventset,params->values);
    #endif
}

/** function that performs the measurement
 *   - entry point for BenchIT framework (called by bi_entry())
 */
void _work(unsigned long long memsize, volatile mydata_t* data, double **results)
{
	register unsigned long long aligned_addr;	  /* used as pointer to param_t structure (PARAMS) */
	void (*asm_work)(param_t*)=NULL;                  /* pointer to selected measurement routine */
        int max_threads;

 /* select asm routine according to selected function and method and burst length */
	switch(data->function)
	{
		case 0: //movapd
			switch (data->method)
			{
				case 1: // copy
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_copy_movapd_1; break;
						case 2: asm_work=&asm_copy_movapd_2; break;
						case 3: asm_work=&asm_copy_movapd_3; break;
						case 4: asm_work=&asm_copy_movapd_4; break;
						case 8: asm_work=&asm_copy_movapd_8; break;
						default: break;
					}
					break;
				case 2: // scale
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_scale_movapd_1; break;
						case 2: asm_work=&asm_scale_movapd_2; break;
						case 3: asm_work=&asm_scale_movapd_3; break;
						case 4: asm_work=&asm_scale_movapd_4; break;
						case 8: asm_work=&asm_scale_movapd_8; break;
						default: break;
					}
					break;
				case 4: // indep
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_indep_movapd_1; break;
						case 2: asm_work=&asm_indep_movapd_2; break;
						case 3: asm_work=&asm_indep_movapd_3; break;
						case 4: asm_work=&asm_indep_movapd_4; break;
						case 8: asm_work=&asm_indep_movapd_8; break;
						default: break;
					}
					break;
				default: break;
			}
			break;
		case 1: //vmovapd
			switch (data->method)
			{
				case 1: // copy
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_copy_vmovapd_1; break;
						case 2: asm_work=&asm_copy_vmovapd_2; break;
						case 3: asm_work=&asm_copy_vmovapd_3; break;
						case 4: asm_work=&asm_copy_vmovapd_4; break;
						case 8: asm_work=&asm_copy_vmovapd_8; break;
						default: break;
					}
					break;
				case 2: // scale
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_scale_vmovapd_1; break;
						case 2: asm_work=&asm_scale_vmovapd_2; break;
						case 3: asm_work=&asm_scale_vmovapd_3; break;
						case 4: asm_work=&asm_scale_vmovapd_4; break;
						case 8: asm_work=&asm_scale_vmovapd_8; break;
						default: break;
					}
					break;
				case 4: // indep
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_indep_vmovapd_1; break;
						case 2: asm_work=&asm_indep_vmovapd_2; break;
						case 3: asm_work=&asm_indep_vmovapd_3; break;
						case 4: asm_work=&asm_indep_vmovapd_4; break;
						case 8: asm_work=&asm_indep_vmovapd_8; break;
						default: break;
					}
					break;
				default: break;
			}
			break;
		case 2: //movupd
			switch (data->method)
			{
				case 1: // copy
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_copy_movupd_1; break;
						case 2: asm_work=&asm_copy_movupd_2; break;
						case 3: asm_work=&asm_copy_movupd_3; break;
						case 4: asm_work=&asm_copy_movupd_4; break;
						case 8: asm_work=&asm_copy_movupd_8; break;
						default: break;
					}
					break;
				case 2: // scale
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_scale_movupd_1; break;
						case 2: asm_work=&asm_scale_movupd_2; break;
						case 3: asm_work=&asm_scale_movupd_3; break;
						case 4: asm_work=&asm_scale_movupd_4; break;
						case 8: asm_work=&asm_scale_movupd_8; break;
						default: break;
					}
					break;
				case 4: // indep
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_indep_movupd_1; break;
						case 2: asm_work=&asm_indep_movupd_2; break;
						case 3: asm_work=&asm_indep_movupd_3; break;
						case 4: asm_work=&asm_indep_movupd_4; break;
						case 8: asm_work=&asm_indep_movupd_8; break;
						default: break;
					}
					break;
				default: break;
			}
			break;
		case 3: //vmovupd
			switch (data->method)
			{
				case 1: // copy
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_copy_vmovupd_1; break;
						case 2: asm_work=&asm_copy_vmovupd_2; break;
						case 3: asm_work=&asm_copy_vmovupd_3; break;
						case 4: asm_work=&asm_copy_vmovupd_4; break;
						case 8: asm_work=&asm_copy_vmovupd_8; break;
						default: break;
					}
					break;
				case 2: // scale
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_scale_vmovupd_1; break;
						case 2: asm_work=&asm_scale_vmovupd_2; break;
						case 3: asm_work=&asm_scale_vmovupd_3; break;
						case 4: asm_work=&asm_scale_vmovupd_4; break;
						case 8: asm_work=&asm_scale_vmovupd_8; break;
						default: break;
					}
					break;
				case 4: // indep
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_indep_vmovupd_1; break;
						case 2: asm_work=&asm_indep_vmovupd_2; break;
						case 3: asm_work=&asm_indep_vmovupd_3; break;
						case 4: asm_work=&asm_indep_vmovupd_4; break;
						case 8: asm_work=&asm_indep_vmovupd_8; break;
						default: break;
					}
					break;
				default: break;
			}
			break;
		case 4: //mov
			switch (data->method)
			{
				case 1: // copy
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_copy_mov_1; break;
						case 2: asm_work=&asm_copy_mov_2; break;
						case 3: asm_work=&asm_copy_mov_3; break;
						case 4: asm_work=&asm_copy_mov_4; break;
						default: break;
					}
					break;
				case 2: // scale
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_scale_mov_1; break;
						case 2: asm_work=&asm_scale_mov_2; break;
						case 3: asm_work=&asm_scale_mov_3; break;
						case 4: asm_work=&asm_scale_mov_4; break;
						default: break;
					}
					break;
				case 4: // indep
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_indep_mov_1; break;
						case 2: asm_work=&asm_indep_mov_2; break;
						case 3: asm_work=&asm_indep_mov_3; break;
						case 4: asm_work=&asm_indep_mov_4; break;
						default: break;
					}
					break;
				default: break;
			}
			break;
		case 5: //mov_clflush
			switch (data->method)
			{
				case 1: // copy
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_copy_mov_clflush_1; break;
						case 2: asm_work=&asm_copy_mov_clflush_2; break;
						case 3: asm_work=&asm_copy_mov_clflush_3; break;
						case 4: asm_work=&asm_copy_mov_clflush_4; break;
						default: break;
					}
					break;
				case 2: // scale
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_scale_mov_clflush_1; break;
						case 2: asm_work=&asm_scale_mov_clflush_2; break;
						case 3: asm_work=&asm_scale_mov_clflush_3; break;
						case 4: asm_work=&asm_scale_mov_clflush_4; break;
						default: break;
					}
					break;
				case 4: // indep
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_indep_mov_clflush_1; break;
						case 2: asm_work=&asm_indep_mov_clflush_2; break;
						case 3: asm_work=&asm_indep_mov_clflush_3; break;
						case 4: asm_work=&asm_indep_mov_clflush_4; break;
						default: break;
					}
					break;
				default: break;
			}
			break;
		case 6: //movnti
			switch (data->method)
			{
				case 1: // copy
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_copy_movnti_1; break;
						case 2: asm_work=&asm_copy_movnti_2; break;
						case 3: asm_work=&asm_copy_movnti_3; break;
						case 4: asm_work=&asm_copy_movnti_4; break;
						default: break;
					}
					break;
				case 2: // scale
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_scale_movnti_1; break;
						case 2: asm_work=&asm_scale_movnti_2; break;
						case 3: asm_work=&asm_scale_movnti_3; break;
						case 4: asm_work=&asm_scale_movnti_4; break;
						default: break;
					}
					break;
				case 4: // indep
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_indep_movnti_1; break;
						case 2: asm_work=&asm_indep_movnti_2; break;
						case 3: asm_work=&asm_indep_movnti_3; break;
						case 4: asm_work=&asm_indep_movnti_4; break;
						default: break;
					}
					break;
				default: break;
			}
			break;
		case 7: //movntpd
			switch (data->method)
			{
				case 1: // copy
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_copy_movntpd_1; break;
						case 2: asm_work=&asm_copy_movntpd_2; break;
						case 3: asm_work=&asm_copy_movntpd_3; break;
						case 4: asm_work=&asm_copy_movntpd_4; break;
						case 8: asm_work=&asm_copy_movntpd_8; break;
						default: break;
					}
					break;
				case 2: // scale
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_scale_movntpd_1; break;
						case 2: asm_work=&asm_scale_movntpd_2; break;
						case 3: asm_work=&asm_scale_movntpd_3; break;
						case 4: asm_work=&asm_scale_movntpd_4; break;
						case 8: asm_work=&asm_scale_movntpd_8; break;
						default: break;
					}
					break;
				case 4: // indep
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_indep_movntpd_1; break;
						case 2: asm_work=&asm_indep_movntpd_2; break;
						case 3: asm_work=&asm_indep_movntpd_3; break;
						case 4: asm_work=&asm_indep_movntpd_4; break;
						case 8: asm_work=&asm_indep_movntpd_8; break;
						default: break;
					}
					break;
				default: break;
			}
			break;
		case 8: //vmovntpd
			switch (data->method)
			{
				case 1: // copy
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_copy_vmovntpd_1; break;
						case 2: asm_work=&asm_copy_vmovntpd_2; break;
						case 3: asm_work=&asm_copy_vmovntpd_3; break;
						case 4: asm_work=&asm_copy_vmovntpd_4; break;
						case 8: asm_work=&asm_copy_vmovntpd_8; break;
						default: break;
					}
					break;
				case 2: // scale
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_scale_vmovntpd_1; break;
						case 2: asm_work=&asm_scale_vmovntpd_2; break;
						case 3: asm_work=&asm_scale_vmovntpd_3; break;
						case 4: asm_work=&asm_scale_vmovntpd_4; break;
						case 8: asm_work=&asm_scale_vmovntpd_8; break;
						default: break;
					}
					break;
				case 4: // indep
					switch (data->burst_length)
					{
						case 1: asm_work=&asm_indep_vmovntpd_1; break;
						case 2: asm_work=&asm_indep_vmovntpd_2; break;
						case 3: asm_work=&asm_indep_vmovntpd_3; break;
						case 4: asm_work=&asm_indep_vmovntpd_4; break;
						case 8: asm_work=&asm_indep_vmovntpd_8; break;
						default: break;
					}
					break;
				default: break;
			}
			break;
		default: break;
	}
  /* MEMORY LAYOUT
   * - aligned_addr points to the middle of the buffer
   * - an area in the middle of the buffer is used for the param_t structure, that contains all information that is
   *   needeed duringthe measurement ( PARAMS is defined as ((param_t*)aligned_addr) )
   * - the read buffer is mapped to the area before the parameter structure
   * - the write buffer starts behind the parameters structure
   * - parameter structure and write buffer are always contiguous memory 
   *   - a fixed read buffer (BENCHIT_KERNEL_LAYOUT="F") is not placed cache index aware with respect to the write buffer
   *     thus interference is likely (requires at least 2-way set associative cache)
   *   - contiguous memory can be enforced (BENCHIT_KERNEL_LAYOUT="C") to reduce interference, in this case the read buffer
   *     grows backwards starting from the parameter structure , thus read buffer, parameter structure, and write buffer
   *     are contiguous memory (with some gaps to avoid unwanted prefetching) that would even fit a direct mapped cache.
   *     However, this method is likely to cause bank conflicts 
   *   - BENCHIT_KERNEL_LAYOUT="A{1|2}" combine both approaches to find optimum */
  aligned_addr=(unsigned long long)(data->buffer) + data->buffersize/2 + data->offset; /* used as pointer to parameter structure (PARAMS) */

  max_threads=data->num_results;
  /* perform measurement for each selected core (BENCHIT_KERNEL_CPU_LIST) */
  /* thread_id: currently selected CPU
   * thread_id = 0: bandwidth of local access on first selected CPU
   *                - thread on first selected CPU accesses data
   *                - afterwards the same thread measures bandwidth for accesses to this data
   * thread_id > 0: bandwidth of remote accesses
   *                - thread on another CPU accesses data to bring it in its caches
   *                - afterwards thread on first selected CPU measures bandwidth for that data
   *                - (BENCHIT_KERNEL_READ_LOCAL/BENCHIT_KERNEL_WRITE_LOCAL) can be used to keep
   *                  one of the streams local in all cases*/
  for (PARAMS->thread_id=0;PARAMS->thread_id<max_threads;PARAMS->thread_id++)
  {
   /* set pointer to parameter structure of currently selected CPU */
   if (PARAMS->thread_id) THREAD_PARAMS=(param_t*) (data->threaddata[PARAMS->thread_id].aligned_addr + data->buffersize/2 + data->offset);
   else THREAD_PARAMS=NULL;
   /* set pointer to parameter structure of SHARE_CPU if required*/
   if ((data->USE_MODE_R&(MODE_SHARED|MODE_OWNED|MODE_FORWARD))||(data->USE_MODE_W&(MODE_SHARED|MODE_OWNED|MODE_FORWARD)))
     SHARE_CPU_PARAMS=(param_t*) (data->threaddata[data->FRST_SHARE_CPU].aligned_addr + data->buffersize/2 + data->offset);
   else SHARE_CPU_PARAMS=NULL;

   /* setup all information needed during measurement into the param_t structure */
   PARAMS->runs=data->runs;
   switch(data->burst_length) /* all but burst_length=3 perform 32 accesses per loop within the measurement routine, (burst_length_3 requires a multiple of 6) */
   {
     case 1: PARAMS->accesses_per_loop=64;break;
     case 2: PARAMS->accesses_per_loop=64;break;
     case 3: PARAMS->accesses_per_loop=66;break;
     case 4: PARAMS->accesses_per_loop=64;break;
     case 8: PARAMS->accesses_per_loop=64;break;
     default: PARAMS->accesses_per_loop=64;break;
   }
   switch (data->function)  /* setup data type size - determines the shift of the write buffer in each run */
   {
     case 1: /* vmovapd */
       PARAMS->alignment=32;
       break;
     case 3: /* vmovupd */
       PARAMS->alignment=32;
       break;
     case 4: /* mov */
       PARAMS->alignment=8;
       break;
     case 5: /* mov_clflush */
       PARAMS->alignment=8;
       break;
     case 6: /* movnti */
       PARAMS->alignment=8;
       break;
     case 8: /* vmovntpd */
       PARAMS->alignment=32;
       break;
     default: 
       PARAMS->alignment=16; /* 128 Bit operations*/
       break;
   }
   PARAMS->read_local=data->read_local;
   PARAMS->write_local=data->write_local;
   PARAMS->passes=memsize/(PARAMS->alignment*PARAMS->accesses_per_loop);
   PARAMS->memsize=PARAMS->passes*PARAMS->accesses_per_loop*PARAMS->alignment; 
   if (data->layout == LAYOUT_CONT) PARAMS->addr_1=aligned_addr-((PARAMS->passes*PARAMS->accesses_per_loop*PARAMS->alignment)/2); 
   else if (data->layout == LAYOUT_FIXED) PARAMS->addr_1=aligned_addr-data->buffersize/2; 
   PARAMS->addr_2=aligned_addr+((sizeof(param_t)+data->alignment)/data->alignment)*data->alignment;
   PARAMS->layout=data->layout;
   PARAMS->use_direction=data->USE_DIRECTION;
   PARAMS->num_uses=data->NUM_USES;
   PARAMS->default_use_mode_1=data->USE_MODE_R;
   PARAMS->default_use_mode_2=data->USE_MODE_W;
   #ifdef USE_PAPI
   PARAMS->Eventset=data->Eventset;
   PARAMS->num_events=data->num_events;
   PARAMS->values=data->values;
   #endif
   if (data->method==2) PARAMS->factor=data->factor;
   PARAMS->value=data->init_value;
   /* configure cache flushes */
   PARAMS->flush_mode=data->FLUSH_MODE;
   PARAMS->num_flushes=data->NUM_FLUSHES;
   PARAMS->flushaddr=(void*)(data->cache_flush_area);
   PARAMS->flushsize=0;
   if (!strcmp(data->cpuinfo->vendor,"AuthenticAMD")) /* exclusive caches */
   {
     for (PARAMS->i=data->cpuinfo->Cachelevels;PARAMS->i>0;PARAMS->i--)
     {   
       if (data->settings&FLUSH(PARAMS->i))
       {
         PARAMS->flushsize=0;
         /* flushsize = sum of all cache levels */
         for (PARAMS->j=PARAMS->i;PARAMS->j>0;PARAMS->j--) PARAMS->flushsize+=data->cpuinfo->U_Cache_Size[PARAMS->j-1]+data->cpuinfo->D_Cache_Size[PARAMS->j-1];
         if(memsize<=PARAMS->flushsize) PARAMS->flushsize = 0;
       }
     }
   }
   if (!strcmp(data->cpuinfo->vendor,"GenuineIntel")) /* inclusive caches */
   {
     for (PARAMS->i=data->cpuinfo->Cachelevels;PARAMS->i>0;PARAMS->i--)
     {   
       if (data->settings&FLUSH(PARAMS->i))
       {
         /* flushsize = size of selected level */
         PARAMS->flushsize==data->cpuinfo->U_Cache_Size[PARAMS->i-1]+data->cpuinfo->D_Cache_Size[PARAMS->i-1];;
         if(memsize<=PARAMS->flushsize) PARAMS->flushsize = 0;
       }
     }
   } 
   /* increase size to increase cache preasure */
   PARAMS->flushsize*=14;
   PARAMS->flushsize/=10;   

   /* setup parameter structure of selected CPU */
   if (PARAMS->thread_id) {
     memcpy(THREAD_PARAMS,PARAMS,sizeof(param_t));
     /* setup pointers to thread private streams */
     if (data->layout == LAYOUT_CONT) THREAD_PARAMS->addr_1=(data->threaddata[PARAMS->thread_id].aligned_addr+ data->buffersize/2 + data->offset)-((PARAMS->passes*PARAMS->accesses_per_loop*PARAMS->alignment)/2); 
     else if (data->layout == LAYOUT_FIXED) THREAD_PARAMS->addr_1=data->threaddata[PARAMS->thread_id].aligned_addr+data->offset;
     THREAD_PARAMS->addr_2=(data->threaddata[PARAMS->thread_id].aligned_addr+ data->buffersize/2 + data->offset)+((sizeof(param_t)+data->alignment)/data->alignment)*data->alignment;
     THREAD_PARAMS->flushaddr=(void*)(data->threaddata[PARAMS->thread_id].cache_flush_area);  
   }
   
   /* setup parameter structure of SHARE_CPU */
   if (SHARE_CPU_PARAMS!=NULL) {
     memcpy(SHARE_CPU_PARAMS,PARAMS,sizeof(param_t));
     SHARE_CPU_PARAMS->thread_id=data->FRST_SHARE_CPU;
     SHARE_CPU_PARAMS->flushaddr=(void*)(data->threaddata[SHARE_CPU_PARAMS->thread_id].cache_flush_area); 
     /* addr_1 and addr_2 are set to the selected streams within the loop */
   }   

   /* clflush everything that is not needed any more
    * - can help to reduce L1 anomalies on AMD K8/K10 if memsize is greater than half of the 2-way set associative L1
    * - however, clflushes create TLB entries for the unused area, thus might result in performance reduction by evicting usefull TLB entries
    * TODO add option to deactivate this
    */
   __asm__ __volatile__("mfence;"::: "memory");
   __asm__ __volatile__("clflush (%%rax);":: "a" ((unsigned long long)&memsize));
   for(PARAMS->i = sizeof(cpu_info_t)/64;PARAMS->i>=0;PARAMS->i--)
   {
      __asm__ __volatile__("clflush (%%rax);":: "a" (((unsigned long long)(data->cpuinfo))+64*PARAMS->i));
   }
   for(PARAMS->i = (sizeof(threaddata_t)*data->num_threads)/64;PARAMS->i>=0;PARAMS->i--)
   {
      __asm__ __volatile__("clflush (%%rax);":: "a" (((unsigned long long)(data->threaddata))+64*PARAMS->i));
   }
   for(PARAMS->i = sizeof(mydata_t)/64;PARAMS->i>=0;PARAMS->i--)
   {
      __asm__ __volatile__("clflush (%%rax);":: "a" (((unsigned long long)data)+64*PARAMS->i));
   }
   __asm__ __volatile__("clflush (%%rax);":: "a" ((unsigned long long)&data));
   __asm__ __volatile__("mfence;"::: "memory");
  
   /* perform measurement only if memsize is large enough for at least one iteration of the measurement loop */
   if (PARAMS->passes) 
   {
    PARAMS->tmax=0x7fffffffffffffff;
    /* perform the selected number of runs (BENCHIT_KERNEL_RUNS) */
    for (PARAMS->iter=0;PARAMS->iter<PARAMS->runs;PARAMS->iter++)
    {
      /* rotate memory layout each run */
      if (PARAMS->layout == LAYOUT_ALT1) 
      {
       if (PARAMS->iter%2 == 1){
         PARAMS->addr_1=aligned_addr-((PARAMS->passes*PARAMS->accesses_per_loop*PARAMS->alignment)/2);
         if (PARAMS->thread_id) THREAD_PARAMS->addr_1=(data->threaddata[PARAMS->thread_id].aligned_addr+ data->buffersize/2 + data->offset)-((PARAMS->passes*PARAMS->accesses_per_loop*PARAMS->alignment)/2);
       }
       else { 
         PARAMS->addr_1=aligned_addr-data->buffersize/2;
         if (PARAMS->thread_id) THREAD_PARAMS->addr_1=data->threaddata[PARAMS->thread_id].aligned_addr+data->offset;
       }
      }
      /* switch layout after half of the runns */
      if (PARAMS->layout == LAYOUT_ALT2) 
      {
       if (PARAMS->iter>=PARAMS->runs/2) {
         PARAMS->addr_1=aligned_addr-((PARAMS->passes*PARAMS->accesses_per_loop*PARAMS->alignment)/2);
         if (PARAMS->thread_id) THREAD_PARAMS->addr_1=(data->threaddata[PARAMS->thread_id].aligned_addr+ data->buffersize/2 + data->offset)-((PARAMS->passes*PARAMS->accesses_per_loop*PARAMS->alignment)/2);
       }
       else {
         PARAMS->addr_1=aligned_addr-data->buffersize/2;
         if (PARAMS->thread_id) THREAD_PARAMS->addr_1=data->threaddata[PARAMS->thread_id].aligned_addr+data->offset;
       }
      }
     
     /* slightly shift write buffer each run to reduce bank conflicts 
      * - deactivated for contiguous memory as this is supposed to show bank conflicts */   
     if (PARAMS->layout!=LAYOUT_CONT){
       PARAMS->addr_2+=PARAMS->alignment;
       if (PARAMS->thread_id) THREAD_PARAMS->addr_2+=PARAMS->alignment;
     }
    
     /* access remote memory to warm up TLB before other threads use the data 
      * cached data will be invalidated by other threads' accesses */
     if (PARAMS->thread_id>0)
     {
       if (!(PARAMS->read_local)) PARAMS->addr_1=THREAD_PARAMS->addr_1;
       if (!(PARAMS->write_local)) PARAMS->addr_2=THREAD_PARAMS->addr_2;
       /* use modified as this is the fastest option */
       PARAMS->use_mode_1=MODE_MODIFIED;
       PARAMS->use_mode_2=MODE_MODIFIED;
       /* local streams will be touched later on so they can be skiped here*/
       if ((PARAMS->read_local)) PARAMS->use_mode_1=MODE_DISABLED;
       if ((PARAMS->write_local)) PARAMS->use_mode_2=MODE_DISABLED;
       use_memory(PARAMS);
     }

     /* copy pointers to selected streams to SHARE_CPU parameters */
     if (SHARE_CPU_PARAMS!=NULL) {
       SHARE_CPU_PARAMS->addr_1=PARAMS->addr_1;
       SHARE_CPU_PARAMS->addr_2=PARAMS->addr_2;
     }        

    /* USE MODE ADAPTION (for BENCHIT_KERNEL_*_USE_MODE={S|F|O})
     * enforcing data to be in one of the shared coherency states (SHARED/OWNED/FORWARD), is implemented by adapting the target state for
     * individual accesses (a specific core (BENCHIT_KERNEL_SHARE_CPU) is used to share cachelines with the currently selected CPU (thread_id))
     * Forward: - Thread on SHARE_CPU accesses data with use mode EXCLUSIVE
     *          - Thread on selected CPU accesses data with use mode FORWARD (read only)
     *          Note: Forward seems to be a per-package state
     *                - Cores will have the line in shared state
     *                - L3 will have it in shared state (and 2 core valid bits set) if both cores share a package (die)
     *                - only if cores are in different packacges (dies), one L3 (last accessing core determines which one) will mark the line with state Forward
     *          Note: only usefull if coherency protocol is MESIF !!!
     * Shared:  - Thread on selected CPU accesses data with use mode EXCLUSIVE
     *          - Thread on SHARE_CPU accesses data with use mode SHARED (read only)
     *          Note: works on MESIF and non-MESIF protocols (copy on SHARE_CPU will be in Forward state for MESIF, thus SHRAE_CPU should be as far away from first CPU as posible)
     * Owned:   - Thread on selected CPU accesses data with use mode MODIFIED
     *          - Thread on SHARE_CPU accesses data with use mode SHARED (read only)
     *          Note: only works if coherency protocol is MOESI (otherwise both lines will be in shared state)
     */
      /* thread on SHARE_CPU acceses selected streams with target use mode forward */
      if (SHARE_CPU_PARAMS!=NULL){
        /* see USE MODE ADAPTION */
        if (SHARE_CPU_PARAMS->default_use_mode_1==MODE_FORWARD) SHARE_CPU_PARAMS->use_mode_1=MODE_EXCLUSIVE;
        else SHARE_CPU_PARAMS->use_mode_1=MODE_DISABLED;
        if (SHARE_CPU_PARAMS->default_use_mode_2==MODE_FORWARD) SHARE_CPU_PARAMS->use_mode_2=MODE_EXCLUSIVE;
        else SHARE_CPU_PARAMS->use_mode_2=MODE_DISABLED;
        //TODO remove accesses to mydata_t (data) to reduce cache footprint
      __asm__ __volatile__("mfence;"::: "memory");

        data->thread_comm[SHARE_CPU_PARAMS->thread_id]=THREAD_USE_MEMORY;
        while (!data->ack);
        data->ack=0;
        data->thread_comm[SHARE_CPU_PARAMS->thread_id]=THREAD_WAIT;    
        //wait for other thread using the memory
        while (!data->ack); //printf("wait for ack 1\n");
        data->ack=0;
        while (!data->done); //printf("wait for done 1\n");
        data->done=0;
      }
      
      /* access local streams if running locally (thread_id is 0) or if streams are selected to be
       * allways accessed locally (BENCHIT_KERNEL_READ_LOCAL/BENCHIT_KERNEL_WRITE_LOCAL) */
      if (PARAMS->thread_id==0){
        /* see USE MODE ADAPTION */
        if (PARAMS->default_use_mode_1==MODE_SHARED) PARAMS->use_mode_1=MODE_EXCLUSIVE;
        else if (PARAMS->default_use_mode_1==MODE_OWNED) PARAMS->use_mode_1=MODE_MODIFIED;
        else PARAMS->use_mode_1=PARAMS->default_use_mode_1;
        if (PARAMS->default_use_mode_2==MODE_SHARED) PARAMS->use_mode_2=MODE_EXCLUSIVE;
        else if (PARAMS->default_use_mode_2==MODE_OWNED) PARAMS->use_mode_2=MODE_MODIFIED;
        else PARAMS->use_mode_2=PARAMS->default_use_mode_2;                
        use_memory(PARAMS);
      }
      else if ((PARAMS->read_local)||(PARAMS->write_local)){        
        if (PARAMS->read_local){
          /* see USE MODE ADAPTION */
          if (PARAMS->default_use_mode_1==MODE_SHARED) PARAMS->use_mode_1=MODE_EXCLUSIVE;
          else if (PARAMS->default_use_mode_1==MODE_OWNED) PARAMS->use_mode_1=MODE_MODIFIED;
          else PARAMS->use_mode_1=PARAMS->default_use_mode_1;
        }
        else PARAMS->use_mode_1=MODE_DISABLED;
        if (PARAMS->read_local){
          /* see USE MODE ADAPTION */
          if (PARAMS->default_use_mode_2==MODE_SHARED) PARAMS->use_mode_2=MODE_EXCLUSIVE;
          else if (PARAMS->default_use_mode_2==MODE_OWNED) PARAMS->use_mode_2=MODE_MODIFIED;
          else PARAMS->use_mode_2=PARAMS->default_use_mode_2; 
        }
        else PARAMS->use_mode_2=MODE_DISABLED;
        use_memory(PARAMS);
      }

      /* thread on selected CPU accesses remote streams */
      if (PARAMS->thread_id>0){
        /* see USE MODE ADAPTION */
        if (THREAD_PARAMS->default_use_mode_1==MODE_SHARED) THREAD_PARAMS->use_mode_1=MODE_EXCLUSIVE;
        else if (THREAD_PARAMS->default_use_mode_1==MODE_OWNED) THREAD_PARAMS->use_mode_1=MODE_MODIFIED;
        else THREAD_PARAMS->use_mode_1=THREAD_PARAMS->default_use_mode_1;
        if (THREAD_PARAMS->default_use_mode_2==MODE_SHARED) THREAD_PARAMS->use_mode_2=MODE_EXCLUSIVE;
        else if (THREAD_PARAMS->default_use_mode_2==MODE_OWNED) THREAD_PARAMS->use_mode_2=MODE_MODIFIED;
        else THREAD_PARAMS->use_mode_2=THREAD_PARAMS->default_use_mode_2;
        /* disable unused remote streams to reduce cache prasure */
        if (PARAMS->read_local) THREAD_PARAMS->use_mode_1=MODE_DISABLED;
        if (PARAMS->write_local) THREAD_PARAMS->use_mode_2=MODE_DISABLED;
        //TODO remove accesses to mydata_t (data) to reduce cache footprint
      __asm__ __volatile__("mfence;"::: "memory");

        data->thread_comm[PARAMS->thread_id]=THREAD_USE_MEMORY;
        while (!data->ack);
        data->ack=0;
        data->thread_comm[PARAMS->thread_id]=THREAD_WAIT;    
        //wait for other thread using the memory
        while (!data->ack); //printf("wait for ack 2\n");
        data->ack=0;
        while (!data->done); //printf("wait for done 2\n");
        data->done=0;    
      }

      /* thread on SHARE_CPU acceses selected streams with target use mode owned or shared */
      if (SHARE_CPU_PARAMS!=NULL){
        /* see USE MODE ADAPTION */
        if (SHARE_CPU_PARAMS->default_use_mode_1&(MODE_SHARED|MODE_OWNED)) SHARE_CPU_PARAMS->use_mode_1=SHARE_CPU_PARAMS->default_use_mode_1;
        else SHARE_CPU_PARAMS->use_mode_1=MODE_DISABLED;
        if (SHARE_CPU_PARAMS->default_use_mode_2&(MODE_SHARED|MODE_OWNED)) SHARE_CPU_PARAMS->use_mode_2=SHARE_CPU_PARAMS->default_use_mode_2;
        else SHARE_CPU_PARAMS->use_mode_2=MODE_DISABLED;
        //TODO remove accesses to mydata_t (data) to reduce cache footprint
      __asm__ __volatile__("mfence;"::: "memory");

        data->thread_comm[SHARE_CPU_PARAMS->thread_id]=THREAD_USE_MEMORY;
        while (!data->ack);
        data->ack=0;
        data->thread_comm[SHARE_CPU_PARAMS->thread_id]=THREAD_WAIT;    
        //wait for other thread using the memory
        while (!data->ack); //printf("wait for ack 3\n");
        data->ack=0;
        while (!data->done); //printf("wait for done 3\n");
        data->done=0;
      }

      /* flush cachelevels as specified in PARAMETERS */
      if (PARAMS->flushsize) flush_caches(PARAMS);
           
      /* call ASM implementation */
      asm_work(PARAMS);
      
      if (PARAMS->rax<PARAMS->tmax) PARAMS->tmax=PARAMS->rax;
    }
    /* disabled, not needed as RUN_LINEAR is enforced in PARAMETERS file
     * // clear caches for next run with different (probably smaller) memsize
     * params->use_mode_1=MODE_INVALID;
     * params->use_mode_2=MODE_INVALID;
     * use_memory(params);
     */

   }
   else PARAMS->tmax=0;

   if (PARAMS->tmax>0){
     if ((data->settings)&LOOP_OVERHEAD_COMP)
       (*results)[PARAMS->thread_id+1]=(((double)(PARAMS->passes*PARAMS->accesses_per_loop*PARAMS->alignment))/(((double)(PARAMS->tmax-data->cpuinfo->rdtsc_latency)/data->cpuinfo->clockrate)))/1000000000;
     else 
       (*results)[PARAMS->thread_id+1]=(((double)(PARAMS->passes*PARAMS->accesses_per_loop*PARAMS->alignment))/(((double)(PARAMS->tmax-asm_loop_overhead(100))/data->cpuinfo->clockrate)))/1000000000;
   }
   else (*results)[PARAMS->thread_id+1]=INVALID_MEASUREMENT;
   
   #ifdef USE_PAPI
    for (PARAMS->i=0;PARAMS->i<data->num_events;PARAMS->i++)
    {
       data->papi_results[(PARAMS->i)*max_threads+(PARAMS->thread_id)]=(double)data->values[PARAMS->i]/(double)(PARAMS->passes*PARAMS->accesses_per_loop);
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
  param_t* params;

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
      *((double*)((unsigned long long)mydata->buffer+i))=(double)i;
   }

    clflush(mydata->buffer,mydata->buffersize,*(mydata->cpuinfo));
    mydata->aligned_addr=(unsigned long long)(mydata->buffer) + mydata->offset;
  }
  else mydata->aligned_addr=(unsigned long long)(global_data->buffer) + mydata->offset; 
  params=(param_t*)(mydata->aligned_addr + global_data->buffersize/2 + global_data->offset);

  cpu_set(((threaddata_t *) threaddata)->cpu_id);
  while(1)
  {
     switch (global_data->thread_comm[id]){
       case THREAD_USE_MEMORY: 
         if (old!=THREAD_USE_MEMORY)
         {
           old=THREAD_USE_MEMORY;
           global_data->ack=id;

           /* use memory */           
           use_memory(params);
           global_data->done=id;
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
           if (params->flushsize) flush_caches(params);
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


