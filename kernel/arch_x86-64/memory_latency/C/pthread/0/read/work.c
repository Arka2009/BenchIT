/******************************************************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id$
 * For license details see COPYING in the package base directory
 ******************************************************************************************************/
/* Kernel: measures read latency of data located in different cache levels or memory of certain CPUs.
 ******************************************************************************************************/
 
/*
 * TODO  - check malloc and mmap return values for errors and abort if alocation of buffers fails
 *       - adopt cache and TLB parameters to refer to identifiers returned by 
 *         the hardware detection
 *       - optional global or local alloc of flush buffer
 *       - add manual instrumentation for VampirTracce
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

/* report average latency instead of minimum */
//#define AVERAGE

/* add data dependencies in kernel versions with arithmetic operations between the loads */
//#define DEPENDENT

int iteration,accesses,alignment;

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

static void reset_tlb_check(volatile mydata_t* data){
  int i,j;
  
  if (data->tlb_sets) for (i=0;i<data->tlb_size/data->tlb_sets;i++){
    data->tlb_collision_check_array[i]=0;
    for (j=0;j<data->tlb_sets;j++) data->tlb_tags[j*(data->tlb_size/data->tlb_sets)+i]=(unsigned long long)0;
  }
}

//checks if page-addresses fit into the n-way associative TLB
static int tlb_check(unsigned long long addr,volatile mydata_t* data){
  int i,indizes,index_mask,index,tmp;

  if ((data->tlb_size==0)||(data->tlb_sets==0)) return 0;
 
  indizes = data->tlb_size/data->tlb_sets;
  index_mask=indizes-1;
  tmp=addr/data->pagesize;
  index=tmp&index_mask;
  /* check if addr is within a already selected page */
  for (i=0;i<data->tlb_collision_check_array[index];i++){
    if (tmp==data->tlb_tags[i*(data->tlb_size/data->tlb_sets)+index]) return 0;
  }
  /* check if another page fits into TLB */
  if (data->tlb_collision_check_array[index]<data->tlb_sets){
    data->tlb_tags[data->tlb_collision_check_array[index]*(data->tlb_size/data->tlb_sets)+index]=tmp;
    data->tlb_collision_check_array[index]++;
    return 0;
  }
  
  //printf("TLB_COLLISION\n");
  return -1;
  
}
static int already_selected(unsigned long long addr, unsigned long long *addresses, int max){
   int i;
   for (i=0;i<max;i++){
      if (addr==addresses[i]) return -1;
   }
   return 0;
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
static inline int use_memory(void* buffer,void* flush_buffer,unsigned long long memsize,int mode,int direction,int repeat,cpu_info_t cpuinfo,volatile mydata_t *data, threaddata_t *threaddata)
{
   int i,j,tmp=0xd08a721b;
   unsigned long long stride = 64;

   /* additional variables for generation of unique random pattern during use_memory() prior to each call of asm_work() function */
   unsigned long long tmp_addr,tmp_offset,mask,max_accesses;
   unsigned long long usable_memory,num_pages,accesses_per_page,usable_page_size;
   struct timeval time;
   unsigned long long aligned_addr;	   

   aligned_addr=(unsigned long long)buffer;

   /* MODE_EXCLUSIVE and MODE_MODIFIED generate a new random sequence in each call. This does not conflict with the 
      coherence state generation, as those three invalidate all other caches anyway
      MODE_SHARED, MODE_FORWARD, MODE_RDONLY, and MODE_OWNED are read-only operations that generate the wanted coherence states in different caches 
      in combination with MODE_EXCLUSIVE or MODE_MODIFIED accesses by other cores. They therefore must not modify the buffer as this would
      evict copies of other cores.
   */
   if ((mode==MODE_EXCLUSIVE)||(mode==MODE_MODIFIED)||(mode==MODE_INVALID)){
     /* clear the memory */
     memset(buffer,0,memsize);
     mask=(data->pagesize-1)^0xffffffffffffffffULL;
     usable_memory=(memsize&mask);
     usable_page_size=data->pagesize;

      if ((data->settings&RESTORE_TLB)&&(data->hugepages==HUGEPAGES_OFF))
      {
        usable_memory=usable_memory/2;
        usable_page_size=(data->pagesize)/2;
        if (usable_memory>data->tlb_size*(data->pagesize/2)) usable_memory=data->tlb_size*(data->pagesize/2);
        reset_tlb_check(data);
      }

      max_accesses=(usable_memory/alignment);
      if (max_accesses<accesses) accesses=max_accesses;
      num_pages=usable_memory/usable_page_size;
      accesses=(accesses/24)*24;
      if (accesses<=num_pages) {num_pages=accesses;usable_memory=num_pages*usable_page_size;/*alignment=usable_page_size;*/}

      gettimeofday( &time, (struct timezone *) 0);
      _random_init(time.tv_sec*time.tv_usec+pthread_self()*iteration*iteration,memsize/data->pagesize-1);
      /* randomly select pages (4KB) - repetition free sequence returned by _random() 
       * the first page is implicitely selected, as the asm_work() function is called with a pointer to the beginning of the buffer
       */
      data->page_address[0]=aligned_addr;tlb_check(aligned_addr,data); 
      for (j=1;j<num_pages;j++)
      {
        /* select pages that fit into selected TLB level (BENCHIT_KERNEL_TLB_MODE) */
        do{
          data->page_address[j]=(((unsigned long long)_random()+1)*data->pagesize);
        } while (tlb_check(aligned_addr+data->page_address[j],data));

        if (threaddata!=NULL) threaddata->page_address[j]=data->page_address[j];
        data->page_address[j]+=aligned_addr;
        if (threaddata!=NULL) threaddata->page_address[j]+=threaddata->aligned_addr;
      }  
  
      /* select random addresses within the choosen pages - repetition free sequence returned by _random() */
      gettimeofday( &time, (struct timezone *) 0);
      _random_init(time.tv_sec*time.tv_usec+pthread_self()*iteration*iteration,usable_memory/alignment-1);
      tmp_addr=aligned_addr; 
      for(j=0;j<accesses;j++)
      {
        tmp_offset=(((unsigned long long)_random())*alignment)+alignment;
        //*((unsigned long long*)(tmp_addr))=data->page_address[tmp_offset/usable_page_size]+(tmp_offset%usable_page_size);
        //changed to non-temporal store to prevent caching of the selected addresses
        __asm__ __volatile__(
             "movnti %%rbx, (%%rax);"
        :: "a" (tmp_addr), "b" (data->page_address[tmp_offset/usable_page_size]+(tmp_offset%usable_page_size)));
        tmp_addr=data->page_address[tmp_offset/usable_page_size]+(tmp_offset%usable_page_size);
      }
   }
   if ((data->extra_clflush)&&((mode==MODE_EXCLUSIVE)||(mode==MODE_MODIFIED)||(mode==MODE_INVALID))) {
      /* remove data from cache before data placement to avoid reuse of data between runs */
      clflush(buffer,memsize,cpuinfo);
   }

   for (i=cpuinfo.Cachelevels;i>0;i--)
   {
     if (cpuinfo.Cacheline_size[i-1]<stride) stride=cpuinfo.Cacheline_size[i-1];
   }

   if ((mode==MODE_MODIFIED)||(mode==MODE_EXCLUSIVE)||(mode==MODE_INVALID))
   {
     //invalidate remote caches
     //this kernel needs the content of the buffer, so the usage must not be destructive
     __asm__ __volatile__(
       		"_use_mem_inv_loop:"
       		"mov (%%rax), %%rbx;"
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
         //this kernel needs the content of the buffer, so the usage must not be destructive
         __asm__ __volatile__(
       		"_use_mem_write_loop_fifo:"
       		"mov (%%rax), %%rbx;"
       		"mov %%rbx, (%%rax);"
       		"add %%rcx, %%rax;"
       		"sub $1, %%rdx;"
       		"jnz _use_mem_write_loop_fifo;"
       		:: "a" ((unsigned long long)buffer), "b" (tmp), "c" (stride), "d" (memsize/stride) : "memory");
       }
       if (direction==LIFO){
         //this kernel needs the content of the buffer, so the usage must not be destructive
         __asm__ __volatile__(
       		"_use_mem_write_loop_lifo:"
       		"sub %%rcx, %%rax;"
       		"mov (%%rax), %%rbx;"
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
 */
static inline void flush_caches(void* buffer,unsigned long long memsize,int settings,int num_flushes,int flush_mode,void* flush_buffer,cpu_info_t *cpuinfo)
{
   int i,j;
   unsigned long long total_cache_size;
   if ((!strcmp(cpuinfo->vendor,"AuthenticAMD")) && (cpuinfo->family != 21)) //exclusive caches
   for (i=cpuinfo->Cachelevels;i>0;i--)
   {   
     if (settings&FLUSH(i))
     {
       // determine total exclusive cache size of level that should be flushed
       total_cache_size=0;
       for (j=i;j>0;j--) total_cache_size+=cpuinfo->U_Cache_Size[j-1]+cpuinfo->D_Cache_Size[j-1];
       // subtract higher levels that are flushed too as these flushes polute the cache and reduce the effectively usable size
       for (j=i-1;j>0;j--) if (settings&FLUSH(j)) total_cache_size-=cpuinfo->U_Cache_Size[j-1]+cpuinfo->D_Cache_Size[j-1];
       if(memsize>total_cache_size)
       {
         cacheflush(i,num_flushes,flush_mode,flush_buffer,*(cpuinfo));
         break;
       }
     }
   }
   else if ((!strcmp(cpuinfo->vendor,"AuthenticAMD")) && (cpuinfo->family == 21))//inclusive L2 cache, exclusive L3
   {
    for (i=cpuinfo->Cachelevels;i>2;i--)
    {   
     if (settings&FLUSH(i))
     {
       // determine total exclusive cache size of level that should be flushed
       total_cache_size=0;
       for (j=i;j>1;j--) total_cache_size+=cpuinfo->U_Cache_Size[j-1]+cpuinfo->D_Cache_Size[j-1];
       // subtract higher levels that are flushed too as these flushes polute the cache and reduce the effectively usable size
       if ((i==3) && (settings&FLUSH(2))) total_cache_size-=cpuinfo->U_Cache_Size[1]+cpuinfo->D_Cache_Size[1];
       else if ((i==3) && (settings&FLUSH(1))) total_cache_size-=cpuinfo->U_Cache_Size[0]+cpuinfo->D_Cache_Size[0];
       if(memsize>total_cache_size)
       {
         cacheflush(i,num_flushes,flush_mode,flush_buffer,*(cpuinfo));
         break;
       }
     }
    }
    for (i=2;i>0;i--)
    {   
     if ((settings&FLUSH(i))&&(memsize>(cpuinfo->U_Cache_Size[i-1]+cpuinfo->D_Cache_Size[i-1])))
     {
       cacheflush(i,num_flushes,flush_mode,flush_buffer,*(cpuinfo));
       break;
     }
    }
   }
   else // inclusive caches
   for (i=cpuinfo->Cachelevels;i>0;i--)
   {   
     if ((settings&FLUSH(i))&&(memsize>(cpuinfo->U_Cache_Size[i-1]+cpuinfo->D_Cache_Size[i-1])))
     {
       cacheflush(i,num_flushes,flush_mode,flush_buffer,*(cpuinfo));
       break;
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

/** assembler implementation of latency measurement using mov instruction
 */
static int asm_work_mov(unsigned long long addr, unsigned long long passes,volatile mydata_t *data) __attribute__((noinline));
static int asm_work_mov(unsigned long long addr, unsigned long long passes,volatile mydata_t *data)
{
   unsigned long long a,b;
   int i;

   if (!passes) return 0;

   #ifdef USE_PAPI
    if (data->num_events) PAPI_reset(data->Eventset);
   #endif


     /*
      * Input:  RBX: addr (pointer to the buffer)
      *         RCX: passes (number of loop iterations)
      * Output: RAX: stop timestamp
      *         RBX: start timestamp
      */
     __asm__ __volatile__(
                TIMESTAMP
                SERIALIZE
/* standard version */
                "jmp _work_loop_mov_1;"
                ".align 64,0x0;"
                //loop that performs random memory accesses (memory contains precalculated random target addresses)
                "_work_loop_mov_1:"
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                "sub $1,%%rcx;"
                "jnz _work_loop_mov_1;"
/* */
/* alternate version with division operations on pointer
                #ifdef DEPENDENT
                "mov %%rbx,%%r10;"
                "mov %%rax,%%rbx;"
                "mov %%r10,%%rax;"  // move address to rax (implicit operand of div)
                #endif
                "mov $1, %%r9;"
                "mov $0, %%rdx;"
                "jmp _work_loop_mov_1;"
                ".align 64,0x0;"
                //loop that performs random memory accesses (memory contains precalculated random target addresses) 
                "_work_loop_mov_1:"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                #ifdef DEPENDENT
                "mov (%%rax), %%rax;"NOP(NOPCOUNT)
                #else
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #endif                
                "div %%r9;div %%r9;div %%r9;div %%r9;"
                "sub $1,%%rcx;"
                "jnz _work_loop_mov_1;"
                #ifdef DEPENDENT
                "mov %%rbx,%%rax;"  // restore first timestamp
                #endif
/* */
/* alternate version with addition operations on pointer
                "jmp _work_loop_mov_1;"
                ".align 64,0x0;"
                //loop that performs random memory accesses (memory contains precalculated random target addresses)
                "_work_loop_mov_1:"
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                "add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;add $0, %%rbx;"
                #else
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                "add $0, %%r8;add $0, %%r9;add $0, %%r10;add $0, %%r11;add $0, %%r12;add $0, %%r13;add $0, %%r14;add $0, %%r15;"
                #endif
                "sub $1,%%rcx;"
                "jnz _work_loop_mov_1;"
/* */
/* alternate version with multiplication operations on pointer 
                "jmp _work_loop_mov_1;"
                ".align 64,0x0;"
                //loop that performs random memory accesses (memory contains precalculated random target addresses)
                "_work_loop_mov_1:"
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "mov (%%rbx), %%rbx;"NOP(NOPCOUNT)
                #ifdef DEPENDENT
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                "imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;imul $1, %%rbx;"
                #else
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                "imul $1, %%r8;imul $1, %%r9;imul $1, %%r10;imul $1, %%r11;imul $1, %%r12;imul $1, %%r13;imul $1, %%r14;imul $1, %%r15;"
                #endif
                "sub $1,%%rcx;"
                "jnz _work_loop_mov_1;"
/* */

                SERIALIZE
                "mov %%rax,%%rbx;"
                TIMESTAMP
                : "=a" (a),"=b" (b)
                : "b"(addr), "c" (passes)
                : "%rdx", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15"

     );
  #ifdef USE_PAPI
    if (data->num_events) PAPI_read(data->Eventset,data->values);
  #endif
    return (unsigned int) ((a-b)-data->cpuinfo->rdtsc_latency)/(passes*24);
}

/** function that performs the measurement
 *   - entry point for BenchIT framework (called by bi_entry())
 */
void _work(unsigned long long memsize, int def_alignment, int offset, int function, int num_accesses, int runs, volatile mydata_t* data, double **results)
{
  int i,j,k,t,tmin,max_threads;
  unsigned long long tmp,tmp2,tmp3,mask;
  
  unsigned long long usable_memory,num_pages,accesses_per_page,usable_page_size;
	
  unsigned long long tmp_addr,tmp_offset,max_accesses;	

  /* aligned address */
  unsigned long long aligned_addr;


  struct timeval time;
  
  gettimeofday( &time, (struct timezone *) 0);

 
  /* use rdtsc latency parameter for loop overhead compensation */
  if ((data->settings)&LOOP_OVERHEAD_COMP) data->cpuinfo->rdtsc_latency=data->loop_overhead;
  
  /* calculate aligned address*/
  aligned_addr = (unsigned long long)(data->buffer)+offset;
  
  accesses=num_accesses;
  alignment=def_alignment;

  mask=(data->pagesize-1)^0xffffffffffffffffULL;
  usable_memory=(memsize&mask);
  usable_page_size=data->pagesize;

  if ((data->settings&RESTORE_TLB)&&(data->hugepages==HUGEPAGES_OFF))
  {
    usable_memory=usable_memory/2;
    usable_page_size=(data->pagesize)/2;
    if (usable_memory>data->tlb_size*(data->pagesize/2)) usable_memory=data->tlb_size*(data->pagesize/2);
    reset_tlb_check(data);
  }

  max_accesses=(usable_memory/alignment);
  if (max_accesses<accesses) accesses=max_accesses;
  num_pages=usable_memory/usable_page_size;
  accesses=(accesses/24)*24;

  data->page_address=(unsigned long long*)realloc(data->page_address,num_pages*sizeof(unsigned long long));
  for (t=1;t<data->num_threads;t++) data->threaddata[t].page_address=(unsigned long long*)realloc(data->threaddata[t].page_address,num_pages*sizeof(unsigned long long));

  if (accesses<=num_pages) {num_pages=accesses;usable_memory=num_pages*usable_page_size;/*alignment=usable_page_size;*/}


  if ((accesses<=48) && (memsize<data->cpuinfo->Total_D_Cache_Size)) runs*=2;
  if ((accesses<=120) && (memsize<data->cpuinfo->Total_D_Cache_Size)) runs*=2;
  if (memsize>data->cpuinfo->Total_D_Cache_Size) runs/=3;
  if (runs==0) runs=1;

  max_threads=data->num_results;
  for (t=0;t<max_threads;t++)
  {
   #ifdef AVERAGE
    tmin=0;
    #ifdef USE_PAPI
    for (j=0;j<data->num_events;j++)
    {
      data->papi_results[j*max_threads+t]=0;
    }
    #endif
   #else
    tmin=INT_MAX;
    #ifdef USE_PAPI
    for (j=0;j<data->num_events;j++)
    {
      data->papi_results[j*max_threads+t]=LONG_MAX;
    }
    #endif
   #endif
   
   if (accesses>=24) 
   {

    for (i=0;i<runs;i++)
    {
      iteration=i;
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
      //remove page tables from core0's caches as would be the case for a local measurement
      //ensures consistent results, if disabled accesses to memory used by other cores memory can be faster than accesses to memory used by core0 itself
      //as core0 is idle in case of accssesing other cores memory and will retain page tables in it's cache that are lost if core0 is active (if t==0)
      if ((t) && (data->FLUSH_PT) && (data->hugepages == HUGEPAGES_OFF)) use_memory((void*)(aligned_addr),data->cache_flush_area,memsize,MODE_EXCLUSIVE,FIFO,data->NUM_USES,*(data->cpuinfo),data,NULL);

   if (!strcmp("GenuineIntel",data->cpuinfo->vendor))
   {
      /* 
       * create copies in CPUs from SHARED_CPU_LIST first, forward copy in target CPU will be created in next step
       * one CPU in SHARED_CPU_LIST -> Exclusive copy in FRST_SHARE_CPU
       * multiple CPUs in SHARED_CPU_LIST -> one or multiple shared copies, forward copy in last CPU in SHARED_CPU_LIST
       */
      if ((data->USE_MODE==MODE_FORWARD)){
        //tell other threads to use memory
        unsigned long long tmp;
        int i;

        for (i=data->FRST_SHARE_CPU;i<data->FRST_SHARE_CPU+data->NUM_SHARED_CPUS;i++){
          tmp=data->threaddata[i].aligned_addr;
          if (t) data->threaddata[i].aligned_addr=data->threaddata[t].aligned_addr;
          else data->threaddata[i].aligned_addr=aligned_addr;
          data->threaddata[i].memsize=memsize;
          data->threaddata[i].accesses=accesses;
          if (i==data->FRST_SHARE_CPU) data->threaddata[i].USE_MODE=MODE_EXCLUSIVE;
          else data->threaddata[i].USE_MODE=data->USE_MODE;
      __asm__ __volatile__("mfence;"::: "memory");

          data->thread_comm[i]=THREAD_USE_MEMORY;
          while (!data->ack);
          data->ack=0;
          data->thread_comm[i]=THREAD_WAIT;    
          //wait for other thread using the memory
          while (!data->ack); //printf("wait for ack 1\n");
          data->ack=0;
          while (!data->done); //printf("wait for done 1\n");
          data->done=0;
          data->threaddata[i].aligned_addr=tmp;
        }
      }

      /* 
       * modified/exclusive: create copy with the requested state in target CPU (CPUs in SHARED_CPU_LIST not involved)
       * shared: create exclussive copy in target CPU first, will be transformed to shared by later accesses of CPUs in SHARED_CPU_LIST
       * forward: one exclusive or multiple shared copies already exist in CPUs from SHARED_CPU_LIST, additional read inserts forward copy in target CPU
       */    
      if (!t){ // measure local cache hierarchy      
        //access whole buffer to warm up cache
        if ((data->USE_MODE==MODE_SHARED)) use_memory((void*)aligned_addr,data->cache_flush_area,memsize,MODE_EXCLUSIVE,FIFO,data->NUM_USES,*(data->cpuinfo),data,NULL);
        else use_memory((void*)aligned_addr,data->cache_flush_area,memsize,data->USE_MODE,FIFO,data->NUM_USES,*(data->cpuinfo),data,NULL);
      }
      else{ // measure accesses to other cores' caches
        //tell other thread to use memory
        data->threaddata[t].memsize=memsize;
        data->threaddata[t].accesses=accesses;
        if ((data->USE_MODE==MODE_SHARED)) data->threaddata[t].USE_MODE=MODE_EXCLUSIVE;
        else data->threaddata[t].USE_MODE=data->USE_MODE;
      __asm__ __volatile__("mfence;"::: "memory");

        data->thread_comm[t]=THREAD_USE_MEMORY;
        while (!data->ack);
        data->ack=0;
        data->thread_comm[t]=THREAD_WAIT;    
        //wait for other thread using the memory
        while (!data->ack); //printf("wait for ack 2\n");
        data->ack=0;
        while (!data->done);//printf("wait for done 2\n");
        data->done=0;             
      }
 
      /* turn Exclusive copy in target CPU into Shared copy
       * one CPU in SHARED_CPU_LIST will have forward copy
       */       
      if (data->USE_MODE==MODE_SHARED){
        //tell other threads to use memory
        unsigned long long tmp;
        int i;

        for (i=data->FRST_SHARE_CPU;i<data->FRST_SHARE_CPU+data->NUM_SHARED_CPUS;i++){
          tmp=data->threaddata[i].aligned_addr;
          if (t) data->threaddata[i].aligned_addr=data->threaddata[t].aligned_addr;
          else data->threaddata[i].aligned_addr=aligned_addr;
          data->threaddata[i].memsize=memsize;
          data->threaddata[i].accesses=accesses;
          data->threaddata[i].USE_MODE=data->USE_MODE;
      __asm__ __volatile__("mfence;"::: "memory");

          data->thread_comm[i]=THREAD_USE_MEMORY;
          while (!data->ack);
          data->ack=0;
          data->thread_comm[i]=THREAD_WAIT;    
          //wait for other thread using the memory
          while (!data->ack); //printf("wait for ack 3\n");
          data->ack=0;
          while (!data->done); //printf("wait for done 3\n");
          data->done=0;
          data->threaddata[i].aligned_addr=tmp;
        }
      }
   }
   if (!strcmp("AuthenticAMD",data->cpuinfo->vendor))
   {

      /*
       * create modified copy in one shared CPU first, MuW in target CPU will be created in next step
       */
      if (data->USE_MODE==MODE_MUW){
        //tell another thread to use memory
        unsigned long long tmp;
        tmp=data->threaddata[data->FRST_SHARE_CPU].aligned_addr;
        if (t) data->threaddata[data->FRST_SHARE_CPU].aligned_addr=data->threaddata[t].aligned_addr;
        else data->threaddata[data->FRST_SHARE_CPU].aligned_addr=aligned_addr;
        data->threaddata[data->FRST_SHARE_CPU].memsize=memsize;
        data->threaddata[data->FRST_SHARE_CPU].accesses=accesses;
        data->threaddata[data->FRST_SHARE_CPU].USE_MODE=MODE_MODIFIED; // -> M in SHARE_CPU, next read results in MUW in the requestor
      __asm__ __volatile__("mfence;"::: "memory");

        data->thread_comm[data->FRST_SHARE_CPU]=THREAD_USE_MEMORY;
        while (!data->ack);
        data->ack=0;
        data->thread_comm[data->FRST_SHARE_CPU]=THREAD_WAIT;    
        //wait for other thread using the memory
        while (!data->ack); //printf("wait for ack 1\n");
        data->ack=0;
        while (!data->done); //printf("wait for done 1\n");
        data->done=0;
        data->threaddata[data->FRST_SHARE_CPU].aligned_addr=tmp;
      }

      /* 
       * modified/exclusive: create copy with the requested state in target CPU (CPUs in SHARED_CPU_LIST not involved)
       * MuW: read modified data from SHARED_CPU to insert MuW copy in target CPU
       * shared: non-MuW MOESI: create shared copy in target CPU, exclusive copy in FRST_SHARE_CPU turns into shared as well
       *         MuW: create MuW copy in target CPU, exclusive copy in FRST_SHARE_CPU is invalidated 
       * owned: create modified copy in target CPU first, will be turned into Owned state by following accesses
       */
      if (!t){ // measure local cache hierarchy       
        //access whole buffer to warm up cache
        if ((data->USE_MODE==MODE_MUW)) use_memory((void*)aligned_addr,data->cache_flush_area,memsize,MODE_SHARED,FIFO,data->NUM_USES,*(data->cpuinfo),data,NULL); // -> MUW, invalid in SHARE_CPU
        else if ((data->USE_MODE==MODE_OWNED)) use_memory((void*)aligned_addr,data->cache_flush_area,memsize,MODE_MODIFIED,FIFO,data->NUM_USES,*(data->cpuinfo),data,NULL); // -> M, invalid in SHARE_CPU, following read by SHARE_CPU will turn it into Owned, shared in SHARE_CPU or invalid, MUW in SHARE_CPU
        else if ((data->USE_MODE==MODE_SHARED)) use_memory((void*)aligned_addr,data->cache_flush_area,memsize,MODE_EXCLUSIVE,FIFO,data->NUM_USES,*(data->cpuinfo),data,NULL); // -> E, invalid in SHARE_CPU, following read by SHARE_CPU will turn it into Shared
        else use_memory((void*)aligned_addr,data->cache_flush_area,memsize,data->USE_MODE,FIFO,data->NUM_USES,*(data->cpuinfo),data,NULL);
        //early flushes disabled, now flushing all threads after creating desired coherence state
        //flush_caches((void*) data->threaddata[t].aligned_addr,memsize,data->settings,data->NUM_FLUSHES,data->FLUSH_MODE,data->cache_flush_area,data->cpuinfo);
      }
      else{ // measure accesses to other cores' caches
        //tell other thread to use memory
        data->threaddata[t].memsize=memsize;
        data->threaddata[t].accesses=accesses;
        if ((data->USE_MODE==MODE_MUW)) data->threaddata[t].USE_MODE=MODE_SHARED; // -> MUW in target CPU, M -> invalid in SHARE_CPU
        else if ((data->USE_MODE==MODE_OWNED)) data->threaddata[t].USE_MODE=MODE_MODIFIED; // -> M in target CPU, invalid in SHARE_CPU, following read by SHARE_CPU will turn it into Owned, shared in SHARE_CPU (non-MUW MOESI) or invalid, MUW in SHARE_CPU (MuW protocol)
        else if ((data->USE_MODE==MODE_SHARED)) data->threaddata[t].USE_MODE=MODE_EXCLUSIVE; // -> E in target CPU, invalid in SHARE_CPU, following read by SHARE_CPU will turn it into Shared
        else data->threaddata[t].USE_MODE=data->USE_MODE;
      __asm__ __volatile__("mfence;"::: "memory");

        data->thread_comm[t]=THREAD_USE_MEMORY;
        while (!data->ack);
        data->ack=0;
        data->thread_comm[t]=THREAD_WAIT;    
        //wait for other thread using the memory
        while (!data->ack); //printf("wait for ack 3\n");
        data->ack=0;
        while (!data->done);//printf("wait for done 3\n");
        data->done=0;             
      }

      /*
       * non-MuW: shared in target and all shared CPUs
       * MuW: shared in target CPU, one owned copy in last shared CPU, other shared CPUs in state shared 
       */        
      if (data->USE_MODE==MODE_SHARED){
        //tell other threads to use memory
        unsigned long long tmp;
        int i;

        for (i=data->FRST_SHARE_CPU;i<data->FRST_SHARE_CPU+data->NUM_SHARED_CPUS;i++){
          tmp=data->threaddata[i].aligned_addr;
          if (t) data->threaddata[i].aligned_addr=data->threaddata[t].aligned_addr;
          else data->threaddata[i].aligned_addr=aligned_addr;
          data->threaddata[i].memsize=memsize;
          data->threaddata[i].accesses=accesses;
          data->threaddata[i].USE_MODE=data->USE_MODE;
      __asm__ __volatile__("mfence;"::: "memory");

          data->thread_comm[i]=THREAD_USE_MEMORY;
          while (!data->ack);
          data->ack=0;
          data->thread_comm[i]=THREAD_WAIT;    
          //wait for other thread using the memory
          while (!data->ack); //printf("wait for ack 4\n");
          data->ack=0;
          while (!data->done); //printf("wait for done 4\n");
          data->done=0;
          data->threaddata[i].aligned_addr=tmp;
        }
      }

      /*
       * non-MuW: M-> owned in target CPU, shared in SHARED_CPU
       * MuW: invalid in target CPU, MuW in FRST_SHARE_CPU
       */
      if (data->USE_MODE==MODE_OWNED){
        //tell another thread to use memory
        unsigned long long tmp;
        tmp=data->threaddata[data->FRST_SHARE_CPU].aligned_addr;
        if (t) data->threaddata[data->FRST_SHARE_CPU].aligned_addr=data->threaddata[t].aligned_addr;
        else data->threaddata[data->FRST_SHARE_CPU].aligned_addr=aligned_addr;
        data->threaddata[data->FRST_SHARE_CPU].memsize=memsize;
        data->threaddata[data->FRST_SHARE_CPU].accesses=accesses;
        data->threaddata[data->FRST_SHARE_CPU].USE_MODE=data->USE_MODE;
      __asm__ __volatile__("mfence;"::: "memory");

        data->thread_comm[data->FRST_SHARE_CPU]=THREAD_USE_MEMORY;
        while (!data->ack);
        data->ack=0;
        data->thread_comm[data->FRST_SHARE_CPU]=THREAD_WAIT;    
        //wait for other thread using the memory
        while (!data->ack); //printf("wait for ack 5\n");
        data->ack=0;
        while (!data->done); //printf("wait for done 5\n");
        data->done=0;
        data->threaddata[data->FRST_SHARE_CPU].aligned_addr=tmp;
      }

      /* MOESI with MuW support
       * Owned: read again to convert MUW in SHARE_CPU into Owned in target CPU, shared in SHARE_CPU (I->O, Muw->S in SHARE_CPU)
       *        no change in non-MuW version (owned copy already present)
       */
      if (data->USE_MODE==MODE_OWNED){
       if (!t){
          use_memory((void*)aligned_addr,data->cache_flush_area,memsize,data->USE_MODE,FIFO,data->NUM_USES,*(data->cpuinfo),data,NULL);
        }
       if (t){
         //tell other thread to use memory
         data->threaddata[t].memsize=memsize;
         data->threaddata[t].accesses=accesses;
         data->threaddata[t].USE_MODE=data->USE_MODE;
      __asm__ __volatile__("mfence;"::: "memory");

         data->thread_comm[t]=THREAD_USE_MEMORY;
         while (!data->ack);
         data->ack=0;
         data->thread_comm[t]=THREAD_WAIT;    
         //wait for other thread using the memory
         while (!data->ack); //printf("wait for ack 6\n");
         data->ack=0;
         while (!data->done);//printf("wait for done 6\n");
         data->done=0;
       }
      }

   }

      //flush cachelevels as specified in PARAMETERS
      //tell threads on shared CPUs to flush caches  
      for (j=data->FRST_SHARE_CPU;j<data->FRST_SHARE_CPU+data->NUM_SHARED_CPUS;j++){
         if (data->flush_share_cpu) data->thread_comm[j]=THREAD_FLUSH_ALL;
         else data->thread_comm[j]=THREAD_FLUSH;
         while (!data->ack);
         data->ack=0;
         data->thread_comm[j]=THREAD_WAIT;    
         //wait for other thread flushing their caches
         while (!data->ack); //printf("wait for ack 6\n");
         data->ack=0;       
      }     
      if (t){
         //tell thread on target CPU to flush caches
         data->thread_comm[t]=THREAD_FLUSH;
         while (!data->ack);
         data->ack=0;
         data->thread_comm[t]=THREAD_WAIT;    
         //wait for other thread flushing their caches
         while (!data->ack); //printf("wait for ack 6\n");
         data->ack=0;
         if (data->settings&OPT_FLUSH_CPU0) flush_caches((void*) data->threaddata[t].aligned_addr,memsize,data->settings,data->NUM_FLUSHES,data->FLUSH_MODE,data->cache_flush_area,data->cpuinfo);
      }
      else flush_caches((void*) data->threaddata[t].aligned_addr,memsize,data->settings,data->NUM_FLUSHES,data->FLUSH_MODE,data->cache_flush_area,data->cpuinfo);

      //restore TLB if enabled (that was destroied by flushing the cache)
      if ((data->settings&RESTORE_TLB)&&(data->hugepages==HUGEPAGES_OFF))
      {
       //printf("restore TLB\n");fflush(stdout);
        tmp2=data->pagesize/2+data->pagesize/8;
        for (j=0;j<num_pages;j++)
        {
          for (k=tmp2;k<tmp2+data->pagesize/4;k+=alignment)
          {
            if (!t)
            {
              tmp=*((unsigned long long*)(data->page_address[j]+k));
              *((unsigned long long*)(data->page_address[j]+k))=tmp;
              clflush((void*)data->page_address,num_pages*sizeof(unsigned long long),*(data->cpuinfo));  
            }
           else
            {
              tmp=*((unsigned long long*)(data->threaddata[t].page_address[j]+k));
              *((unsigned long long*)(data->threaddata[t].page_address[j]+k))=tmp;
              clflush((void*)data->threaddata[t].page_address,num_pages*sizeof(unsigned long long),*(data->cpuinfo));  
            }
          }
        }
      }

      /* call ASM implementation */
     switch(function){
       case 0:          
               //prefetch measurement routine
               if (data->ENABLE_CODE_PREFETCH){
                  *((unsigned long long*)(data->cache_flush_area))=(unsigned long long)(data->cache_flush_area); //pointer to itself
                  for (j=0;j<data->NUM_USES;j++) {tmp+=asm_work_mov((unsigned long long)(data->cache_flush_area),1,data);}
               }
               //measurement
               if (!t) tmp=asm_work_mov(aligned_addr,accesses/24,data);
               else tmp=asm_work_mov(data->threaddata[t].aligned_addr,accesses/24,data);
               break;
       default: break;
     }

      // discard first iteration if more than 1 runs are performed
      if (((i>0)||(runs==1))&&(tmp!=-1))
      {
       #ifdef AVERAGE
         tmin+=tmp;
         #ifdef USE_PAPI
         for (j=0;j<data->num_events;j++)
         {
           data->papi_results[j*max_threads+t]+=((double)data->values[j]/(double)accesses);
         }
         #endif
       #else
         if (tmp<tmin) tmin=tmp;
         #ifdef USE_PAPI
         for (j=0;j<data->num_events;j++)
         {
           if ((double)data->values[j]/(double)accesses < data->papi_results[j*max_threads+t])
             data->papi_results[j*max_threads+t]=(double)data->values[j]/(double)accesses;
         }
         #endif
       #endif        
      }
    }
    #ifdef AVERAGE
    if (runs>1){
      tmin/=(runs-1);
       #ifdef USE_PAPI
       for (j=0;j<data->num_events;j++)
       {
         data->papi_results[j*max_threads+t]/=(runs-1);
       }
       #endif       
    }
    #endif
   }
   else tmin=0;
  
   if (tmin) (*results)[t]=(double)tmin;
   else (*results)[t]=INVALID_MEASUREMENT;
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
    mydata->aligned_addr=(unsigned long long)(mydata->buffer) + mydata->offset;
  }
  else mydata->aligned_addr=(unsigned long long)(global_data->buffer) + mydata->offset; 

  cpu_set(((threaddata_t *) threaddata)->cpu_id);
  while(1)
  {
     switch (global_data->thread_comm[id]){
       case THREAD_USE_MEMORY: 
         if (old!=THREAD_USE_MEMORY)
         {
           old=THREAD_USE_MEMORY;
           global_data->ack=id;

           // use memory
           use_memory((void*)mydata->aligned_addr,mydata->cache_flush_area,mydata->memsize,mydata->USE_MODE,FIFO,mydata->NUM_USES,*(mydata->cpuinfo),global_data,mydata);
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
           flush_caches((void*) (mydata->aligned_addr),mydata->memsize,mydata->settings,mydata->NUM_FLUSHES,mydata->FLUSH_MODE,mydata->cache_flush_area,mydata->cpuinfo);
         }
         else 
         {
           tmp=100;while(tmp>0) tmp--; 
         }        
         break;
       case THREAD_FLUSH_ALL: 
         if (old!=THREAD_FLUSH_ALL)
         {
           old=THREAD_FLUSH_ALL;
           global_data->ack=id;

           //flush all caches
           flush_caches((void*) (mydata->aligned_addr),mydata->cpuinfo->Total_D_Cache_Size*2,mydata->settings,mydata->NUM_FLUSHES,mydata->FLUSH_MODE,mydata->cache_flush_area,mydata->cpuinfo);
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


