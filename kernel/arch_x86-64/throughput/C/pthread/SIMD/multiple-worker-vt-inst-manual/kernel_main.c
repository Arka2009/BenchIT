/******************************************************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id$
 * For license details see COPYING in the package base directory
 *****************************************************************************************************/
/* Kernel: measures throughput of memory bound SIMD instructions for cache levels and main memory.
 *****************************************************************************************************/
#define _GNU_SOURCE
#include <sched.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/time.h>
#include <signal.h>
#include <unistd.h>
#include "interface.h"
#include "tools/hw_detect/cpu.h"
#include <errno.h>
#include <assert.h>


/*  Header for local functions */
#include "work.h"

#ifdef USE_PAPI
#include <papi.h>
#endif

#ifdef USE_VTRACE
#include "vt_user.h"
#endif

/* number of functions (needed by BenchIT Framework, see bi_getinfo()) */
int n_of_works;
int n_of_sure_funcs_per_work;

/* variables to store settings from PARAMETERS file 
 * parsed by evaluate_environment() function */
unsigned long long BUFFERSIZE;
int HUGEPAGES=0,RUNS=0,EXTRA_CLFLUSH=0,OFFSET=0,FUNCTION=0,BURST_LENGTH=0,RANDOM=0;
int ALIGNMENT=64,NUM_RESULTS=0,TIMEOUT=0,NUM_THREADS=0,LOOP_OVERHEAD_COMPENSATION=0;
int EXTRA_FLUSH_SIZE=0,GLOBAL_FLUSH_BUFFER=0,DISABLE_CLFLUSH=1;
int THREAD_OFFSET=0;
long long INT_INIT[2]={1,-1};
double FP_INIT[2]={2.0,0.5};
unsigned long long ACCESSES=0;


/* string used for error message */
char *error_msg=NULL;

/* CPU bindings of threads, derived from CPU_LIST in PARAMETERS file */
cpu_set_t cpuset;
unsigned long long *cpu_bind;

/* memory affinity of threads, derived from MEM_BIND option in PARAMETERS file */
unsigned long long *mem_bind;

/* filename and filedescriptor for hugetlbfs */
char* filename;
int fd;

/* data structure for hardware detection */
static cpu_info_t *cpuinfo=NULL;

/* determined by hardware detection, needed to identify memory region */
long long CACHEFLUSHSIZE=0,L1_SIZE=-1,L2_SIZE=-1,L3_SIZE=-1,L4_SIZE=-1;
int CACHELINE=0,CACHELEVELS=0;

/* needed to derive elapsed time from clock cycles, determined by hw_detect */
unsigned long long FREQUENCY=0;

/* used to parse list of problemsizes in evaluate_environment()*/
unsigned long long MAX=0;
bi_list_t * problemlist;
unsigned long long problemlistsize;
double *problemarray1,*problemarray2;

/* data structure that holds all relevant information for kernel execution */
volatile mydata_t* mdp;

/* variables for the PAPI counters*/
#ifdef USE_PAPI
char **papi_names;
int *papi_codes;
int papi_num_counters;
int EventSet;
#endif

/* data for watchdog timer */
pthread_t watchdog;
typedef struct watchdog_args{
 pid_t pid;
 int timeout;
} watchdog_arg_t;
watchdog_arg_t watchdog_arg;

/* stops watchdog thread if benchmark finishes before timeout */
static void sigusr1_handler (int signum) {
 pthread_exit(0);
}

/** stops benchmark if timeout is reached
 */
static void *watchdog_timer(void *arg){
  sigset_t  signal_mask; 
  
  /* ignore SIGTERM and SIGINT */
  sigemptyset (&signal_mask);
  sigaddset (&signal_mask, SIGINT);
  sigaddset (&signal_mask, SIGTERM);
  pthread_sigmask (SIG_BLOCK, &signal_mask, NULL);
  
  /* watchdog thread will terminate after receiveing SIGUSR1 during bi_cleanup() */
  signal(SIGUSR1,sigusr1_handler);
  
  if (((watchdog_arg_t*)arg)->timeout>0){
     /* sleep for specified timeout before terminating benchmark */
     sleep(((watchdog_arg_t*)arg)->timeout);
     kill(((watchdog_arg_t*)arg)->pid,SIGTERM);
  }
  pthread_exit(0);
}

/** function that parses the PARAMETERS file
 */
void evaluate_environment(bi_info * info);

/**  The implementation of the bi_getinfo() from the BenchIT interface.
 *   Infostruct is filled with informations about the kernel.
 *   @param infostruct  a pointer to a structure filled with zero's
 */
void bi_getinfo( bi_info * infostruct )
{
   int i = 0, j = 0; /* loop var for n_of_works */
   char buff[512];
   (void) memset ( infostruct, 0, sizeof( bi_info ) );
   /* get environment variables for the kernel */
   evaluate_environment(infostruct);
   infostruct->codesequence = bi_strdup( CODE_SEQUENCE );
   infostruct->xaxistext = bi_strdup( X_AXIS_TEXT );
   infostruct->base_xaxis=10.0;
   infostruct->maxproblemsize=problemlistsize;
   sprintf(buff, KERNEL_DESCRIPTION);
   infostruct->kerneldescription = bi_strdup( buff );
   infostruct->num_processes = 1;
   infostruct->num_threads_per_process = NUM_THREADS;
   infostruct->kernel_execs_mpi1 = 0;
   infostruct->kernel_execs_mpi2 = 0;
   infostruct->kernel_execs_pvm = 0;
   infostruct->kernel_execs_omp = 0;
   infostruct->kernel_execs_pthreads = 1;

   /* GB/s + selected counters */
   n_of_works = 1;
   #ifdef USE_PAPI
    n_of_works+=papi_num_counters;
   #endif
      
   /* aggregate bandwidth of all threads */
   n_of_sure_funcs_per_work = 1;
   
   infostruct->numfunctions = n_of_works * n_of_sure_funcs_per_work;

   /* allocating memory for y axis texts and properties */
   infostruct->yaxistexts = malloc( infostruct->numfunctions * sizeof( char* ));
   if ( infostruct->yaxistexts == 0 ){
     fprintf( stderr, "Allocation of yaxistexts failed.\n" ); fflush( stderr );
     exit( 127 );
   }
   infostruct->outlier_direction_upwards = malloc( infostruct->numfunctions * sizeof( int ));
   if ( infostruct->outlier_direction_upwards == 0 ){
     fprintf( stderr, "Allocation of outlier direction failed.\n" ); fflush( stderr );
     exit( 127 );
   }
   infostruct->legendtexts = malloc( infostruct->numfunctions * sizeof( char* ));
   if ( infostruct->legendtexts == 0 ){
     fprintf( stderr, "Allocation of legendtexts failed.\n" ); fflush( stderr );
     exit( 127 );
   }
   infostruct->base_yaxis = malloc( infostruct->numfunctions * sizeof( double ));
   if ( infostruct->base_yaxis == 0 ){
     fprintf( stderr, "Allocation of base yaxis failed.\n" ); fflush( stderr );
     exit( 127 );
   }

   /* setting up y axis texts and properties */
   for ( j = 0; j < n_of_works; j++ ){
     int k,index;
       k=0;
       index= k + n_of_sure_funcs_per_work * j;
       infostruct->yaxistexts[index] = bi_strdup( Y_AXIS_TEXT_1 );
       infostruct->outlier_direction_upwards[index]=0;         //report maximum of iterations
       infostruct->base_yaxis[index] = 0;
       switch ( j ){
         case 0:  // GB/s
           sprintf(buff,"bandwidth %s ",bi_getenv( "BENCHIT_KERNEL_CPU_LIST", 0 ));
           infostruct->legendtexts[index] = bi_strdup( buff );
           break;
         default: // papi
          #ifdef USE_PAPI
           if (k)  sprintf(buff,"%s CPU%llu - CPU%llu",papi_names[j-1],cpu_bind[0],cpu_bind[k]);
           else sprintf(buff,"%s CPU%llu locally",papi_names[j-1],cpu_bind[0]);
           infostruct->legendtexts[index] = bi_strdup( buff );
           infostruct->outlier_direction_upwards[index] = 0;   //report maximum of iterations
           infostruct->yaxistexts[index] = bi_strdup( Y_AXIS_TEXT_2 );
          #endif
          break;
       } 
   }
}

/** Implementation of the bi_init() of the BenchIT interface.
 *  init data structures needed for kernel execution
 */
void* bi_init( int problemsizemax )
{
   int retval,t,j;
   unsigned long long i,tmp;
   unsigned int numa_node;
   struct bitmask *numa_bitmask;
   #ifdef USE_VTRACE
   VT_USER_START("INIT");
   #endif

   //printf("\n");
   //printf("sizeof mydata_t:           %i\n",sizeof(mydata_t));
   //printf("sizeof threaddata_t:       %i\n",sizeof(threaddata_t));
   //printf("sizeof cpu_info_t:         %i\n",sizeof(cpu_info_t));
   cpu_set(cpu_bind[0]); /* first thread binds to first CPU in list */

   
   //TODO replace unsigned long long with max data type size ???
   /* increase buffersize to account for alignment and offsets */
   //BUFFERSIZE=sizeof(char)*(MAX+ALIGNMENT+OFFSET+THREAD_OFFSET*NUM_THREADS+4*sizeof(unsigned long long));
   BUFFERSIZE=sizeof(char)*MAX;
   BUFFERSIZE=BUFFERSIZE/NUM_THREADS; // multiple threads
   BUFFERSIZE=BUFFERSIZE+ALIGNMENT+OFFSET+(THREAD_OFFSET*NUM_THREADS);
   //bei xeon phi: BUFFERSIZE=BUFFERSIZE+ALIGNMENT+OFFSET+0; durch PARAMETERS: THREAD_OFFSET=0;
   //printf("BUFFERSIZE: %llu\n",BUFFERSIZE);

   /* if hugepages are enabled increase buffersize to the smallest multiple of 2 MIB greater than buffersize */
   if (HUGEPAGES==HUGEPAGES_ON) BUFFERSIZE=(BUFFERSIZE+(2*1024*1024))&0xffe00000ULL;

   mdp->cpuinfo=cpuinfo;
   mdp->settings=0;
 
   /* overwrite detected clockrate if specified in PARAMETERS file*/
   if (FREQUENCY){
      mdp->cpuinfo->clockrate=FREQUENCY;
   }
   else if (mdp->cpuinfo->clockrate==0){
      fprintf( stderr, "Error: CPU-Clockrate could not be estimated\n" );
      exit( 1 );
   }
   
   /* overwrite cache parameters from hw_detection if specified in PARAMETERS file*/
   if(L1_SIZE>=0){
      mdp->cpuinfo->Cache_unified[0]=0;
      mdp->cpuinfo->Cache_shared[0]=0;
      mdp->cpuinfo->U_Cache_Size[0]=0;
      mdp->cpuinfo->I_Cache_Size[0]=L1_SIZE;
      mdp->cpuinfo->D_Cache_Size[0]=L1_SIZE;
      CACHELEVELS=1;
   }
   if(L2_SIZE>=0){
      mdp->cpuinfo->Cache_unified[1]=0;
      mdp->cpuinfo->Cache_shared[1]=0;
      mdp->cpuinfo->U_Cache_Size[1]=0;
      mdp->cpuinfo->I_Cache_Size[1]=L2_SIZE;
      mdp->cpuinfo->D_Cache_Size[1]=L2_SIZE;
      CACHELEVELS=2;
   }
   if(L3_SIZE>=0){
      mdp->cpuinfo->Cache_unified[2]=0;
      mdp->cpuinfo->Cache_shared[2]=0;
      mdp->cpuinfo->U_Cache_Size[2]=0;
      mdp->cpuinfo->I_Cache_Size[2]=L3_SIZE;
      mdp->cpuinfo->D_Cache_Size[2]=L3_SIZE;
      CACHELEVELS=3;
   }
   if(L4_SIZE>=0){
      mdp->cpuinfo->Cache_unified[3]=0;
      mdp->cpuinfo->Cache_shared[3]=0;
      mdp->cpuinfo->U_Cache_Size[3]=0;
      mdp->cpuinfo->I_Cache_Size[3]=L4_SIZE;
      mdp->cpuinfo->D_Cache_Size[3]=L4_SIZE;
      CACHELEVELS=4;
   }
   if (CACHELINE){
      mdp->cpuinfo->Cacheline_size[0]=CACHELINE;
      mdp->cpuinfo->Cacheline_size[1]=CACHELINE;
      mdp->cpuinfo->Cacheline_size[2]=CACHELINE;
      mdp->cpuinfo->Cacheline_size[3]=CACHELINE;
   }

   mdp->INT_INIT=INT_INIT;
   mdp->FP_INIT=FP_INIT;
   mdp->hugepages=HUGEPAGES;
   if (LOOP_OVERHEAD_COMPENSATION){
     mdp->settings|=LOOP_OVERHEAD_COMP;
     mdp->loop_overhead=LOOP_OVERHEAD_COMPENSATION;
   }


   if ((NUM_THREADS>mdp->cpuinfo->num_cores)||(NUM_THREADS==0)) NUM_THREADS=mdp->cpuinfo->num_cores;
   
   mdp->num_threads=NUM_THREADS;
   mdp->num_results=NUM_RESULTS;
   mdp->threads=_mm_malloc(NUM_THREADS*sizeof(pthread_t),ALIGNMENT);
   mdp->thread_comm=_mm_malloc(NUM_THREADS*sizeof(int),ALIGNMENT);
   if ((mdp->threads==NULL)||(mdp->thread_comm==NULL)){
     fprintf( stderr, "Error: Allocation of structure mydata_t failed\n" ); fflush( stderr );
     exit( 127 );
   }   

   printf("\n");  
   fflush(stdout);

   /* calculate required memory for flushes (always allocate enough for LLC flush as this can be required by coherence state control) */
   CACHEFLUSHSIZE=mdp->cpuinfo->U_Cache_Size[3]+cpuinfo->U_Cache_Size[2]+mdp->cpuinfo->U_Cache_Size[1]+mdp->cpuinfo->U_Cache_Size[0];
   CACHEFLUSHSIZE+=mdp->cpuinfo->D_Cache_Size[3]+mdp->cpuinfo->D_Cache_Size[2]+mdp->cpuinfo->D_Cache_Size[1]+mdp->cpuinfo->D_Cache_Size[0];
   CACHEFLUSHSIZE*=100+EXTRA_FLUSH_SIZE;
   CACHEFLUSHSIZE/=50; // double buffer size for implicit increase for LLC flushes

   if (CACHEFLUSHSIZE>mdp->cpuinfo->Cacheflushsize){
      mdp->cpuinfo->Cacheflushsize=CACHEFLUSHSIZE;
   }
   mdp->cache_flush_area=(char*)_mm_malloc(mdp->cpuinfo->Cacheflushsize,ALIGNMENT);
   if (mdp->cache_flush_area == 0){
      fprintf( stderr, "Error: Allocation of structure mydata_t failed\n" ); fflush( stderr );
      exit( 127 );
   }
   //fill cacheflush-area
   tmp=sizeof(unsigned long long);
   for (i=0;i<mdp->cpuinfo->Cacheflushsize;i+=tmp){
      *((unsigned long long*)((unsigned long long)mdp->cache_flush_area+i))=(unsigned long long)i;
   }
   clflush(mdp->cache_flush_area,mdp->cpuinfo->Cacheflushsize,*(mdp->cpuinfo));
     
   if (CACHELEVELS>mdp->cpuinfo->Cachelevels){
      mdp->cpuinfo->Cachelevels=CACHELEVELS;
   }

   mdp->threaddata = _mm_malloc(mdp->num_threads*sizeof(threaddata_t),ALIGNMENT);
   memset( mdp->threaddata,0,mdp->num_threads*sizeof(threaddata_t));
  #ifdef USE_PAPI
   mdp->Eventset=EventSet;
   mdp->num_events=papi_num_counters;
   if (papi_num_counters){ 
    mdp->values=(long long*)malloc(papi_num_counters*sizeof(long long));
    mdp->papi_results=(double*)malloc(papi_num_counters*sizeof(double));
   }
   else {
     mdp->values=NULL;
     mdp->papi_results=NULL;
   }
  #endif
  
  if (generic_num_packages()!=-1) mdp->threads_per_package=calloc(generic_num_packages(),sizeof(int));
  else mdp->threads_per_package=calloc(1,sizeof(int));

  for (i=0;i<NUM_THREADS;i++){
    if (get_pkg(cpu_bind[i])!=-1) mdp->threaddata[i].package=get_pkg(cpu_bind[i]);
    else mdp->threaddata[i].package=0;
    mdp->threads_per_package[mdp->threaddata[i].package]++;
  }
 

  /* create threads */
  for (t=0;t<mdp->num_threads;t++){
    cpu_set(mem_bind[t]);
    numa_node = numa_node_of_cpu(mem_bind[t]);
    numa_bitmask = numa_bitmask_alloc((unsigned int) numa_max_possible_node());
    numa_bitmask = numa_bitmask_clearall(numa_bitmask);
    numa_bitmask = numa_bitmask_setbit(numa_bitmask, numa_node);
    numa_set_membind(numa_bitmask);
    numa_bitmask_free(numa_bitmask);

    mdp->threaddata[t].cpuinfo=(cpu_info_t*)_mm_malloc( sizeof( cpu_info_t ),ALIGNMENT);
    if ( mdp->cpuinfo == 0 ){
      fprintf( stderr, "Error: Allocation of structure mydata_t failed\n" ); fflush( stderr );
      exit( 127 );
    }
    #ifdef USE_PAPI
    if (papi_num_counters){ 
     mdp->threaddata[t].values=(long long*)malloc(papi_num_counters*sizeof(long long));
     mdp->threaddata[t].papi_results=(double*)malloc(papi_num_counters*sizeof(double));
    }
    else {
      mdp->threaddata[t].values=NULL;
      mdp->threaddata[t].papi_results=NULL;
    }
    #endif
    memcpy(mdp->threaddata[t].cpuinfo,mdp->cpuinfo,sizeof(cpu_info_t));
    mdp->ack=0;
    mdp->threaddata[t].thread_id=t;
    mdp->threaddata[t].cpu_id=cpu_bind[t];
    mdp->threaddata[t].mem_bind=mem_bind[t];
    mdp->threaddata[t].data=mdp;
    mdp->thread_comm[t]=THREAD_INIT;
    mdp->threaddata[t].settings=mdp->settings;
    if (GLOBAL_FLUSH_BUFFER){
       mdp->threaddata[t].cache_flush_area=mdp->cache_flush_area;
    }
    else {
       if (mdp->cache_flush_area==NULL) mdp->threaddata[t].cache_flush_area=NULL;
       else {
        mdp->threaddata[t].cache_flush_area=(char*)_mm_malloc(mdp->cpuinfo->Cacheflushsize,ALIGNMENT);
        if (mdp->threaddata[t].cache_flush_area == NULL){
           fprintf( stderr, "Error: Allocation of structure mydata_t failed\n" ); fflush( stderr );
           exit( 127 );
        }
        //fill cacheflush-area
        tmp=sizeof(unsigned long long);
        for (i=0;i<mdp->cpuinfo->Cacheflushsize;i+=tmp){
           *((unsigned long long*)((unsigned long long)mdp->threaddata[t].cache_flush_area+i))=(unsigned long long)i;
        }
        clflush(mdp->threaddata[t].cache_flush_area,mdp->cpuinfo->Cacheflushsize,*(mdp->cpuinfo));
       }
    }

    mdp->threaddata[t].length=ACCESSES;
    //printf("length: %llu \n",ACCESSES);
    mdp->threaddata[t].buffersize=BUFFERSIZE;
    mdp->threaddata[t].alignment=ALIGNMENT;
    mdp->threaddata[t].offset=OFFSET;    
    mdp->threaddata[t].thread_offset=THREAD_OFFSET;
    mdp->threaddata[t].FUNCTION=FUNCTION;
    mdp->threaddata[t].BURST_LENGTH=BURST_LENGTH;
    #ifdef USE_PAPI
    mdp->threaddata[t].Eventset=mdp->Eventset;    
    mdp->threaddata[t].num_events=mdp->num_events;
    #endif
    if (t){
      pthread_create(&(mdp->threads[t]),NULL,thread,(void*)(&(mdp->threaddata[t])));
      while (!mdp->ack);
    }
  }

  mdp->ack=0;mdp->done=0;
  cpu_set(mem_bind[0]);
  numa_node = numa_node_of_cpu(mem_bind[0]);
  numa_bitmask = numa_bitmask_alloc((unsigned int) numa_max_possible_node());
  numa_bitmask = numa_bitmask_clearall(numa_bitmask);
  numa_bitmask = numa_bitmask_setbit(numa_bitmask, numa_node);
  numa_set_membind(numa_bitmask);
  numa_bitmask_free(numa_bitmask);
 
  /* allocate memory for first thread */
  //printf("first thread, malloc: %llu \n",BUFFERSIZE);
  if (HUGEPAGES==HUGEPAGES_OFF) mdp->buffer = _mm_malloc( BUFFERSIZE,ALIGNMENT );
  if (HUGEPAGES==HUGEPAGES_ON){
     char *dir;
     dir=bi_getenv("BENCHIT_KERNEL_HUGEPAGE_DIR",0);
     filename=(char*)malloc((strlen(dir)+20)*sizeof(char));
     sprintf(filename,"%s/thread_data_0",dir);
     mdp->buffer=NULL;
     fd=open(filename,O_CREAT|O_RDWR,0664);
     if (fd == -1){
       fprintf( stderr, "Error: could not create file in hugetlbfs\n" ); fflush( stderr );
       perror("open");
       exit( 127 );
     } 
     mdp->buffer=(char*) mmap(NULL,BUFFERSIZE,PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);
     close(fd);unlink(filename);
  } 
  if ((mdp->buffer == 0)||(mdp->buffer == (void*) -1ULL)){
     fprintf( stderr, "Error: Allocation of buffer failed\n" ); fflush( stderr );
     if (HUGEPAGES==HUGEPAGES_ON) perror("mmap");
     exit( 127 );
  }
 
   /* initialize buffer */
  switch (FUNCTION){
   case 0: //gpr_store_si
   case 1: //gpr_load_si
   case 2: //gpr_add_si
   case 3: //gpr_mul_si
   case 4: //gpr_and_si
   case 5: //gpr_or_si
   case 6: //gpr_xor_si
   case 7: //gpr_cmp_si
   case 8: //load_pi
   case 13: //store_pi
   case 14: //store_nt_pi
   case 17: //copy_pi
   case 18: //copy_nt_pi
   case 21: //scale_pi
   case 22: //scale_nt_pi
   case 24: //add_pi
   case 29: //mul_pi
   case 40: //and_pi
   case 57: //avx_load_pi
   case 63: //avx_store_pi
   case 66: //avx_copy_pi
   case 73: //avx_add_pi
   case 74: //avx_mul_pi
   case 76: //avx_scale_pi
   case 79: //xor_pi
   case 80: //or_pi
   
   tmp=4*BURST_LENGTH*sizeof(long long);
   for (i=0;i<=BUFFERSIZE-tmp;i+=tmp){
      for(j=0;j<2*BURST_LENGTH;j++)
        *((long long*)((unsigned long long)mdp->buffer+i+j*sizeof(long long)))=INT_INIT[0];
      for(j=2*BURST_LENGTH;j<4*BURST_LENGTH;j++)
        *((long long*)((unsigned long long)mdp->buffer+i+j*sizeof(long long)))=INT_INIT[1];
   }
   break;

   case 75: //avx_and_pi
   case 77: //avx_xor_pi
   case 78: //avx_or_pi
   case 81: //avx_gt_pi
   case 82: //avx_eq_pi
   case 83: //avx_gt_pi8
   case 84: //avx_eq_pi8
   for (i=0;i<4*BURST_LENGTH;i++){ // AVX -> 4 (4*8 Byte = 32 Byte = AVX Register length)
        *((long long*)((unsigned long long)mdp->buffer+i*sizeof(long long)))=INT_INIT[0];
   }
   for (;i<BUFFERSIZE/sizeof(long long);i++){
        *((long long*)((unsigned long long)mdp->buffer+i*sizeof(long long)))=INT_INIT[1];
   }
   case 33: //mul_add_pd
  /* SSE double prec., mul_add */

   /* avoid FP overflows:
      create x, x, 1/x, -x pattern to guarantee stable register values for mul_add (alternating mul and add)
      (i.e product of {[0],[2]}= 1 and sum of {[1].[3]} = 0) */  
   tmp=8*BURST_LENGTH*sizeof(double);
   for (i=0;i<=BUFFERSIZE-tmp;i+=tmp){   
      for(j=0;j<2*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[0];
      for(j=2*BURST_LENGTH;j<4*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[0];
      for(j=4*BURST_LENGTH;j<6*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[1];
      for(j=6*BURST_LENGTH;j<8*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=-1.0*FP_INIT[0];
    }
    break;

   case 59: //avx_mul_add_pd
  /* AVX double prec., mul_add */

   /* avoid FP overflows:
      create x, x, 1/x, -x pattern to guarantee stable register values for mul_add (alternating mul and add)
      (i.e product of {[0],[2]}= 1 and sum of {[1].[3]} = 0) */   
   tmp=16*BURST_LENGTH*sizeof(double);
   for (i=0;i<=BUFFERSIZE-tmp;i+=tmp){   
      for(j=0;j<4*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[0];
      for(j=4*BURST_LENGTH;j<8*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[0];
      for(j=8*BURST_LENGTH;j<12*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[1];
      for(j=12*BURST_LENGTH;j<16*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=-1.0*FP_INIT[0];
    }
    break;

   case 9: //load_pd
   case 12: //store_pd
   case 16: //copy_pd
   case 20: //scale_pd
   case 23: //add_pd
   case 26: //add_sd
   case 28: //mul_pd
   case 31: //mul_sd
   case 34: //mul_plus_add_pd
   case 35: //div_pd
   case 37: //div_sd
   case 39: //and_pd
   case 42: //sqrt_pd
   case 44: //sqrt_sd
  /* SSE double prec., not mul_add */

   /* avoid FP overflows:
      create x, -1/x, x, -1/x, -x, 1/x, -x, 1/x pattern to guarantee stable register values for add, mul, and mul_plus_add (mul with subsequent add)
      (i.e sum = 0, product = 1, and sum of all partial products = 0) */   
   tmp=16*BURST_LENGTH*sizeof(double);
   for (i=0;i<=BUFFERSIZE-tmp;i+=tmp){   
      for(j=0;j<2*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[0];
      for(j=2*BURST_LENGTH;j<4*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=-1.0*FP_INIT[1];
      for(j=4*BURST_LENGTH;j<6*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[0];
      for(j=6*BURST_LENGTH;j<8*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=-1.0*FP_INIT[1];
      for(j=8*BURST_LENGTH;j<10*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=-1.0*FP_INIT[0];
      for(j=10*BURST_LENGTH;j<12*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[1];
      for(j=12*BURST_LENGTH;j<14*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=-1.0*FP_INIT[0];
      for(j=14*BURST_LENGTH;j<16*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[1];
    }
    break;

   case 46: //avx_add_pd
   case 48: //avx_mul_pd
   case 50: //avx_div_pd
   case 52: //avx_sqrt_pd
   case 54: //avx_and_pd
   case 56: //avx_load_pd
   case 60: //avx_mul_plus_add_pd
   case 62: //avx_store_pd
   case 65: //avx_copy_pd
   case 68: //avx_scale_pd
   case 69: //avx_fma_pd
   case 71: //avx_fma4_pd
	
  /* AVX double prec. not mul_add */
   /* avoid FP overflows:
      create x, -1/x, x, -1/x, -x, 1/x, -x, 1/x pattern to guarantee stable register values for add, mul, and mul_plus_add (mul with subsequent add)
      (i.e sum = 0, product = 1, and sum of all partial products = 0) */   
   tmp=32*BURST_LENGTH*sizeof(double);
   for (i=0;i<=BUFFERSIZE-tmp;i+=tmp){   
      for(j=0;j<4*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[0];
      for(j=4*BURST_LENGTH;j<8*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=-1.0*FP_INIT[1];
      for(j=8*BURST_LENGTH;j<12*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[0];
      for(j=12*BURST_LENGTH;j<16*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=-1.0*FP_INIT[1];
      for(j=16*BURST_LENGTH;j<20*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=-1.0*FP_INIT[0];
      for(j=20*BURST_LENGTH;j<24*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[1];
      for(j=24*BURST_LENGTH;j<28*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=-1.0*FP_INIT[0];
      for(j=28*BURST_LENGTH;j<32*BURST_LENGTH;j++)
        *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[1];
    }
    break;
   
   case 10: //load_ps
   case 11: //store_ps
   case 15: //copy_ps
   case 19: //scale_ps
   case 25: //add_ps
   case 27: //add_ss
   case 30: //mul_ps
   case 32: //mul_ss
   case 36: //div_ps
   case 38: //div_ss
   case 41: //and_ps
   case 43: //sqrt_ps
   case 45: //sqrt_ss

   /* avoid FP overflows:
      create x, -1/x, x, -1/x, -x, 1/x, -x, 1/x pattern to guarantee stable register values for add and mul
      (i.e sum = 0 and product = 1) */
   tmp=32*BURST_LENGTH*sizeof(float);
   for (i=0;i<=BUFFERSIZE-tmp;i+=tmp){  
      for(j=0;j<4*BURST_LENGTH;j++)
        *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=(float)FP_INIT[0];
      for(j=4*BURST_LENGTH;j<8*BURST_LENGTH;j++)
        *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=-1.0*(float)FP_INIT[1];
      for(j=8*BURST_LENGTH;j<12*BURST_LENGTH;j++)
        *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=(float)FP_INIT[0];
      for(j=12*BURST_LENGTH;j<16*BURST_LENGTH;j++)
        *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=-1.0*(float)FP_INIT[1];
      for(j=16*BURST_LENGTH;j<20*BURST_LENGTH;j++)
        *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=-1.0*(float)FP_INIT[0];
      for(j=20*BURST_LENGTH;j<24*BURST_LENGTH;j++)
        *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=(float)FP_INIT[1];
      for(j=24*BURST_LENGTH;j<28*BURST_LENGTH;j++)
        *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=-1.0*(float)FP_INIT[0];
      for(j=28*BURST_LENGTH;j<32*BURST_LENGTH;j++)
        *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=(float)FP_INIT[1];
   }
   break;

   case 47: //avx_add_ps
   case 49: //avx_mul_ps
   case 51: //avx_div_ps
   case 53: //avx_sqrt_ps
   case 55: //avx_and_ps
   case 58: //avx_load_ps
   case 61: //avx_store_ps
   case 64: //avx_copy_ps
   case 67: //avx_scale_ps
   case 70: //avx_fma_ps
   case 72: //avx_fma4_ps
   /* AVX single prec. */

   /* avoid FP overflows:
      create x, -1/x, x, -1/x, -x, 1/x, -x, 1/x pattern to guarantee stable register values for add and mul
      (i.e sum = 0 and product = 1) */
   tmp=64*BURST_LENGTH*sizeof(float);
   for (i=0;i<=BUFFERSIZE-tmp;i+=tmp){  
      for(j=0;j<8*BURST_LENGTH;j++)
        *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=(float)FP_INIT[0];
      for(j=8*BURST_LENGTH;j<16*BURST_LENGTH;j++)
        *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=-1.0*(float)FP_INIT[1];
      for(j=16*BURST_LENGTH;j<24*BURST_LENGTH;j++)
        *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=(float)FP_INIT[0];
      for(j=24*BURST_LENGTH;j<32*BURST_LENGTH;j++)
        *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=-1.0*(float)FP_INIT[1];
      for(j=32*BURST_LENGTH;j<40*BURST_LENGTH;j++)
        *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=-1.0*(float)FP_INIT[0];
      for(j=40*BURST_LENGTH;j<48*BURST_LENGTH;j++)
        *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=(float)FP_INIT[1];
      for(j=48*BURST_LENGTH;j<56*BURST_LENGTH;j++)
        *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=-1.0*(float)FP_INIT[0];
      for(j=56*BURST_LENGTH;j<64*BURST_LENGTH;j++)
        *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=(float)FP_INIT[1];
   }
   break;

  /* MIC single prec. */
  /* avoid FP overflows:
     create x, -1/x, x, -1/x, -x, 1/x, -x, 1/x pattern to guarantee stable register values for add and mul
     (i.e sum = 0 and product = 1) */
  tmp=128*BURST_LENGTH*sizeof(float);
  for (i=0;i<=BUFFERSIZE-tmp;i+=tmp){
     for(j=0;j<16*BURST_LENGTH;j++)
       *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=(float)FP_INIT[0];
     for(j=16*BURST_LENGTH;j<32*BURST_LENGTH;j++)
       *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=-1.0*(float)FP_INIT[1];
     for(j=32*BURST_LENGTH;j<48*BURST_LENGTH;j++)
       *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=(float)FP_INIT[0];
     for(j=48*BURST_LENGTH;j<64*BURST_LENGTH;j++)
       *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=-1.0*(float)FP_INIT[1];
     for(j=64*BURST_LENGTH;j<80*BURST_LENGTH;j++)
       *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=-1.0*(float)FP_INIT[0];
     for(j=80*BURST_LENGTH;j<96*BURST_LENGTH;j++)
       *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=(float)FP_INIT[1];
     for(j=96*BURST_LENGTH;j<112*BURST_LENGTH;j++)
       *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=-1.0*(float)FP_INIT[0];
     for(j=112*BURST_LENGTH;j<128*BURST_LENGTH;j++)
       *((float*)((unsigned long long)mdp->buffer+i+j*sizeof(float)))=(float)FP_INIT[1];
  }
  break;

  /* MIC double prec. */
  /* avoid FP overflows:
     create x, -1/x, x, -1/x, -x, 1/x, -x, 1/x pattern to guarantee stable register values for add, mul, and mul_plus_add (mul with subsequent add)
     (i.e sum = 0, product = 1, and sum of all partial products = 0) */
  tmp=64*BURST_LENGTH*sizeof(double);
  for (i=0;i<=BUFFERSIZE-tmp;i+=tmp){
     for(j=0;j<8*BURST_LENGTH;j++)
       *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[0];
     for(j=8*BURST_LENGTH;j<16*BURST_LENGTH;j++)
       *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=-1.0*FP_INIT[1];
     for(j=16*BURST_LENGTH;j<24*BURST_LENGTH;j++)
       *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[0];
     for(j=24*BURST_LENGTH;j<32*BURST_LENGTH;j++)
       *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=-1.0*FP_INIT[1];
     for(j=32*BURST_LENGTH;j<40*BURST_LENGTH;j++)
       *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=-1.0*FP_INIT[0];
     for(j=40*BURST_LENGTH;j<48*BURST_LENGTH;j++)
       *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[1];
     for(j=48*BURST_LENGTH;j<56*BURST_LENGTH;j++)
       *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=-1.0*FP_INIT[0];
     for(j=56*BURST_LENGTH;j<64*BURST_LENGTH;j++)
       *((double*)((unsigned long long)mdp->buffer+i+j*sizeof(double)))=FP_INIT[1];
   }
   break;

   default:
    fprintf( stderr, "Error: initialization failed: unknown mode:%i \n",FUNCTION );      
    exit( 1 );
  }
   clflush(mdp->buffer,BUFFERSIZE,*(mdp->cpuinfo));
 
  cpu_set(cpu_bind[0]);
  printf("  wait for threads memory initialization \n");fflush(stdout);
  /* wait for threads to finish their initialization */  
  for (t=1;t<mdp->num_threads;t++){
     mdp->ack=0;
     mdp->thread_comm[t]=THREAD_WAIT;
     while (!mdp->ack);
  }
  mdp->ack=0;
  printf("    ...done\n");
  if ((num_packages()!=-1)&&(num_cores_per_package()!=-1)&&(num_threads_per_core()!=-1))  printf("  num_packages: %i, %i cores per package, %i threads per core\n",num_packages(),num_cores_per_package(),num_threads_per_core());
  printf("  using %i threads\n",NUM_THREADS);
  for (i=0;i<NUM_THREADS;i++) if ((get_pkg(cpu_bind[i])!=-1)&&(get_core_id(cpu_bind[i])!=-1)) printf("    - Thread %llu runs on CPU %llu, core %i in package: %i\n",i,cpu_bind[i],get_core_id(cpu_bind[i]),get_pkg(cpu_bind[i]));
  fflush(stdout);

  #ifdef USE_VTRACE
  VT_USER_END("INIT");
  #endif

  /* start watchdog thread */
  watchdog_arg.pid=getpid();
  watchdog_arg.timeout=TIMEOUT;
  pthread_create(&watchdog,NULL,watchdog_timer,&watchdog_arg);
  
  return (void*)mdp;
}

/** The central function within each kernel. This function
 *  is called for each measurment step seperately.
 *  @param  mdpv         a pointer to the structure created in bi_init,
 *                       it is the pointer the bi_init returns
 *  @param  problemsize  the actual problemsize
 *  @param  results      a pointer to a field of doubles, the
 *                       size of the field depends on the number
 *                       of functions, there are #functions+1
 *                       doubles
 *  @return 0 if the measurment was sucessfull, something
 *          else in the case of an error
 */
int inline bi_entry( void* mdpv, int problemsize, double* results )
{
  /* j is used for loop iterations */
  int j = 0,k = 0;
  /* real problemsize*/
  unsigned long long rps;
  /* cast void* pointer */
  mydata_t* mdp = (mydata_t*)mdpv;

  /* results */
  double *tmp_results;
  #ifdef USE_PAPI
   tmp_results=malloc((1+papi_num_counters)*sizeof(double));
  #else
   tmp_results=malloc(sizeof(double));
  #endif
 
  /* calculate real problemsize */
  if (RANDOM){
  rps = problemarray2[problemsize-1];
  } else {
  rps = problemarray1[problemsize-1];
  }

  /* check wether the pointer to store the results in is valid or not */
  if ( results == NULL ) return 1;

  mdp->threaddata[0].length=ACCESSES; // restore length, used internally to return actual number of accesses
  _work(rps,OFFSET,FUNCTION,BURST_LENGTH,mdp,&tmp_results);
  results[0] = (double)rps;

  /* copy tmp_results to final results */  
  results[1]=tmp_results[0];
  #ifdef USE_PAPI
   for (j=0;j<papi_num_counters;j++)
   {
     results[j+2]=tmp_results[j+1];
   }
  #endif
  free(tmp_results);
  return 0;
}

/** Clean up the memory
 */
void bi_cleanup( void* mdpv )
{
   int t;
   
   mydata_t* mdp = (mydata_t*)mdpv;
   /* terminate other threads */
   for (t=1;t<mdp->num_threads;t++)
   {
    mdp->ack=0;
    mdp->thread_comm[t]=THREAD_STOP;
    pthread_join((mdp->threads[t]),NULL);
   } 
   pthread_kill(watchdog,SIGUSR1);

   /* free resources */
   if ((HUGEPAGES==HUGEPAGES_OFF)&&(mdp->buffer)) _mm_free(mdp->buffer);
   if (HUGEPAGES==HUGEPAGES_ON){
     if(mdp->buffer!=NULL) munmap((void*)mdp->buffer,BUFFERSIZE);
   }
   if (mdp->cache_flush_area!=NULL) _mm_free (mdp->cache_flush_area);
   if (mdp->threaddata){
     for (t=1;t<mdp->num_threads;t++){
        if (mdp->threaddata[t].cpuinfo) _mm_free(mdp->threaddata[t].cpuinfo);
     }
     _mm_free(mdp->threaddata);   
   }
   if (mdp->threads) _mm_free(mdp->threads);
   if (mdp->thread_comm) _mm_free(mdp->thread_comm);
   if (mdp->cpuinfo) _mm_free(mdp->cpuinfo);
   _mm_free( mdp );
   return;
}

/********************************************************************/
/*************** End of interface implementations *******************/
/********************************************************************/

/* Reads the environment variables used by this kernel. */
void evaluate_environment(bi_info * info)
{
   int i;
   char arch[16];
   int errors = 0;
   char * p = 0;
   struct timeval time;

   #ifdef PAPI_UNCORE
   // variables for uncore measurement setup
   int uncore_cidx=-1;
   PAPI_cpu_option_t cpu_opt;
   PAPI_granularity_option_t gran_opt;
   PAPI_domain_option_t domain_opt;
   const PAPI_component_info_t *cmp_info;
   #endif
  
   cpuinfo=(cpu_info_t*)_mm_malloc( sizeof( cpu_info_t ),64);memset((void*)cpuinfo,0,sizeof( cpu_info_t ));
   if ( cpuinfo == 0 ) {
      fprintf( stderr, "Error: Allocation of structure cpuinfo_t failed\n" ); fflush( stderr );
      exit( 127 );
   }
   init_cpuinfo(cpuinfo,1);

   mdp = (mydata_t*)_mm_malloc( sizeof( mydata_t ),ALIGNMENT);memset((void*)mdp,0, sizeof( mydata_t ));
   if ( mdp == 0 ) {
      fprintf( stderr, "Error: Allocation of structure mydata_t failed\n" ); fflush( stderr );
      exit( 127 );
   }

   error_msg=malloc(256);

   /* generate ordered list of data set sizes in problemarray1*/
   p = bi_getenv( "BENCHIT_KERNEL_PROBLEMLIST", 0 );
   if ( p == 0 ){
     unsigned long long MIN;
     int STEPS;
     double MemFactor;
     p = bi_getenv("BENCHIT_KERNEL_MIN",0);
     if ( p == 0 ) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_MIN not set");}
     else MIN=atoll(p);
     p = bi_getenv("BENCHIT_KERNEL_MAX",0);
     if ( p == 0 ) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_MAX not set");}
     else MAX=atoll(p);
     p = bi_getenv("BENCHIT_KERNEL_STEPS",0);
     if ( p == 0 ) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_STEPS not set");}
     else STEPS=atoi(p);
     if ( errors == 0){
       problemarray1=malloc(STEPS*sizeof(double));
       MemFactor =((double)MAX)/((double)MIN);
       MemFactor = pow(MemFactor, 1.0/((double)STEPS-1));
       for (i=0;i<STEPS;i++){ 
          problemarray1[i] = ((double)MIN)*pow(MemFactor, i);
       }
       problemlistsize=STEPS;
       problemarray1[STEPS-1]=(double)MAX;
     }
   }
   else{
     fflush(stdout);printf("BenchIT: parsing list of problemsizes: ");
     bi_parselist(p);
     problemlist = info->list;
     problemlistsize = info->listsize;
     problemarray1=malloc(problemlistsize*sizeof(double));
     for (i=0;i<problemlistsize;i++){ 
        problemarray1[i]=problemlist->dnumber;
        if (problemlist->pnext!=NULL) problemlist=problemlist->pnext;
        if (problemarray1[i]>MAX) MAX=problemarray1[i];
     }
   }

   p = bi_getenv( "BENCHIT_KERNEL_RANDOM", 0 );
   if (p) RANDOM=atoi(p);

   if (RANDOM) {
   /* generate random order of measurements in 2nd array */
     gettimeofday( &time, (struct timezone *) 0);
     problemarray2=malloc(problemlistsize*sizeof(double));
     _random_init(time.tv_usec,problemlistsize);
     for (i=0;i<problemlistsize;i++) problemarray2[i] = problemarray1[(int) _random()];
   }
 
   CPU_ZERO(&cpuset);NUM_THREADS==0;
   if (bi_getenv( "BENCHIT_KERNEL_CPU_LIST", 0 )!=NULL) p=bi_strdup(bi_getenv( "BENCHIT_KERNEL_CPU_LIST", 0 ));else p=NULL;
   if (p){
     char *q,*r,*s;
     i=0;
     do{
       q=strstr(p,",");if (q) {*q='\0';q++;}
       s=strstr(p,"/");if (s) {*s='\0';s++;}
       r=strstr(p,"-");if (r) {*r='\0';r++;}
       
       if ((s)&&(r)) for (i=atoi(p);i<=atoi(r);i+=atoi(s)) {if (cpu_allowed(i)) {CPU_SET(i,&cpuset);NUM_THREADS++;}}
       else if (r) for (i=atoi(p);i<=atoi(r);i++) {if (cpu_allowed(i)) {CPU_SET(i,&cpuset);NUM_THREADS++;}}
       else if (cpu_allowed(atoi(p))) {CPU_SET(atoi(p),&cpuset);NUM_THREADS++;}
       p=q;
     }while(p!=NULL);
   }
   else { /* use all allowed CPUs if not defined otherwise */
     for (i=0;i<CPU_SETSIZE;i++) {if (cpu_allowed(i)) {CPU_SET(i,&cpuset);NUM_THREADS++;}}
   }

   /* bind threads to available cores in specified order */
   if (NUM_THREADS==0) {errors++;sprintf(error_msg,"No allowed CPUs in BENCHIT_KERNEL_CPU_LIST");}
   else
   {
     int j=0;
     cpu_bind=(unsigned long long*)malloc((NUM_THREADS+1)*sizeof(unsigned long long));
     if (bi_getenv( "BENCHIT_KERNEL_CPU_LIST", 0 )!=NULL) p=bi_strdup(bi_getenv( "BENCHIT_KERNEL_CPU_LIST", 0 ));else p=NULL;
     if (p)
     {
       char *q,*r,*s;
       i=0;
       do
       {
         q=strstr(p,",");if (q) {*q='\0';q++;}
         s=strstr(p,"/");if (s) {*s='\0';s++;}
         r=strstr(p,"-");if (r) {*r='\0';r++;}
       
         if ((s)&&(r)) for (i=atoi(p);i<=atoi(r);i+=atoi(s)) {if (cpu_allowed(i)) {cpu_bind[j]=i;j++;}}
         else if (r) for (i=atoi(p);i<=atoi(r);i++) {if (cpu_allowed(i)) {cpu_bind[j]=i;j++;}}
         else if (cpu_allowed(atoi(p))) {cpu_bind[j]=atoi(p);j++;}
         p=q;
       }
       while(p!=NULL);
     }
     else { /* no order specified */ 
       for(i=0;i<CPU_SETSIZE;i++){
        if (CPU_ISSET(i,&cpuset)) {cpu_bind[j]=i;j++;}
       }
     }
   }
   NUM_RESULTS=NUM_THREADS;

   p = bi_getenv( "BENCHIT_KERNEL_CPU_FREQUENCY", 0 );
   if ( p != 0 ) FREQUENCY = atoll( p );
   p = bi_getenv( "BENCHIT_KERNEL_L1_SIZE", 0 );
   if ( p != 0 ) L1_SIZE = atoll( p );  
   p = bi_getenv( "BENCHIT_KERNEL_L2_SIZE", 0 );
   if ( p != 0 ) L2_SIZE = atoll( p );  
   p = bi_getenv( "BENCHIT_KERNEL_L3_SIZE", 0 );
   if ( p != 0 ) L3_SIZE = atoll( p ); 
   p = bi_getenv( "BENCHIT_KERNEL_L4_SIZE", 0 );
   if ( p != 0 ) L4_SIZE = atoll( p ); 
   p = bi_getenv( "BENCHIT_KERNEL_CACHELINE_SIZE", 0 );
   if ( p != 0 ) CACHELINE = atoi( p );

   p=bi_getenv( "BENCHIT_KERNEL_ALLOC", 0 );
   if (p==0) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_ALLOC not set");}
   else {
     mem_bind=(unsigned long long*)malloc((NUM_THREADS+1)*sizeof(unsigned long long));
     if (!strcmp(p,"G")) for (i=0;i<NUM_THREADS;i++) mem_bind[i] = cpu_bind[0];
     else if (!strcmp(p,"L")) for (i=0;i<NUM_THREADS;i++) mem_bind[i] = cpu_bind[i];
     else if (!strcmp(p,"B")) {
       int j=0;

       if (bi_getenv( "BENCHIT_KERNEL_MEM_BIND", 0 )!=NULL) p=bi_strdup(bi_getenv( "BENCHIT_KERNEL_MEM_BIND", 0 ));else p=NULL;
       if (p)
       {
         char *q,*r,*s;
         i=0;
         do
         {
           q=strstr(p,",");if (q) {*q='\0';q++;}
           s=strstr(p,"/");if (s) {*s='\0';s++;}
           r=strstr(p,"-");if (r) {*r='\0';r++;}

           if ((s)&&(r)) for (i=atoi(p);i<=atoi(r);i+=atoi(s)) {if (cpu_allowed(i)) {if (j<=NUM_THREADS) mem_bind[j]=i;j++;} else {errors++;sprintf(error_msg,"selected CPU not allowed");}}
           else if (r) for (i=atoi(p);i<=atoi(r);i++) {if (cpu_allowed(i)) {if (j<=NUM_THREADS) mem_bind[j]=i;j++;} else {errors++;sprintf(error_msg,"selected CPU not allowed");}}
           else if (cpu_allowed(atoi(p))) {if (j<=NUM_THREADS) mem_bind[j]=atoi(p);j++;} else {errors++;sprintf(error_msg,"selected CPU not allowed");}
           p=q;
         }
         while((p!=NULL)&&(j<NUM_THREADS));
         if (j<NUM_THREADS) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_MEM_BIND too short");}
       }
       else {errors++;sprintf(error_msg,"BENCHIT_KERNEL_MEM_BIND not set, required by BENCHIT_KERNEL_ALLOC=\"B\"");}
     }
     else {errors++;sprintf(error_msg,"invalid setting for BENCHIT_KERNEL_ALLOC");}
   }

   p = bi_getenv( "BENCHIT_KERNEL_SIZE", 0 );
   if ( p == 0 ) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_SIZE not set");}
   else ACCESSES = atoll( p );
   p=bi_getenv("BENCHIT_KERNEL_INT_INIT", 0);
   if (p) {
      INT_INIT[0]=atoll(p);
      p=bi_getenv("BENCHIT_KERNEL_INT_INIT2", 0);
      if (p) {
        INT_INIT[1]=atoll(p);
      } else {
        INT_INIT[1]=INT_INIT[0]*-1;
      }
   }
   
   p=bi_getenv("BENCHIT_KERNEL_FP_INIT", 0);
   if (p) {
      FP_INIT[0]=atof(p);
      p=bi_getenv("BENCHIT_KERNEL_FP_INIT2", 0);
      if (p) {
        FP_INIT[1]=atof(p);
      } else {
        FP_INIT[1]=(1.0/FP_INIT[0]);
      }
   }

   p=bi_getenv( "BENCHIT_KERNEL_HUGEPAGES", 0 );
   if (p==0) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_HUGEPAGES not set");}
   else {
     if (!strcmp(p,"0")) HUGEPAGES=HUGEPAGES_OFF;
     else if (!strcmp(p,"1")) HUGEPAGES=HUGEPAGES_ON;
     else {errors++;sprintf(error_msg,"invalid setting for BENCHIT_KERNEL_HUGEPAGES");}
   }
   
   p = bi_getenv( "BENCHIT_KERNEL_OFFSET", 0 );
   if ( p == 0 ) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_OFFSET not set");}
   else OFFSET = atoi( p );

   p=bi_getenv( "BENCHIT_KERNEL_INSTRUCTION", 0 );
   if (p==0) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_INSTRUCTION not set");}
   else {
     if (0);
     else if (!strcmp(p,"gpr_store_si")) {
       ALIGNMENT=64;OFFSET=0;FUNCTION=0;
     }
     else if (!strcmp(p,"gpr_load_si")) {
       ALIGNMENT=64;OFFSET=0;FUNCTION=1;
     }
     else if (!strcmp(p,"gpr_add_si")) {
       ALIGNMENT=64;OFFSET=0;FUNCTION=2;
     }
     else if (!strcmp(p,"gpr_mul_si")) {
       ALIGNMENT=64;OFFSET=0;FUNCTION=3;
     }
     else if (!strcmp(p,"gpr_and_si")) {
       ALIGNMENT=64;OFFSET=0;FUNCTION=4;
     }
     else if (!strcmp(p,"gpr_or_si")) {
       ALIGNMENT=64;OFFSET=0;FUNCTION=5;
     }
     else if (!strcmp(p,"gpr_xor_si")) {
       ALIGNMENT=64;OFFSET=0;FUNCTION=6;
     }
     else if (!strcmp(p,"gpr_cmp_si")) {
       ALIGNMENT=64;OFFSET=0;FUNCTION=7;
     }
     else if (!strcmp(p,"load_pi")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=8;
     }
     else if (!strcmp(p,"load_pd")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=9;
     }
     else if (!strcmp(p,"load_ps")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=10;
     }
     else if (!strcmp(p,"store_ps")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=11;
     }
     else if (!strcmp(p,"store_pd")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=12;
     }
     else if (!strcmp(p,"store_pi")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=13;
     }
     else if (!strcmp(p,"store_nt_pi")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=14;
     }
     else if (!strcmp(p,"copy_ps")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=15;
     }
     else if (!strcmp(p,"copy_pd")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=16;
     }
     else if (!strcmp(p,"copy_pi")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=17;
     }
     else if (!strcmp(p,"copy_nt_pi")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=18;
     }
     else if (!strcmp(p,"scale_ps")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=19;
     }
     else if (!strcmp(p,"scale_pd")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=20;
     }
     else if (!strcmp(p,"scale_pi")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=21;
     }
     else if (!strcmp(p,"scale_nt_pi")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=22;
     }
     else if (!strcmp(p,"add_pd")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=23;
     }
     else if (!strcmp(p,"add_pi")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=24;
     }
     else if (!strcmp(p,"add_ps")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=25;
     }
     else if (!strcmp(p,"add_sd")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=26;
     }
     else if (!strcmp(p,"add_ss")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=27;
     }
     else if (!strcmp(p,"mul_pd")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=28;
     }
     else if (!strcmp(p,"mul_pi")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=29;
     }
     else if (!strcmp(p,"mul_ps")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=30;
     }
     else if (!strcmp(p,"mul_sd")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=31;
     }
     else if (!strcmp(p,"mul_ss")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=32;
     }
     else if (!strcmp(p,"mul_add_pd")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=33;
     }
     else if (!strcmp(p,"mul_plus_add_pd")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=34;
     }
     else if (!strcmp(p,"div_pd")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=35;
     }
     else if (!strcmp(p,"div_ps")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=36;
     }
     else if (!strcmp(p,"div_sd")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=37;
     }
     else if (!strcmp(p,"div_ss")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=38;
     }
     else if (!strcmp(p,"and_pd")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=39;
     }
     else if (!strcmp(p,"and_pi")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=40;
     }
     else if (!strcmp(p,"and_ps")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=41;
     }
     else if (!strcmp(p,"sqrt_pd")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=42;
     }
     else if (!strcmp(p,"sqrt_ps")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=43;
     }
     else if (!strcmp(p,"sqrt_sd")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=44;
     }
     else if (!strcmp(p,"sqrt_ss")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=45;
     }
     else if (!strcmp(p,"avx_add_pd")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=46;
     }
     else if (!strcmp(p,"avx_add_ps")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=47;
     }
     else if (!strcmp(p,"avx_mul_pd")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=48;
     }
     else if (!strcmp(p,"avx_mul_ps")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=49;
     }
     else if (!strcmp(p,"avx_div_pd")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=50;
     }
     else if (!strcmp(p,"avx_div_ps")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=51;
     }
     else if (!strcmp(p,"avx_sqrt_pd")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=52;
     }
     else if (!strcmp(p,"avx_sqrt_ps")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=53;
     }
     else if (!strcmp(p,"avx_and_pd")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=54;
     }
     else if (!strcmp(p,"avx_and_ps")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=55;
     }
     else if (!strcmp(p,"avx_load_pd")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=56;
     }
     else if (!strcmp(p,"avx_load_pi")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=57;
     }
     else if (!strcmp(p,"avx_load_ps")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=58;
     }
     else if (!strcmp(p,"avx_mul_add_pd")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=59;
     }
     else if (!strcmp(p,"avx_mul_plus_add_pd")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=60;
     }
     else if (!strcmp(p,"avx_store_ps")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=61;
     }
     else if (!strcmp(p,"avx_store_pd")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=62;
     }
     else if (!strcmp(p,"avx_store_pi")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=63;
     }
     else if (!strcmp(p,"avx_copy_ps")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=64;
     }
     else if (!strcmp(p,"avx_copy_pd")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=65;
     }
     else if (!strcmp(p,"avx_copy_pi")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=66;
     }
     else if (!strcmp(p,"avx_scale_ps")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=67;
     }
     else if (!strcmp(p,"avx_scale_pd")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=68;
     }
     else if (!strcmp(p,"avx_fma_pd")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=69;
     }
     else if (!strcmp(p,"avx_fma_ps")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=70;
     }
     else if (!strcmp(p,"avx_fma4_pd")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=71;
     }
     else if (!strcmp(p,"avx_fma4_ps")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=72;
     }
     else if (!strcmp(p,"avx_add_pi")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=73;
     }
     else if (!strcmp(p,"avx_mul_pi")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=74;
     }
     else if (!strcmp(p,"avx_and_pi")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=75;
     }
     else if (!strcmp(p,"avx_scale_pi")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=76;
     }
     else if (!strcmp(p,"avx_xor_pi")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=77;
     }
     else if (!strcmp(p,"avx_or_pi")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=78;
     }
     else if (!strcmp(p,"xor_pi")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=79;
     }
     else if (!strcmp(p,"or_pi")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=80;
     }
     else if (!strcmp(p,"avx_gt_pi")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=81;
     }
     else if (!strcmp(p,"avx_eq_pi")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=82;
     }
     else if (!strcmp(p,"avx_gt_pi8")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=83;
     }
     else if (!strcmp(p,"avx_eq_pi8")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=84;
     }
     else {errors++;sprintf(error_msg,"invalid setting for BENCHIT_KERNEL_INSTRUCTION");}
   }
   p = bi_getenv( "BENCHIT_KERNEL_BURST_LENGTH", 0 );
   if ( p == 0 ) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_BURST_LENGTH not set");}
   else BURST_LENGTH = atoi( p );
   p=bi_getenv( "BENCHIT_KERNEL_THREAD_OFFSET", 0 );
   if (p!=0) THREAD_OFFSET=atoi(p);

   p=bi_getenv( "BENCHIT_KERNEL_TSC_SYNC", 0 );
   if (p!=0)
   {
     if (!strcmp(p,"enabled")) {cpuinfo->tsc_invariant=1;}
     else if (!strcmp(p,"disabled")) {cpuinfo->tsc_invariant=0;}
     else if (strcmp(p,"auto")) {errors++;sprintf(error_msg,"invalid setting for BENCHIT_KERNEL_TSC_SYNC");}
   }

   p=bi_getenv( "BENCHIT_KERNEL_LOOP_OVERHEAD_COMPENSATION", 0 );
   if (p!=0)
   {
     if (!strcmp(p,"enabled")) {
       int tmp_ovrhd;
       LOOP_OVERHEAD_COMPENSATION=asm_loop_overhead(10000);
       for (i=0;i<1000;i++){
         tmp_ovrhd=asm_loop_overhead(10000);
         if (tmp_ovrhd<LOOP_OVERHEAD_COMPENSATION){
           i=0;
           LOOP_OVERHEAD_COMPENSATION=tmp_ovrhd;
         }
       }
     }
     else if (!strcmp(p,"disabled")) {LOOP_OVERHEAD_COMPENSATION=0;}
     else {errors++;sprintf(error_msg,"invalid setting for BENCHIT_KERNEL_LOOP_OVERHEAD_COMPENSATION");}
   }

   p=bi_getenv( "BENCHIT_KERNEL_TIMEOUT", 0 );
   if (p!=0){
     TIMEOUT=atoi(p);
   }
   
   p=bi_getenv( "BENCHIT_KERNEL_SERIALIZATION", 0 );
   if ((p!=0)&&(strcmp(p,"mfence"))&&(strcmp(p,"cpuid"))&&(strcmp(p,"disabled"))) {errors++;sprintf(error_msg,"invalid setting for BENCHIT_KERNEL_SERIALIZATION");}

   #ifdef USE_PAPI
   p=bi_getenv( "BENCHIT_KERNEL_ENABLE_PAPI", 0 );
   if (p==0) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_ENABLE_PAPI not set");}
   else if (atoi(p)>0) {
      papi_num_counters=0;
      p=bi_getenv( "BENCHIT_KERNEL_PAPI_COUNTERS", 0 );
      if ((p!=0)&&(strcmp(p,""))){
        if (PAPI_library_init(PAPI_VER_CURRENT) != PAPI_VER_CURRENT){
          sprintf(error_msg,"PAPI library init error\n");errors++;
        }
        else{      
          char* tmp;
          papi_num_counters=1;
          tmp=p;
          PAPI_thread_init(pthread_self);
          while (strstr(tmp,",")!=NULL) {tmp=strstr(tmp,",")+1;papi_num_counters++;}
          papi_names=(char**)malloc(papi_num_counters*sizeof(char*));
          papi_codes=(int*)malloc(papi_num_counters*sizeof(int));
         
          tmp=p;
          for (i=0;i<papi_num_counters;i++){
            tmp=strstr(tmp,",");
            if (tmp!=NULL) {*tmp='\0';tmp++;}
            papi_names[i]=p;p=tmp;
            if (PAPI_event_name_to_code(papi_names[i],&papi_codes[i])!=PAPI_OK){
             sprintf(error_msg,"Papi error: unknown Counter: %s\n",papi_names[i]);fflush(stdout);
             papi_num_counters=0;errors++;
            }
          }
          
          EventSet = PAPI_NULL;
          if (PAPI_create_eventset(&EventSet) != PAPI_OK) {
             sprintf(error_msg,"PAPI error, could not create eventset\n");fflush(stdout);
             papi_num_counters=0;errors++;
          }

          #ifdef PAPI_UNCORE
          /* configure PAPI for uncore measurements 
           * based on: https://icl.cs.utk.edu/papi/docs/d3/d57/tests_2perf__event__uncore_8c_source.html
           */
           
          //find uncore component
          uncore_cidx=PAPI_get_component_index("perf_event_uncore");
          if (uncore_cidx<0) {
            sprintf(error_msg,"PAPI error, perf_event_uncore component not found");fflush(stdout);
            papi_num_counters=0;errors++;
          }
          else{
            cmp_info=PAPI_get_component_info(uncore_cidx);
            if (cmp_info->disabled) {
              sprintf(error_msg,"PAPI error, uncore component disabled; /proc/sys/kernel/perf_event_paranoid set to 0?");fflush(stdout);
              papi_num_counters=0;errors++;
            }
            else{
              //assign event set to uncore component
              PAPI_assign_eventset_component(EventSet, uncore_cidx);           
            }
          }
          
          //bind to measuring CPU
          cpu_opt.eventset=EventSet;
          cpu_opt.cpu_num=cpu_bind[0];
          if (PAPI_set_opt(PAPI_CPU_ATTACH,(PAPI_option_t*)&cpu_opt) !=  PAPI_OK) {
            sprintf(error_msg,"PAPI error, PAPI_CPU_ATTACH failed; might need to run as root");fflush(stdout);
            papi_num_counters=0;errors++;
          }
          
          //set granularity to PAPI_GRN_SYS
          gran_opt.def_cidx=0;
          gran_opt.eventset=EventSet;
          gran_opt.granularity=PAPI_GRN_SYS;
          if (PAPI_set_opt(PAPI_GRANUL,(PAPI_option_t*)&gran_opt) != PAPI_OK) {
            sprintf(error_msg,"PAPI error, setting PAPI_GRN_SYS failed");fflush(stdout);
            papi_num_counters=0;errors++;
          }
          
          //set domain to PAPI_DOM_ALL
          domain_opt.def_cidx=0;
          domain_opt.eventset=EventSet;
          domain_opt.domain=PAPI_DOM_ALL;
          if (PAPI_set_opt(PAPI_DOMAIN,(PAPI_option_t*)&domain_opt) != PAPI_OK) {
            sprintf(error_msg,"PAPI error, setting PAPI_DOM_ALL failed");fflush(stdout);
            papi_num_counters=0;errors++;
          }
          #endif

          for (i=0;i<papi_num_counters;i++) { 
            if ((PAPI_add_event(EventSet, papi_codes[i]) != PAPI_OK)){
              #ifdef PAPI_UNCORE
              sprintf(error_msg,"PAPI error, could not add counter %s to eventset for uncore counters.\n",papi_names[i]);fflush(stdout);
              #else
              sprintf(error_msg,"PAPI error, could not add counter %s to eventset for core counters.\n",papi_names[i]);fflush(stdout);
              #endif
              papi_num_counters=0;errors++;
            }
          }
        }
      }
      #ifdef USE_VTRACE
       mdp->cid_papi=calloc(papi_num_counters,sizeof(unsigned int));
       mdp->gid_papi=calloc(papi_num_counters,sizeof(unsigned int));
       for (i=0;i<papi_num_counters;i++){
         mdp->gid_papi[i] = VT_COUNT_GROUP_DEF("papi counters");
         mdp->cid_papi[i] = VT_COUNT_DEF(papi_names[i], "number", VT_COUNT_TYPE_DOUBLE, mdp->gid_papi[i]);
       }
      #endif
      if (papi_num_counters>0) PAPI_start(EventSet);
   }
   #endif

   if ((BURST_LENGTH>4)&&(BURST_LENGTH!=8)&&(BURST_LENGTH!=16))
     {errors++;sprintf(error_msg,"BURST LENGTH %i not supported",BURST_LENGTH);}

   if ( errors > 0 ) {
      fprintf( stderr, "Error: There's an environment variable not set or invalid!\n" );      
      fprintf( stderr, "%s\n", error_msg);
      exit( 1 );
   }
   free(error_msg);
   
   get_architecture(arch,sizeof(arch));
   if (strcmp(arch,"x86_64")) {
      fprintf( stderr, "Error: wrong architecture: %s, x86_64 required \n",arch );
      exit( 1 );
   }

   if (cpuinfo->features&CLFLUSH!=CLFLUSH) {
      fprintf( stderr, "Error: required function \"clflush\" not supported!\n" );
      exit( 1 );
   }
   
   if (cpuinfo->features&CPUID!=CPUID) {
      fprintf( stderr, "Error: required function \"cpuid\" not supported!\n" );
      exit( 1 );
   }
   
   if (cpuinfo->features&TSC!=TSC) {
      fprintf( stderr, "Error: required function \"rdtsc\" not supported!\n" );
      exit( 1 );
   }

   
   switch (FUNCTION){
     case 8: //load_pi
     case 9: //load_pd
     case 13: //store_pi
     case 14: //store_nt_pi
     case 17: //copy_pi
     case 18: //copy_nt_pi
     case 21: //scale_pi
     case 22: //scale_nt_pi
     case 23: //add_pd
     case 24: //add_pi
     case 25: //add_ps
     case 26: //add_sd
     case 27: //add_ss
     case 28: //mul_pd
     case 29: //mul_pi
     case 30: //mul_ps
     case 31: //mul_sd
     case 32: //mul_ss
     case 33: //mul_add_pd
     case 34: //mul_plus_add_pd
     case 35: //div_pd
     case 36: //div_ps
     case 37: //div_sd
     case 38: //div_ss
     case 39: //and_pd
     case 40: //and_pi
     case 41: //and_ps
     case 42: //sqrt_pd
     case 43: //sqrt_ps
     case 44: //sqrt_sd
     case 45: //sqrt_ss
     case 79: //xor_pi
     case 80: //or_pi
     if ((cpuinfo->features&SSE2)!=SSE2) {
         fprintf( stderr, "Error: SSE2 not supported!\n" );
         exit( 1 );
       }
     default:
       break;
   }
   switch (FUNCTION){
     case 21: //scale_pi
     case 22: //scale_nt_pi
     case 29: //mul_pi
     if ((cpuinfo->features&SSE4_1)!=SSE4_1) {
         fprintf( stderr, "Error: SSE4.1 not supported!\n" );
         exit( 1 );
       }
     default:
       break;
   }
   switch (FUNCTION){
     case 46: //avx_add_pd
     case 47: //avx_add_ps
     case 48: //avx_mul_pd
     case 49: //avx_mul_ps
     case 50: //avx_div_pd
     case 51: //avx_div_ps
     case 52: //avx_sqrt_pd
     case 53: //avx_sqrt_ps
     case 54: //avx_and_pd
     case 55: //avx_and_ps
     case 56: //avx_load_pd
     case 57: //avx_load_pi
     case 58: //avx_load_ps
     case 59: //avx_mul_add_pd
     case 60: //avx_mul_plus_add_pd
     case 61: //avx_store_ps
     case 62: //avx_store_pd
     case 63: //avx_store_pi
     case 64: //avx_copy_ps
     case 65: //avx_copy_pd
     case 66: //avx_copy_pi
     case 67: //avx_scale_ps
     case 68: //avx_scale_pd
     case 71: //avx_fma4_pd
     case 72: //avx_fma4_ps
     if ((cpuinfo->features&AVX)!=AVX) {
         fprintf( stderr, "Error: AVX not supported!\n" );
         exit( 1 );
       }
     default:
       break;
   }
   switch (FUNCTION){
     case 73: //avx_add_pi
     case 74: //avx_mul_pi
     case 75: //avx_and_pi
     case 76: //avx_scale_pi
     case 77: //avx_xor_pi
     case 81: //avx_gt_pi
     case 82: //avx_eq_pi
     case 83: //avx_gt_pi8
     case 84: //avx_eq_pi8
     if ((cpuinfo->features&AVX2)!=AVX2) {
         fprintf( stderr, "Error: AVX2 not supported!\n" );
         exit( 1 );
       }
     default:
       break;
   }
   switch (FUNCTION){
     case 69: //avx_fma_pd
     case 70: //avx_fma_ps
     if ((cpuinfo->features&FMA)!=FMA) {
         fprintf( stderr, "Error: FMA not supported!\n" );
         exit( 1 );
       }
     default:
       break;
   }
   switch (FUNCTION){
     case 71: //avx_fma4_pd
     case 72: //avx_fma4_ps
     if ((cpuinfo->features&FMA4)!=FMA4) {
         fprintf( stderr, "Error: FMA4 not supported!\n" );
         exit( 1 );
       }
     default:
       break;
   }

    
}
