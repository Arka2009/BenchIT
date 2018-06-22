/******************************************************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id$
 * For license details see COPYING in the package base directory
 *****************************************************************************************************/
/* Kernel: measures aggregate write bandwidth of multiple parallel threads for cache levels and main memory.
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


/*  Header for local functions */
#include "work.h"

#ifdef USE_PAPI
#include <papi.h>
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
int FLUSH_L1=0,FLUSH_L2=0,FLUSH_L3=0,FLUSH_L4=0,NUM_FLUSHES=0,NUM_USES=0,FLUSH_MODE=0,ENABLE_CODE_PREFETCH=0,FLUSH_SHARED_CPU=0;
int USE_MODE=0,THREAD_OFFSET=0,USE_DIRECTION=0;


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

/* needed for cacheflush function, determined by hardware detection */
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
      mdp->cpuinfo->Cacheflushsize-=mdp->cpuinfo->U_Cache_Size[0];
      mdp->cpuinfo->Cacheflushsize-=mdp->cpuinfo->D_Cache_Size[0];
      mdp->cpuinfo->Cacheflushsize+=L1_SIZE;
      mdp->cpuinfo->Cache_unified[0]=0;
      mdp->cpuinfo->Cache_shared[0]=0;
      mdp->cpuinfo->U_Cache_Size[0]=0;
      mdp->cpuinfo->I_Cache_Size[0]=L1_SIZE;
      mdp->cpuinfo->D_Cache_Size[0]=L1_SIZE;
      CACHELEVELS=1;
   }
   if(L2_SIZE>=0){
      mdp->cpuinfo->Cacheflushsize-=mdp->cpuinfo->U_Cache_Size[1];
      mdp->cpuinfo->Cacheflushsize-=mdp->cpuinfo->D_Cache_Size[1];
      mdp->cpuinfo->Cacheflushsize+=L2_SIZE;
      mdp->cpuinfo->Cache_unified[1]=0;
      mdp->cpuinfo->Cache_shared[1]=0;
      mdp->cpuinfo->U_Cache_Size[1]=0;
      mdp->cpuinfo->I_Cache_Size[1]=L2_SIZE;
      mdp->cpuinfo->D_Cache_Size[1]=L2_SIZE;
      CACHELEVELS=2;
   }
   if(L3_SIZE>=0){
      mdp->cpuinfo->Cacheflushsize-=mdp->cpuinfo->U_Cache_Size[2];
      mdp->cpuinfo->Cacheflushsize-=mdp->cpuinfo->D_Cache_Size[2];
      mdp->cpuinfo->Cacheflushsize+=L3_SIZE;
      mdp->cpuinfo->Cache_unified[2]=0;
      mdp->cpuinfo->Cache_shared[2]=0;
      mdp->cpuinfo->U_Cache_Size[2]=0;
      mdp->cpuinfo->I_Cache_Size[2]=L3_SIZE;
      mdp->cpuinfo->D_Cache_Size[2]=L3_SIZE;
      CACHELEVELS=3;
   }
   if(L4_SIZE>=0){
      mdp->cpuinfo->Cacheflushsize-=mdp->cpuinfo->U_Cache_Size[3];
      mdp->cpuinfo->Cacheflushsize-=mdp->cpuinfo->D_Cache_Size[3];
      mdp->cpuinfo->Cacheflushsize+=L4_SIZE;
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

   mdp->NUM_FLUSHES=NUM_FLUSHES;
   mdp->NUM_USES=NUM_USES;
   mdp->FLUSH_MODE=FLUSH_MODE;
   mdp->ENABLE_CODE_PREFETCH=ENABLE_CODE_PREFETCH;
   mdp->USE_MODE=USE_MODE;
   mdp->USE_DIRECTION=USE_DIRECTION;
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

   /* enable selected cache flushes */
   if ((FLUSH_L1)&&(mdp->cpuinfo->U_Cache_Size[0]+mdp->cpuinfo->D_Cache_Size[0]!=0)){ 
      mdp->settings|=FLUSH(1);
      if (mdp->cpuinfo->Cacheline_size[0]==0){
        fprintf( stderr, "Error: unknown Cacheline-length for L1 cache\n" );
        exit( 1 );    
      }     
   }
   if ((FLUSH_L2)&&(mdp->cpuinfo->U_Cache_Size[1]+mdp->cpuinfo->D_Cache_Size[1]!=0)){
      mdp->settings|=FLUSH(2);
      if (mdp->cpuinfo->Cacheline_size[1]==0){
        fprintf( stderr, "Error: unknown Cacheline-length for L2 cache\n" );
        exit( 1 );    
      }     
   }
   if ((FLUSH_L3)&&(mdp->cpuinfo->U_Cache_Size[2]+mdp->cpuinfo->D_Cache_Size[2]!=0)){ 
      mdp->settings|=FLUSH(3);
      if (mdp->cpuinfo->Cacheline_size[2]==0){
        fprintf( stderr, "Error: unknown Cacheline-length for L3 cache\n" );
        exit( 1 );    
      }     
   }
   if ((FLUSH_L4)&&(mdp->cpuinfo->U_Cache_Size[3]+mdp->cpuinfo->D_Cache_Size[3]!=0)){ 
      mdp->settings|=FLUSH(4);
      if (mdp->cpuinfo->Cacheline_size[3]==0){
        fprintf( stderr, "Error: unknown Cacheline-length for L4 cache\n" );
        exit( 1 );    
      }     
   }
   mdp->flush_share_cpu=(unsigned char)FLUSH_SHARED_CPU;
   printf("\n");     
   if (mdp->settings&FLUSH(1)) printf("  enabled L1 flushes\n");
   if (mdp->settings&FLUSH(2)) printf("  enabled L2 flushes\n");
   if (mdp->settings&FLUSH(3)) printf("  enabled L3 flushes\n");
   if (mdp->settings&FLUSH(4)) printf("  enabled L4 flushes\n");
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

    mdp->threaddata[t].USE_MODE=mdp->USE_MODE;
    mdp->threaddata[t].NUM_USES=mdp->NUM_USES;
    mdp->threaddata[t].USE_DIRECTION=mdp->USE_DIRECTION;
    mdp->threaddata[t].NUM_FLUSHES=mdp->NUM_FLUSHES;
    mdp->threaddata[t].FLUSH_MODE=mdp->FLUSH_MODE;
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
   tmp=sizeof(unsigned long long);
   for (i=0;i<=BUFFERSIZE-tmp;i+=tmp){
      *((unsigned long long*)((unsigned long long)mdp->buffer+i))=(unsigned long long)i;
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

  _work(rps,OFFSET,FUNCTION,BURST_LENGTH,RUNS,mdp,&tmp_results);
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

   p = bi_getenv( "BENCHIT_KERNEL_RUNS", 0 );
   if ( p != 0 ) RUNS = atoi( p );


   p = bi_getenv( "BENCHIT_KERNEL_FLUSH_L1", 0 );
   if ( p == 0 ) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_FLUSH_L1 not set");}
   else FLUSH_L1 = atoi( p );
   p = bi_getenv( "BENCHIT_KERNEL_FLUSH_L2", 0 );
   if ( p == 0 ) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_FLUSH_L2 not set");}
   else FLUSH_L2 = atoi( p );
   p = bi_getenv( "BENCHIT_KERNEL_FLUSH_L3", 0 );
   if ( p == 0 ) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_FLUSH_L3 not set");}
   else FLUSH_L3 = atoi( p );
   p = bi_getenv( "BENCHIT_KERNEL_FLUSH_L4", 0 );
   if ( p == 0 ) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_FLUSH_L4 not set");}
   else FLUSH_L4 = atoi( p );

   p = bi_getenv( "BENCHIT_KERNEL_FLUSH_ACCESSES", 0 );
   if ( p != 0 ) NUM_FLUSHES = atoi( p );
   else NUM_FLUSHES=1;

   p = bi_getenv( "BENCHIT_KERNEL_FLUSH_MODE", 0 );
   if ( p == 0 ) FLUSH_MODE=MODE_EXCLUSIVE;
   else{ 
     if (!strcmp(p,"M")) FLUSH_MODE=MODE_MODIFIED;
     else if (!strcmp(p,"E")) FLUSH_MODE=MODE_EXCLUSIVE;
     else if (!strcmp(p,"I")) FLUSH_MODE=MODE_INVALID;
     else if (!strcmp(p,"R")) FLUSH_MODE=MODE_RDONLY;
     else {errors++;sprintf(error_msg,"invalid setting for BENCHIT_KERNEL_FLUSH_MODE");};
   }

   p = bi_getenv( "BENCHIT_KERNEL_FLUSH_BUFFER", 0 );
   if ( p != 0 ){
     if (!strcmp(p,"G")) GLOBAL_FLUSH_BUFFER=1;
     else if (!strcmp(p,"T")) GLOBAL_FLUSH_BUFFER=0;
     else {errors++;sprintf(error_msg,"invalid setting for BENCHIT_KERNEL_FLUSH_BUFFER");};
   }



   p = bi_getenv( "BENCHIT_KERNEL_FLUSH_EXTRA", 0 );
   if ( p != 0 ) EXTRA_FLUSH_SIZE = atoi( p );
   if ((EXTRA_FLUSH_SIZE < 0) || (EXTRA_FLUSH_SIZE > 1000)){
     errors++;sprintf(error_msg,"invalid setting for BENCHIT_KERNEL_FLUSH_EXTRA");
   }
   else{
     cpuinfo->EXTRA_FLUSH_SIZE=100+EXTRA_FLUSH_SIZE;
   }

   p=bi_getenv( "BENCHIT_KERNEL_DISABLE_CLFLUSH", 0 );
   if (p!=0) DISABLE_CLFLUSH=atoi(p);
   cpuinfo->disable_clflush=DISABLE_CLFLUSH;
   
   p=bi_getenv( "BENCHIT_KERNEL_ENABLE_CODE_PREFETCH", 0 );
   if (p!=0) ENABLE_CODE_PREFETCH=atoi(p);

   p = bi_getenv( "BENCHIT_KERNEL_USE_ACCESSES", 0 );
   if ( p != 0 ) NUM_USES = atoi( p );
   else NUM_USES=1;

   p = bi_getenv( "BENCHIT_KERNEL_USE_MODE", 0 );
   if ( p == 0 ) USE_MODE=MODE_EXCLUSIVE;
   else { 
     if (!strcmp(p,"M")) USE_MODE=MODE_MODIFIED;
     else if (!strcmp(p,"E")) USE_MODE=MODE_EXCLUSIVE;
     else if (!strcmp(p,"I")) USE_MODE=MODE_INVALID;
     else {errors++;sprintf(error_msg,"invalid setting for BENCHIT_KERNEL_USE_MODE");}
   }
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

   p = bi_getenv( "BENCHIT_KERNEL_USE_DIRECTION", 0 );
   if ( p == 0 ) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_USE_DIRECTION not set");}
   else {
     if (!strcmp(p,"LIFO")) USE_DIRECTION=LIFO;
     else if (!strcmp(p,"FIFO")) USE_DIRECTION=FIFO;
     else {errors++;sprintf(error_msg,"invalid setting for BENCHIT_KERNEL_USE_DIRECTION");}
   }

   p=bi_getenv( "BENCHIT_KERNEL_INSTRUCTION", 0 );
   if (p==0) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_INSTRUCTION not set");}
   else {
     if (0);
     else if (!strcmp(p,"movdqa")) {
       ALIGNMENT=128;OFFSET=0;FUNCTION=0;
       if (ACCESS_STRIDE % 16 != 0) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_STRIDE has to be a multiple of 16 for movdqa instruction");}
     }
     else if (!strcmp(p,"vmovdqa")) {
       ALIGNMENT=256;OFFSET=0;FUNCTION=1;
       if (ACCESS_STRIDE % 32 != 0) {errors++;sprintf(error_msg,"BENCHIT_KERNEL_STRIDE has to be a multiple of 32 for vmovdqa instruction");}
     }
     else if (!strcmp(p,"movdqu")) {
       ALIGNMENT=128;OFFSET=OFFSET%ALIGNMENT;FUNCTION=2;
     }
     else if (!strcmp(p,"vmovdqu")) {
       ALIGNMENT=256;OFFSET=OFFSET%ALIGNMENT;FUNCTION=3;
     }
     else if (!strcmp(p,"mov")) {
       ALIGNMENT=64;OFFSET=OFFSET%ALIGNMENT;FUNCTION=4;
     }
     else if (!strcmp(p,"movnti")) {
       ALIGNMENT=64;OFFSET=OFFSET%ALIGNMENT;FUNCTION=5;
     }
     else if (!strcmp(p,"movntdq")) {
       ALIGNMENT=128;OFFSET=OFFSET%ALIGNMENT;FUNCTION=6;
     }
     else if (!strcmp(p,"vmovntdq")) {
       ALIGNMENT=256;OFFSET=OFFSET%ALIGNMENT;FUNCTION=7;
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
      if (papi_num_counters>0) PAPI_start(EventSet);
   }
   #endif

   if ((BURST_LENGTH>4)&&(BURST_LENGTH!=8)) {errors++;sprintf(error_msg,"BURST LENGTH %i not supported",BURST_LENGTH);}  
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

   if ((LINE_PREFETCH>0)&&(ACCESS_STRIDE>0)) {
      fprintf( stderr, "combination of BENCHIT_KERNEL_LINE_PREFETCH and BENCHIT_KERNEL_STRIDE not supported (one has to be 0)\n" );
      exit( 1 );
   }
   
   switch (FUNCTION){
     case 0: //movdqa
     case 2: //movdqu
     case 6: //movntdq
     if ((cpuinfo->features&SSE2)!=SSE2) {
         fprintf( stderr, "Error: SSE2 not supported!\n" );
         exit( 1 );
       }
     default:
       break;
   }
   switch (FUNCTION){
     case 1: //vmovdqa
     case 3: //vmovdqu
     case 7: //vmovntdq
     if ((cpuinfo->features&AVX)!=AVX) {
         fprintf( stderr, "Error: AVX not supported!\n" );
         exit( 1 );
       }
     default:
       break;
   }

   if (!strcmp("GenuineIntel",cpuinfo->vendor)){
     if (USE_MODE==MODE_MUW){
         fprintf( stderr, "Error: USE_MODE U not supported on Intel CPUs!\n" );
         exit( 1 );
       }
     if (USE_MODE==MODE_OWNED){
         fprintf( stderr, "Error: USE_MODE O not supported on Intel CPUs!\n" );
         exit( 1 );
       }
   }
   if (!strcmp("AuthenticAMD",cpuinfo->vendor)){
     if (USE_MODE==MODE_FORWARD){
         fprintf( stderr, "Error: USE_MODE F not supported on AMD CPUs!\n" );
         exit( 1 );
       }
   }

    
}
