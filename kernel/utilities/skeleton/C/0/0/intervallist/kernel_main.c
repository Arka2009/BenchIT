/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: kernel_main.c 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/utilities/skeleton/C/0/0/intervallist/kernel_main.c $
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* Kernel: simple Variant of the c-Skeleton with list PARAMETER
 *******************************************************************/
 
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "interface.h"

#include "simple.h"

bi_info * myinfo;

/**  The implementation of the bi_getinfo from the BenchIT interface.
 *   Here the infostruct is filled with informations about the
 *   kernel.
 *   @param infostruct  a pointer to a structure filled with zero's
 */
void bi_getinfo( bi_info * pinfo )
{
   char * p = 0;
   
   (void) memset ( pinfo, 0, sizeof( bi_info ) );
   myinfo=pinfo;

   /* get environment variables for the kernel */
   p = bi_getenv( "BENCHIT_KERNEL_PROBLEMLIST", 0 );
   bi_parselist(p);
 
   pinfo->codesequence = bi_strdup( "start kernel; do nothing; " );
   pinfo->kerneldescription = bi_strdup( "simple skeleton for c kernels" );
   pinfo->xaxistext = bi_strdup( "Problem Size" );
   pinfo->maxproblemsize = myinfo->listsize;
   pinfo->num_processes = 1;
   pinfo->num_threads_per_process = 0;
   pinfo->kernel_execs_mpi1 = 0;
   pinfo->kernel_execs_mpi2 = 0;
   pinfo->kernel_execs_pvm = 0;
   pinfo->kernel_execs_omp = 0;
   pinfo->kernel_execs_pthreads = 0;
   pinfo->numfunctions = 1;

   /* allocating memory for y axis texts and properties */
   pinfo->yaxistexts = malloc( pinfo->numfunctions * sizeof( char* ) );
   if ( pinfo->yaxistexts == NULL )
   {
     fprintf( stderr, "Allocation of yaxistexts failed.\n" ); fflush( stderr );
     exit( 127 );
   }
   pinfo->outlier_direction_upwards = malloc( pinfo->numfunctions * sizeof( int ) );
   if ( pinfo->outlier_direction_upwards == NULL )
   {
     fprintf( stderr, "Allocation of outlier direction failed.\n" ); fflush( stderr );
     exit( 127 );
   }
   pinfo->legendtexts = malloc( pinfo->numfunctions * sizeof( char* ) );
   if ( pinfo->legendtexts == NULL )
   {
     fprintf( stderr, "Allocation of legendtexts failed.\n" ); fflush( stderr );
     exit( 127 );
   }
   pinfo->base_yaxis = malloc( pinfo->numfunctions * sizeof( double ) );
   if ( pinfo->base_yaxis == NULL )
   {
     fprintf( stderr, "Allocation of base yaxis failed.\n" ); fflush( stderr );
     exit( 127 );
   }

   /* setting up y axis texts and properties */
   pinfo->yaxistexts[0] = bi_strdup( "time in s" );
   pinfo->outlier_direction_upwards[0] = 0;
   pinfo->base_yaxis[0] = 10; //logarythmic axis 10^x
   pinfo->legendtexts[0] = bi_strdup( "time in s" );
 
}



/** Implementation of the bi_init of the BenchIT interface.
 *  Here you have the chance to allocate the memory you need.
 *  It is also possible to allocate the memory at the beginning
 *  of every single measurment and to free the memory thereafter.
 *  But making usage always of the same memory is faster.
 *  HAVE A LOOK INTO THE HOWTO !
 */
void* bi_init( int problemsizemax )
{
   void * no_personel_data=NULL;

   return no_personel_data;
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
 *  @return 0 if the measurment was suscessfull, something
 *          else in the case of an error
 */
int bi_entry( void * mdpv, int iproblemsize, double * dresults )
{
  /* dstart, dend: the start and end time of the measurement */
  /* dtime: the time for a single measurement in seconds */
  double dstart = 0.0, dend = 0.0, dtime = 0.0;
  /* flops stores the calculated FLOPS */
  double dres = 0.0;
  /* ii is used for loop iterations */
  int ii = 0;
  double dmyproblemsize = 0.0;

  /* get real problemsize */
  dmyproblemsize = bi_get_list_element(iproblemsize); 
  
  /* check wether the pointer to store the results in is valid or not */
  if ( dresults == NULL ) return 1;

  /* get the actual time
   * do the measurement / your algorythm
   * get the actual time
   */
  dstart = bi_gettime(); 
  dres = simple(&dmyproblemsize); 
  dend = bi_gettime();

//  fprintf( stderr, "Problemsize=%d, Value=%f\n", imyproblemsize, dres);

  /* calculate the used time and FLOPS */
  dtime = dend - dstart;
  dtime -= dTimerOverhead;
      
  /* If the operation was too fast to be measured by the timer function,
   * mark the result as invalid 
   */
  if( dtime < dTimerGranularity ) dtime = INVALID_MEASUREMENT;

  /* store the results in results[1], results[2], ...
  * [1] for the first function, [2] for the second function
  * and so on ...
  * the index 0 always keeps the value for the x axis
  */
  dresults[0] = dmyproblemsize;
  dresults[1] = dtime;

  return 0;
}

/** Clean up the memory
 */
void bi_cleanup( void* mdpv )
{
   return;
}

