/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: kernel_main.h 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/utilities/skeleton/php/0/0/0/kernel_main.h $
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* Kernel: php kernel skeleton
 *******************************************************************/

#ifndef __kernelmain_h
#define __kernelmain_h

/** The data structure that holds all the data.
 *  Please use this construct instead of global variables.
 *  Global Variables seem to have large access times (?).
 */
typedef struct mydata
{
  /* measurement bounds */
  int min;
  int max;
  int logbase;
  int steps;
   
  /* gloabl enviroment */ 
  int num_processes;
  int num_threads; 
   
  /* script runtime specifics */
  char* interpreter;
  char* kerneldir;
  int min_runtime;
   
  /* database specific data */
  char* dbserver;
  char* dbname;
  char* dbuser;
  char* dbpass;
} mydata_t;

void evaluate_environment( mydata_t * pmydata );

#endif

