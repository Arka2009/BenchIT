/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: work.h 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/utilities/skeleton/C/0/PCL/0/work.h $
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* Kernel: c pcl kernel skeleton
 *******************************************************************/

#ifndef __work_h
#define __work_h

#ifdef BENCHIT_USE_PCL
#include <pcl.h>
#endif

#if (defined (_CRAYMPP) || \
     defined (_USE_SHORT_AS_INT))
typedef short myinttype;
#elif (defined (_USE_LONG_AS_INT))
typedef long myinttype;
#else
typedef int myinttype;
#endif

/** The data structure that holds all the data.
 *  Please use this construct instead of global variables.
 *  Global Variables seem to have large access times (?).
 */
typedef struct mydata
{
   myinttype dummy;
#ifdef BENCHIT_USE_PCL
   int *doable_list;
   int doable_nevents;
   unsigned int mode;
   PCL_DESCR_TYPE descr;
   PCL_CNT_TYPE * i_result;
   PCL_FP_CNT_TYPE * fp_result;
#endif
/*
   <variabletype1> <variablename1>;
   <variabletype2> <variablename2>;
*/
} mydata_t;

extern void work_1( void );
extern void work_2( void );

#endif

