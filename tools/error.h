/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: error.h 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/tools/error.h $
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* extended error numbers 
 *******************************************************************/

#ifndef __BENCHIT_ERROR_H
#define __BENCHIT_ERROR_H 1


#include <errno.h>

/*
 * Must be equal largest errno
 * #define ELAST       102
 */
 #ifndef ELAST
 #define ELAST 1000
 #endif
       
#define BUNDEF      ELAST+1     /* undefined BenchIT error */
#define BNOSHELL    ELAST+2     /* system() couldnt open a shell */ 
#define BSHELLEX    ELAST+3     /* system() process failed */
#define BENVEMPTY   ELAST+4     /* environment variable set but empty */
#define BENVUNKNOWN ELAST+5     /* unknown value in env-variable */




#define BLAST       ELAST+3     /* must be equal largest errornumber */ 

#endif /* error.h */
