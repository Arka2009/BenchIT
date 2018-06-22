/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: benchscript.h 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/tools/benchscript.h $
 * For license details see COPYING in the package base directory
 *******************************************************************/

#ifndef BENCHSCRIPT_H
#define BENCHSCRIPT_H

extern double logx( double base, double value );
extern char* int2char( int number );
extern char* bi_strcat( const char *str1, const char *str2 );

/* NEW */

extern void bi_script( char* script, int num_processes, int num_threads );
extern void bi_script_create_processes( char* script, int num_processes, int num_threads );
extern void bi_script_create_threads( char* script, int num_threads );
extern void* bi_script_run( void* script );

#endif

