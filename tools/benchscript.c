/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: benchscript.c 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/tools/benchscript.c $
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* The implementation of the BenchScript Interface
 *******************************************************************/

#include "benchscript.h"
#include "interface.h"

#include <stddef.h>
#include <sys/wait.h>
#include <pthread.h>
#include <math.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>

double logx( double base, double value )
{
  return log( value ) / log( base );
}

char* int2char( int number )
{
  char buffer[100], *ret_val;
  size_t size;

  size = sprintf( buffer, "%d", number ) * sizeof(char);

  ret_val = (char*) malloc ( size +1 );

  strcpy( ret_val, buffer );
  
  return ret_val;
}

char* bi_strcat( const char *str1, const char *str2 )
{
  const char *pi1, *pi2;
  char *so, *po;
  size_t size;

  pi1 = str1;
  while (*pi1 != '\0')
  {
    pi1++;
  }

  pi2 = str2;
  while (*pi2 != '\0')
  {
    pi2++;
  }

  size = ( ( ( pi1 + 1 - str1 ) + ( pi2 + 1 - str2 ) ) * sizeof(char) );

  so = (char*) malloc ( size );

  pi1 = str1;
  pi2 = str2;
  
  po = so;
  while (*pi1 != '\0')
  {
    *po++ = *pi1++;
  }
  while (*pi2 != '\0')
  {
    *po++ = *pi2++;
  }

  *po = *pi1;

  return (so);
}

void bi_script( char* script, int num_processes, int num_threads )
{
  if( num_processes <= 1 )
  {
    if( num_threads <= 1 )
    {
/*      printf( "************** single run **********************\n" ); */
      bi_script_run( (void*) script );
/*      printf( "************** single don **********************\n" ); */
    }
    else
    {
/*      printf( "************** threaded run ********************\n" ); */
      bi_script_create_threads( script, num_threads );
/*      printf( "************** threaded don ********************\n" ); */
    }
  }
  else
  {
/*      printf( "************** mproc run ***********************\n" ); */
    bi_script_create_processes( script, num_processes, num_threads );
/*      printf( "************** mproc don ***********************\n" ); */
  }
}

void bi_script_create_processes( char* script, int num_processes, int num_threads )
{
  int i,j;
  int first_pid, last_pid;
  int * child_pids;
  
  /* recognize the parent process pid */
  child_pids = (int*) malloc( num_processes* sizeof(int) );
  
  first_pid = getpid();

  num_processes = 1;
  
  for( i=0; i < num_processes; i++ )
  {
    if( getpid() == first_pid )
    {
      last_pid = fork();
      if( last_pid == 0 )
      {
        /* check if single or multi threaded */
        if( num_threads <= 1 )
        {
/*          printf( "process pid: %d\n", getpid() ); */
          bi_script_run( (void*) script );
        }
        else
        {
/*          printf( "process pid: %d\n", getpid() ); */
          bi_script_create_threads( script, num_threads );
        }
        
        exit(0); 
      }
      else if( last_pid < 0 )
      {
        /* the process could not be forked */
        exit(1);
      }
      else
      {
        /* collect the child pids */
        child_pids[i] = last_pid;
      }
    }
  }
 
  int status;
  
  /* wait until all childs have exited */
  for( j=0; j < num_processes; j++ )
  {
    waitpid( child_pids[j], &status, 0 );
  }
}

void bi_script_create_threads( char* script, int num_threads )
{
  int i,j;
  pthread_t thread_ids[ num_threads ];

/*    printf( "process pid in threadcaller: %d\n", getpid() ); */
  /* start the threads */
  for( i=0; i < num_threads; i++ )
  { 
    pthread_create( &thread_ids[i], NULL, &bi_script_run, script );
/*    printf( "created thread %d\n", thread_ids[i]); */
  }

  /* collect the threads */
  for( j=0; j < num_threads; j++ )
  {
/*    printf( "waiting for thread %d\n", thread_ids[j]); */
    pthread_join( thread_ids[j], NULL);
  }
}

void* bi_script_run( void* script )
{
  return (void*) system( (char*) script );
}

