/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: stringlib.h 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/tools/stringlib.h $
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* For advanced string work, see c-file for more information.
 *******************************************************************/

/** @file stringlib.h
* @Brief For advanced string work, see c-file for more information.
*/
#ifndef STRINGLIB_H
#define STRINGLIB_H


#define STR_LEN 65536
/**
* Brief Commented functions under stringlibc.
*/
extern int compare( const char *, const char * );
extern int comparem( const char *, char * );
extern int comparec( char *, char * );
extern int escapeChar( const char *, char *, char );
extern int indexOf( const char *, char, int );
extern int lastIndexOf( const char *, char, int );
extern int length( const char * );
extern int lengthc( char * );
extern int substring( const char*, char*, int, int );
extern int trim( const char *, char * );
extern int trimChar( const char *, char *, char );

extern int min( int, int );

#endif

