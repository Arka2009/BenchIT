/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: bienvhash.h 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/tools/bienvhash.h $
 * For license details see COPYING in the package base directory
 *******************************************************************/
#ifndef BIENVHASH_H
#define BIENVHASH_H

#include "stringlib.h"
#include <stdio.h>
/** @file bienvhash.h
* @Brief For more information check bienvhash(template)c.
*/
/** Brief For more information check bienvhash(template)c.
*/

/** Dumps the table to stdout. */
extern void bi_dumpTable(void);
/** Dumps the table to our result file. */
extern void bi_dumpTableToFile( FILE ** );
/** Fills the table with predefined content. */
extern void bi_fillTable(void);
/** Retrieves a value from the table. If the given key
    does not exist a null pointer is returned. */
extern char *bi_get ( const char *, int * );
/** Creates the table and initializes the fileds. */
extern void bi_initTable(void);
/** Puts a Key-Value pair into the table. If the key
    already exists, the value will be overwritten.
    Returns 0, if the key is new, 1 if a value was
    overwritten. */
extern int bi_put( const char *, const char * );
/** Returns the number of entries stored in the table. */
extern int bi_size(void);
/** Adds variables from a PARAMETER file to the table. */
extern int bi_readParameterFile( const char * );

#endif

