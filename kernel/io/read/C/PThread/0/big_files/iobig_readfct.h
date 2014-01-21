/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: iobig_readfct.h 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://william@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/io/read/C/PThread/0/big_files/iobig_readfct.h $
 * For license details see COPYING in the package base directory
 *******************************************************************/

#ifndef iobig_readfct_h
#define iobig_readfct_h
char *makenumtopath(long num, long digits, char* filename);
void readfiles(long problemsize, long maxdeep, double *btime, double *etime);
#endif


