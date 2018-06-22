/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: simple.c 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/utilities/skeleton/C/0/0/intervallist/simple.c $
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* Kernel: simple Variant of the c-Skeleton with list PARAMETER
 *******************************************************************/
 
#include "simple.h"
#include "interface.h"

double simple( double * pd_prob_size )
{
  double dresult = 1.0;
  int ii = 0, pre = 0, prepre = 0, ij = 0, prob=(int)*pd_prob_size;
  
/*
  switch ( * pi_prob_size )
  {
    case 0:
            break;
    case 1:
            break;
    default:
            pre = *pi_prob_size - 1;
            prepre = pre - 1;
            dresult = (double) (simple(&pre) + simple(&prepre));
  }
*/
              
	ii=prob;
	ii = ii * ii;
	ij = ii * ii;
  for (ii=prob; ii>0; ii--)
  {
    dresult = dresult * ii;
    dresult = sqrt(dresult);
 		dresult = dresult * dresult;
 		dresult = dresult + dresult;
 		dresult = dresult - dresult;
		for (ij=prob; ij>0; ij--)
		  {
		    dresult = dresult * ii;		    
 		   dresult = sqrt(dresult);
 		   dresult = dresult * dresult;
 		   dresult = dresult + dresult;
 		   dresult = dresult - dresult;
  		}
  }


  return dresult;
}

