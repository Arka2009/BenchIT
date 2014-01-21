/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: work.c 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://william@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/numerical/gemv/C/SSE_Intrinsics/0/unaligned_m128/work.c $
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* Kernel: C SGEMV kernel (SSE, unaligned data)
 *******************************************************************/

#include <xmmintrin.h>
#include "work.h"

void sseunalignIJ_(int sizeVector,int sizeAusgabe,float alpha,float beta, float* x, float *A, float *y)
{
	//IDL(-1,printf("\tIJ:%i\n",sizeVector););
	int i,j,iXsize;
	// upper limit for j-loops
	int upperLimitJ=sizeAusgabe-sizeAusgabe%4;
	// upper limit for i-loops
	int upperLimitI=sizeVector-sizeVector%4;
	// xmm Register
	__m128 xmm_gamma,xmm_y,xmm_x,xmm_a0,xmm_a1,xmm_a2,xmm_a3;
	// load beta into all places of xmm_gamma
	xmm_gamma=_mm_load1_ps(&beta);
	// calculate y=beta*y parallel
	for (j=0;j<upperLimitJ;j=j+4)
	{
		xmm_y=_mm_loadu_ps(&y[j]);
		xmm_y=_mm_mul_ps(xmm_y,xmm_gamma);
		_mm_storeu_ps(&y[j],xmm_y);
	}
	// and maybe sequential (if the size of y is not a multiple of 2)
	for (j=upperLimitJ;j<sizeAusgabe;j++)
	{
		y[j]=beta*y[j];
	}
	//
	// now : x=x, A=A, y=beta*y
	//

	// load alpha into all places of xmm_gamma
	xmm_gamma=_mm_load1_ps(&alpha);


	for (i=0;i<upperLimitI;i=i+4)
	{
		//IDL(-1,printf("\t\ti:%i\n",i););
		// temporary variable for i*sizeAusgabe
		iXsize=i*sizeAusgabe;
		// load x[i] and x[i+1] (the next 2 entries for vector x)
		xmm_a0=_mm_loadu_ps(&x[i]);
		// multiply them with gamma
		xmm_a0=_mm_mul_ps(xmm_a0,xmm_gamma);
		xmm_a3=_mm_shuffle_ps(xmm_a0,xmm_a0,_MM_SHUFFLE(3,3,3,3));
		xmm_a2=_mm_shuffle_ps(xmm_a0,xmm_a0,_MM_SHUFFLE(2,2,2,2));
		// write gamma*x[i+1] into both sides of xmm_a1
		xmm_a1=_mm_shuffle_ps(xmm_a0,xmm_a0,_MM_SHUFFLE(1,1,1,1));
		// write gamma*x[i] into both sides of xmm_a0
		xmm_a0=_mm_shuffle_ps(xmm_a0,xmm_a0,_MM_SHUFFLE(0,0,0,0));
		// do for the two next elements of A
		for (j=0;j<upperLimitJ;j=j+4)
		{
			//IDL(-1,printf("\t\t\tj:%i\n",j););
			// load destination vector y
			xmm_y=_mm_loadu_ps(&y[j]);
			// load next 2 elements of A [i][j] and a[i][j+1]
			xmm_x=_mm_load_ps(&A[iXsize+j]);
			// multiply them with gamma*x[i]
			xmm_x=_mm_mul_ps(xmm_x,xmm_a0);
			// add y[  j  ] = y[  j  ] + A[  i  ][  j  ] * gamma * x[  i  ]
			//     y[ j+1 ] = y[ j+1 ] + A[  i  ][ j+1 ] * gamma * x[  i  ]
			xmm_y=_mm_add_ps(xmm_y,xmm_x);
			// load A [i+1][j] and A[i+1][j+1]
			xmm_x=_mm_loadu_ps(&A[((i+1)*(sizeAusgabe))+j]);
			// see above
			xmm_x=_mm_mul_ps(xmm_x,xmm_a1);
			xmm_y=_mm_add_ps(xmm_y,xmm_x);
			xmm_x=_mm_loadu_ps(&A[((i+2)*(sizeAusgabe))+j]);
			xmm_x=_mm_mul_ps(xmm_x,xmm_a2);
			xmm_y=_mm_add_ps(xmm_y,xmm_x);
			xmm_x=_mm_loadu_ps(&A[((i+3)*(sizeAusgabe))+j]);
			xmm_x=_mm_mul_ps(xmm_x,xmm_a3);
			xmm_y=_mm_add_ps(xmm_y,xmm_x);
			// store
			// y[j]=y[j]+A[i][j]*gamma*x[i]+A[i+1]*gamma*x[i]
			// y[j+1] equivalent
			_mm_storeu_ps(&y[j],xmm_y);
		}
		for (j=upperLimitJ;j<sizeAusgabe;j++)
		{
			//IDL(-1,printf("\t\t\tj:%i\n",j););
			y[j]=y[j]+alpha*(A[iXsize+j]*x[i]+A[((i+1)*sizeAusgabe)+j]*x[i+1]);
		}
	}
	for (i=upperLimitI;i<sizeVector;i++)
	{
		//IDL(-1,printf("\t\ti:%i\n",i););
		// temporary variable for i*sizeAusgabe
		iXsize=i*sizeAusgabe;
		// load x[i]
		xmm_a0=_mm_load1_ps(&x[i]);
		// multiply it with gamma
		xmm_a0=_mm_mul_ps(xmm_a0,xmm_gamma);
		for (j=0;j<upperLimitJ;j=j+4)
		{
			//IDL(-1,printf("\t\t\tj:%i\n",j););
			// load destination vector y
			xmm_y=_mm_loadu_ps(&y[j]);
			// load next 2 elements of A [i][j] and a[i][j+1]
			xmm_x=_mm_loadu_ps(&A[iXsize+j]);
			// multiply them with gamma*x[i]
			xmm_x=_mm_mul_ps(xmm_x,xmm_a0);
			// add y[  j  ] = y[  j  ] + A[  i  ][  j  ] * gamma * x[  i  ]
			//     y[ j+1 ] = y[ j+1 ] + A[  i  ][ j+1 ] * gamma * x[  i  ]
			xmm_y=_mm_add_ps(xmm_y,xmm_x);
			// store
			// y[j]=y[j]+A[i][j]*gamma*x[i]
			// y[j+1] equivalent
			_mm_storeu_ps(&y[j],xmm_y);
		}
		for (j=upperLimitJ;j<sizeAusgabe;j++)
		{
			//IDL(-1,printf("\t\t\tj:%i\n",j););
			y[j]=y[j]+alpha*(A[iXsize+j]*x[i]+A[((i+1)*sizeAusgabe)+j]*x[i+1]);
		}
	}
}

void sseunalignJI_(int sizeVector,int sizeAusgabe,float alpha,float beta, float* x, float *A, float *y)
{
	//IDL(-1,printf("\tJI:%i\n",sizeVector););
	int i,j,iXsize;
	// upper limit for j-loops
	int upperLimitJ=sizeAusgabe-sizeAusgabe%4;
	// upper limit for i-loops
	int upperLimitI=sizeVector-sizeVector%4;
	// xmm Register
	__m128 xmm_gamma,xmm_y,xmm_x,xmm_a0,xmm_a1,xmm_a2,xmm_a3;
	// load beta into all places of xmm_gamma
	xmm_gamma=_mm_load1_ps(&beta);
	// calculate y=beta*y parallel
	for (j=0;j<upperLimitJ;j=j+4)
	{
		xmm_y=_mm_load_ps(&y[j]);
		xmm_y=_mm_mul_ps(xmm_y,xmm_gamma);
		_mm_store_ps(&y[j],xmm_y);
	}
	// and maybe sequential (if the size of y is not a multiple of 2)
	for (j=upperLimitJ;j<sizeAusgabe;j++)
	{
		y[j]=beta*y[j];
	}
	//
	// now : x=x, A=A, y=beta*y
	//

	// load alpha into all places of xmm_gamma
	xmm_gamma=_mm_load1_ps(&alpha);


	// do for the two next elements of y
	for (j=0;j<upperLimitJ;j=j+4)
	{
		// load destination vector y
		xmm_y=_mm_loadu_ps(&y[j]);
		for (i=0;i<upperLimitI;i=i+4)
		{
			// temporary variable for i*sizeAusgabe
			iXsize=i*sizeAusgabe;
			// load x[i] and x[i+1] (the next 2 entries for vector x)
			xmm_a0=_mm_loadu_ps(&x[i]);
			// multiply them with gamma
			xmm_a0=_mm_mul_ps(xmm_a0,xmm_gamma);
			xmm_a3=_mm_shuffle_ps(xmm_a0,xmm_a0,_MM_SHUFFLE(3,3,3,3));
			xmm_a2=_mm_shuffle_ps(xmm_a0,xmm_a0,_MM_SHUFFLE(2,2,2,2));
			// write gamma*x[i+1] into both sides of xmm_a1
			xmm_a1=_mm_shuffle_ps(xmm_a0,xmm_a0,_MM_SHUFFLE(1,1,1,1));
			// write gamma*x[i] into both sides of xmm_a0
			xmm_a0=_mm_shuffle_ps(xmm_a0,xmm_a0,_MM_SHUFFLE(0,0,0,0));
			// load next 2 elements of A [i][j] and a[i][j+1]
			xmm_x=_mm_loadu_ps(&A[iXsize+j]);
			// multiply them with gamma*x[i]
			xmm_x=_mm_mul_ps(xmm_x,xmm_a0);
			// add y[  j  ] = y[  j  ] + A[  i  ][  j  ] * gamma * x[  i  ]
			//     y[ j+1 ] = y[ j+1 ] + A[  i  ][ j+1 ] * gamma * x[  i  ]
			xmm_y=_mm_add_ps(xmm_y,xmm_x);
			// load A [i+1][j] and A[i+1][j+1]
			xmm_x=_mm_loadu_ps(&A[((i+1)*(sizeAusgabe))+j]);
			// see above
			xmm_x=_mm_mul_ps(xmm_x,xmm_a1);
			xmm_y=_mm_add_ps(xmm_y,xmm_x);
			xmm_x=_mm_loadu_ps(&A[((i+2)*(sizeAusgabe))+j]);
			xmm_x=_mm_mul_ps(xmm_x,xmm_a2);
			xmm_y=_mm_add_ps(xmm_y,xmm_x);
			xmm_x=_mm_loadu_ps(&A[((i+3)*(sizeAusgabe))+j]);
			xmm_x=_mm_mul_ps(xmm_x,xmm_a3);
			xmm_y=_mm_add_ps(xmm_y,xmm_x);
		}
		for (i=upperLimitI;i<sizeVector;i++)
		{
			// temporary variable for i*sizeAusgabe
			iXsize=i*sizeAusgabe;
			// load x[i]
			xmm_a0=_mm_load1_ps(&x[i]);
			// multiply it with gamma
			xmm_a0=_mm_mul_ps(xmm_a0,xmm_gamma);
			// load next 2 elements of A [i][j] and a[i][j+1]
			xmm_x=_mm_loadu_ps(&A[iXsize+j]);
			// multiply them with gamma*x[i]
			xmm_x=_mm_mul_ps(xmm_x,xmm_a0);
			// add y[  j  ] = y[  j  ] + A[  i  ][  j  ] * gamma * x[  i  ]
			//     y[ j+1 ] = y[ j+1 ] + A[  i  ][ j+1 ] * gamma * x[  i  ]
			xmm_y=_mm_add_ps(xmm_y,xmm_x);
		}
		// store
		// y[j]=y[j]+A[i][j]*gamma*x[i]+A[i+1]*gamma*x[i]
		// y[j+1] equivalent
		_mm_storeu_ps(&y[j],xmm_y);
	}
	for (j=upperLimitJ;j<sizeAusgabe;j++)
	{
		for (i=0;i<sizeVector;i++)
		{
			y[j]=y[j]+alpha*A[i*sizeAusgabe+j]*x[i];
		}
	}
}

