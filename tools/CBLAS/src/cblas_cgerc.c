/*
 * cblas_cgerc.c
 * The program is a C interface to cgerc.
 * 
 * Keita Teranishi  5/20/98
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include "cblas.h"
#include "cblas_f77.h"
void cblas_cgerc(const enum CBLAS_ORDER order, const int M, const int N,
                 const void *alpha, const void *X, const int incX,
                 const void *Y, const int incY, void *A, const int lda)
{
#ifdef F77_INT
   F77_INT F77_M=M, F77_N=N, F77_lda=lda, F77_incX=incX, F77_incY=incY;
#else
   #define F77_M M
   #define F77_N N
   #define F77_incX incX
   #define F77_incY incy
   #define F77_lda lda   
#endif

   int n, i, tincy, incy=incY;
   float *y=(float *)Y, *yy=(float *)Y, *ty, *st;

   extern int CBLAS_CallFromC;
   extern int RowMajorStrg;
   RowMajorStrg = 0;

   CBLAS_CallFromC = 1;
   if (order == CblasColMajor)
   {
      F77_cgerc(&F77_M, &F77_N, alpha, X, &F77_incX, Y, &F77_incY, A, 
                      &F77_lda);
   }  else if (order == CblasRowMajor)   
   {
      RowMajorStrg = 1;
      if (N > 0)
      {
         n = N << 1;
         y = malloc(n*sizeof(float));

         ty = y;
         if(incY > 0) {
            i = incY << 1;
            tincy = 2;
            st= y+n;
         } else { 
            i = incY *(-2);
            tincy = -2;
            st = y-2; 
            y +=(n-2); 
         }
         do
         {
            *y = *yy;
            y[1] = -yy[1];
            y += tincy ;
            yy += i;
         }
         while (y != st);
         y = ty;

         #ifdef F77_INT
            F77_incY = 1;
         #else
            incy = 1;
         #endif
      }
      else y = (float *) Y;

      F77_cgeru(&F77_N, &F77_M, alpha, y, &F77_incY, X, &F77_incX, A, 
                      &F77_lda);
      if(Y!=y)
         free(y);

   } else cblas_xerbla(1, "cblas_cgerc", "Illegal Order setting, %d\n", order);
   CBLAS_CallFromC = 0;
   RowMajorStrg = 0;
   return;
}
