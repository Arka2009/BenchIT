#include <stdio.h>

static inline void cpuid(unsigned long long *a, unsigned long long *b, unsigned long long *c, unsigned long long *d)
{
  unsigned long long reg_a,reg_b,reg_c,reg_d;
  
  __asm__ __volatile__(
          "cpuid;"
          : "=a" (reg_a), "=b" (reg_b), "=c" (reg_c), "=d" (reg_d)
          : "a" ((int)*a), "b" ((int)*b), "c" ((int)*c), "d" ((int)*d)
        );
  *a=(unsigned long long)reg_a;
  *b=(unsigned long long)reg_b;
  *c=(unsigned long long)reg_c;
  *d=(unsigned long long)reg_d;
}

int main(){
 unsigned long long a,b,c,d;
 
 a=5;
 cpuid(&a,&b,&c,&d);

 printf("%016llx, %016llx\n",a,b);

}
