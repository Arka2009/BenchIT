/** 
* @file x86.c
*  architecture specific part of the hardware detection for x86 architectures
*  Uses CPUID and RDTSC instructions if available
* currently only AMD and Intel CPUs are supported according to their CPUID specifications
* TODO other vendors
* 
* Author: Daniel Molka (daniel.molka@zih.tu-dresden.de)
*/
#include "cpu.h"
#include "x86.h"
#include <stdlib.h>
#include <unistd.h>
#include <math.h>
#include "properties.h"

//see cpu.h
#if defined (__ARCH_X86)

#if ((defined (__x86_64__))||(defined (__x86_64))||(defined (x86_64)))
    #define _64_BIT
#else
  #if ((defined (__i386__))||(defined (__i386))||(defined (i386))||(defined (__i486__))||(defined (__i486))||(defined (i486))||(defined (__i586__))||(defined (__i586))||(defined (i586))||(defined (__i686__))||(defined (__i686))||(defined (i686)))
    #define _32_BIT
  #endif
#endif

/** used to store Registers {R|E}AX, {R|E}BX, {R|E}CX and {R|E}DX */
static unsigned long long a,b,c,d;

/*
 * declarations of x86 specific functions, only used within this file
 */

/**
 * check if CPUID instruction is available
 */
static int has_cpuid();

/**
 * call CPUID instruction
 */
static void cpuid(unsigned long long *a, unsigned long long *b, unsigned long long *c, unsigned long long *d);

/**
 * check if package supports more than 1 (logical) CPU
 */
static int has_htt();

/** 64 Bit implementations  */
#if defined _64_BIT
static unsigned long long reg_a,reg_b,reg_c,reg_d;


static void cpuid(unsigned long long *a, unsigned long long *b, unsigned long long *c, unsigned long long *d)
{
  __asm__ __volatile__(
             "cpuid;"
           : "=a" (reg_a), "=b" (reg_b), "=c" (reg_c), "=d" (reg_d)
           : "a" (*a), "b" (*b), "c" (*c), "d" (*d)
     );
     *a=reg_a;
     *b=reg_b;
     *c=reg_c;
     *d=reg_d;
}

static int has_cpuid()
{
  // all 64 Bit x86 CPUs support CPUID
  return 1;
}

unsigned long long timestamp()
{
  if (!has_rdtsc()) return 0;
  __asm__ __volatile__("rdtsc;": "=a" (reg_a), "=d" (reg_d));
  return (reg_d<<32)|(reg_a&0xffffffffULL);
}

int get_rdtsc_latency()
{
   unsigned int latency=0xffffffff,i;
   double tmp;

   if (!has_rdtsc()) return -1;

   /*
   * Output : EDX:EAX stop timestamp
   *          ECX:EBX start timestamp
   */
   for(i=0;i<100;i++)
   {
     __asm__ __volatile__(
                //start timestamp
                "rdtsc;"
                "mov %%rax,%%rbx;"
                "mov %%rdx,%%rcx;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                //stop timestamp
                "rdtsc;"
                : "=a" (reg_a), "=b" (reg_b), "=c" (reg_c), "=d" (reg_d)
          );
    a=(reg_d<<32)+(reg_a&0xffffffffULL);
    b=(reg_c<<32)+(reg_b&0xffffffffULL);
    tmp=rint(((double)(a-b))/((double)257));
    if (tmp<latency) latency=(int)tmp;
  }
  return latency;
}

int get_virt_address_length()
{
  /* not checking if CPUID is available, as all known 64 Bit x86 CPUs support CPUID */
  a=0x80000000;
  cpuid(&a,&b,&c,&d);
  if (a>=0x80000008)
  {
    a=0x80000008;
    cpuid(&a,&b,&c,&d);
    return (a>>8)&0xff;
  }
  /* might be necessary for Netburst, later CPUs are expected to implement the cpuid function above, TODO Via?*/
  return 48;
}

int get_phys_address_length()
{
  /* not checking if CPUID is available, as all known 64 Bit x86 CPUs support CPUID */
  a=0x80000000;
  cpuid(&a,&b,&c,&d);
  if (a>=0x80000008)
  {
    a=0x80000008;
    cpuid(&a,&b,&c,&d);
    return a&0xff;
  }
  /* might be necessary for Netburst, later CPUs are expected to implement the cpuid function above TODO Via?*/
  return 36;
}

int num_pagesizes()
{
  int num=2; /* 4K pages and 2M pages supported by all 64 Bit x86 cpus */
  char tmp[16];
  if ((get_cpu_vendor(tmp,16)!=-1)&&(!strcmp(tmp,"AuthenticAMD")))
  {
    a=0x80000000;
    cpuid(&a,&b,&c,&d);
    if (a>=0x80000001)
    {
       a=0x80000001;
       cpuid(&a,&b,&c,&d);
       if (d&(1<<26)) num++; /* 1 GB pages */
    }
  }

  return num;
}

long long pagesize(int id)
{
  if (id>num_pagesizes()) return -1;

  if (id==0) return 4096;
  if (id==1) return 2097152;
  if (id==2) return 1073741824;
  
  return -1;
}

#endif

/** 32 Bit implementations */
#if defined(_32_BIT)
/* 32 Bit Registers */
static unsigned int reg_a,reg_b,reg_c,reg_d;

static void cpuid(unsigned long long *a, unsigned long long *b, unsigned long long *c, unsigned long long *d)
{
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

static int has_cpuid()
{
   int flags_old,flags_new;

   __asm__ __volatile__(
           "pushfl;"
           "popl %%eax;"
           : "=a" (flags_old)
   );

   flags_new=flags_old;
   if (flags_old&(1<<21)) flags_new&=0xffdfffff; else flags_new|=(1<<21);

   __asm__ __volatile__(
           "pushl %%eax;"
           "popfl;"
           "pushfl;"
           "popl %%eax;"
           : "=a" (flags_new)
           : "a" (flags_new)
   );

   // CPUID is supported if Bit 21 in the EFLAGS register can be changed
   if (flags_new==flags_old) return 0; 
   else 
   {
     __asm__ __volatile__(
         "pushl %%eax;"
         "popfl;"
         :
         : "a" (flags_old)
     );
     return 1;
   }
}

unsigned long long timestamp()
{
  if (!has_rdtsc()) return 0;
  __asm__ __volatile__("rdtsc;": "=a" (reg_a) , "=d" (reg_d));
  // upper 32 Bit in EDX, lower 32 Bit in EAX
  return (((unsigned long long)reg_d)<<32)+(reg_a&0xffffffffULL);
}

int get_rdtsc_latency()
{
   unsigned int latency=0xffffffff,i;
   double tmp;

   if (!has_rdtsc()) return -1;

   /*
   * Output : EDX:EAX stop timestamp
   *          ECX:EBX start timestamp
   */
   for(i=0;i<100;i++)
   {
     __asm__ __volatile__(
                //start timestamp
                "rdtsc;"
                "movl %%eax,%%ebx;"
                "movl %%edx,%%ecx;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                "rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;rdtsc;"
                //stop timestamp
                "rdtsc;"
                : "=a" (reg_a), "=b" (reg_b), "=c" (reg_c), "=d" (reg_d)
          );

    a=(((unsigned long long)reg_d)<<32)+reg_a;
    b=(((unsigned long long)reg_c)<<32)+reg_b;
    tmp=rint(((double)(a-b))/((double)257));
    if (tmp<latency) latency=(int)tmp;
  }
  return latency;
}

int get_virt_address_length()
{
  if (has_cpuid())
  {
    a=0x80000000;
    cpuid(&a,&b,&c,&d);
    if (a>=0x80000008)
    {
      a=0x80000008;
      cpuid(&a,&b,&c,&d);

      return (a>>8)&0xff;
    }
    return 32;
  }
  else return 32;
}

int get_phys_address_length()
{
  char tmp[16];

  if (has_cpuid())
  {
    a=0x80000000;
    cpuid(&a,&b,&c,&d);
    if (a>=0x80000008)
    {
      a=0x80000008;
      cpuid(&a,&b,&c,&d);

      return a&0xff;
    }
    a=0;
    cpuid(&a,&b,&c,&d);
    if (a>=1)
    {
      a=1;
      cpuid(&a,&b,&c,&d);

      if ((d&(1<<6))||(d&(1<<17))) /* PAE||PSE36*/
      {
         get_cpu_vendor(tmp, 13);

         /* K7 uses only 13! address lines, addresses are splitt in 3 parts. One Bit is used to decide if the remainder is a 12 Bit part
            of the actual address or if it is further devided. In the second case another Bit is used to identify one of the 2 11 Bit parts
            of the address */
         if ((!strcmp(tmp,"AuthenticAMD"))&&(get_cpu_family()==6)) return 34;
         else return 36;
         /* TODO Via? */
      }
    }
    return 32;
  }
  else return 32;
}

int num_pagesizes()
{
  int num=1; /* 4K pages supported, since 386 */

  if (has_cpuid())
  {
    a=0;
    cpuid(&a,&b,&c,&d);
    if (a>=1)
    {
      a=1;
      cpuid(&a,&b,&c,&d);

      /* TODO check if enabled */
      if (d&(1<<6)) num++; /* PAE -> 2M pages*/
      if (d&(1<<3)) num++; /* PSE -> 4M pages*/
    }
  }

  return num;
}

long long pagesize(int id)
{
  if (id>num_pagesizes()) return -1;

  if (id==0) return 4096;
  if ((id==1)&&(num_pagesizes()==3)) return 2097152;
  if ((id==1)&&(num_pagesizes()==2))
  {
    a=1;
    cpuid(&a,&b,&c,&d);

    /* TODO check if enabled */
    if (d&(1<<6)) return 2097152; /* PAE -> 2M pages*/
    if (d&(1<<3)) return 4194304; /* PSE -> 4M pages*/
  }
  if (id==2) return 4194304;
  return -1;
}

#endif

/**
 * shared implementations for 32 Bit and 64 Bit mode
 */

 /**
  * try to estimate ISA using compiler macros
  */
void get_architecture(char* arch, size_t len)
{
  #if ((defined (__i386__))||(defined (__i386))||(defined (i386)))
   strncpy(arch,"i386",len);
  #endif

  #if ((defined (__i486__))||(defined (__i486))||(defined (i486)))
   strncpy(arch,"i486",len);
  #endif

  #if ((defined (__i586__))||(defined (__i586))||(defined (i586)))
   strncpy(arch,"i586",len);
  #endif

  #if ((defined (__i686__))||(defined (__i686))||(defined (i686)))
   strncpy(arch,"i686",len);
  #endif

  #if ((defined (__x86_64__))||(defined (__x86_64))||(defined (x86_64)))
   strncpy(arch,"x86_64",len);
  #endif
}


int has_rdtsc()
{
  if (!has_cpuid()) return 0;

  a=0;
  cpuid(&a,&b,&c,&d);
  if (a>=1)
  {
    a=1;
    cpuid(&a,&b,&c,&d);
    if ((int)d&(1<<4)) return 1;
  }

  return 0;

}

int has_invariant_rdtsc()
{
   char tmp[_HW_DETECT_MAX_OUTPUT];
   int res=0;

   if ((has_rdtsc())&&(get_cpu_vendor((char*)&tmp[0],_HW_DETECT_MAX_OUTPUT)==0))
   {

     /* TSCs are usable if CPU supports only one frequency in C0 (no speedstep/Cool'n'Quite) 
        or if multiple frequencies are available and the constant/invariant TSC feature flag is set */
      
      if (!strcmp(&tmp[0],"GenuineIntel"))
      {
         /*check if Powermanagement and invariant TSC are supported*/
         if (has_cpuid())
         { 
           a=1;
           cpuid(&a,&b,&c,&d);
           /* no Frequency control */
           if ((!(d&(1<<22)))&&(!(c&(1<<7)))) res=1;
           a=0x80000000;
           cpuid(&a,&b,&c,&d);
           if (a >=0x80000007)
           {
              a=0x80000007;
              cpuid(&a,&b,&c,&d);
              /* invariant TSC */
              if (d&(1<<8)) res =1;
           }
         }
      }

      if (!strcmp(&tmp[0],"AuthenticAMD"))
      {
         /*check if Powermanagement and invariant TSC are supported*/
         if (has_cpuid())
         { 
           a=0x80000000;
           cpuid(&a,&b,&c,&d);
           if (a >=0x80000007)
           {
              a=0x80000007;
              cpuid(&a,&b,&c,&d);

              /* no Frequency control */
              if ((!(d&(1<<7)))&&(!(d&(1<<1)))) res=1;
              /* invariant TSC */
              if (d&(1<<8)) res =1;
           }
           /* assuming no frequency control if cpuid does not provide the extended function to test for it */
           else res=1;
         }
      }
   }

   return res;
}

static int has_htt()
{
  if (!has_cpuid()) return 0;
  a=0;
  cpuid(&a,&b,&c,&d);
  if (a>=1)
  {
    a=1;
    cpuid(&a,&b,&c,&d);
    if (d&(1<<28)) return 1;
  }
  return 0;
}

int get_cpu_vendor(char* vendor, size_t len)
{
  char tmp_vendor[13];

  if (!has_cpuid()) return generic_get_cpu_vendor(vendor,len);
  a=0;
  cpuid(&a,&b,&c,&d);
  *((unsigned int*)&(tmp_vendor[0]))=(int)b;
  *((unsigned int*)&(tmp_vendor[4]))=(int)d;
  *((unsigned int*)&(tmp_vendor[8]))=(int)c;
  tmp_vendor[12]='\0';

  strncpy(vendor,tmp_vendor,len);

  return 0;
}

int get_cpu_name(char* name, size_t len)
{
  char vendor[13];
  char tmp[48];
  char* start;

  if (!has_cpuid()) return generic_get_cpu_name(name,len);
  a=0x80000000;
  cpuid(&a,&b,&c,&d);
  /* read the name string returned by cpuid */
  if (a >=0x80000004)
  {
      a=0x80000002;
      cpuid(&a,&b,&c,&d);
      *((unsigned int*)&(tmp[0]))=(int)a;
      *((unsigned int*)&(tmp[4]))=(int)b;
      *((unsigned int*)&(tmp[8]))=(int)c;
      *((unsigned int*)&(tmp[12]))=(int)d;

      a=0x80000003;
      cpuid(&a,&b,&c,&d);
      *((unsigned int*)&(tmp[16]))=(int)a;
      *((unsigned int*)&(tmp[20]))=(int)b;
      *((unsigned int*)&(tmp[24]))=(int)c;
      *((unsigned int*)&(tmp[28]))=(int)d;

      a=0x80000004;
      cpuid(&a,&b,&c,&d);
      *((unsigned int*)&(tmp[32]))=(int)a;
      *((unsigned int*)&(tmp[36]))=(int)b;
      *((unsigned int*)&(tmp[40]))=(int)c;
      *((unsigned int*)&(tmp[44]))=(int)d;

      tmp[47]='\0';

      /* remove leading whitespace */
      start=&tmp[0];
      while (*start==' ') start++;

      if (len>48) len=48;
      memset(name,0,len);
      if (len>strlen(start)) len=strlen(start)+1;
      strncpy(name,start,len);

      return 0;
  }

  /* checking brand IDs of older Intel CPUs if brand strings are not supported*/
  a=0x0;
  cpuid(&a,&b,&c,&d);
  if (a < 0x00000001) return generic_get_cpu_name(name,len);
  vendor[12]='\0';
  if ((!get_cpu_vendor(vendor,13))&&(!strncmp(vendor,"GenuineIntel",13)))
  {
      a=0x1;
      cpuid(&a,&b,&c,&d);
      switch(b)
      {
         /* Pentium, Pentium Pro, Pentium II and early Pentium III do not even support the brand id*/
         case 0:
             if ((a&0xf00)==0x400) snprintf(name,len,"Intel(R) i486(TM) processor");return 0;
             if ((a&0xf00)==0x500) snprintf(name,len,"Intel(R) Pentium(R) processor");return 0;
             if ((a&0xff0)==0x610) snprintf(name,len,"Intel(R) Pentium(R) Pro processor");return 0;
             if ((a&0xff0)==0x630) snprintf(name,len,"Intel(R) Pentium(R) II processor");return 0;
             if ((a&0xff0)==0x650) snprintf(name,len,"Intel(R) Pentium(R) II processor");return 0;
             if ((a&0xff0)==0x660) snprintf(name,len,"Intel(R) Celeron(R) processor");return 0;
             if ((a&0xff0)==0x670) snprintf(name,len,"Intel(R) Pentium(R) III processor");return 0;
             /* model 8 and later should support brand string, just in case they don't...*/
             if ((a&0xff0)==0x680) snprintf(name,len,"Intel(R) Pentium(R) III processor");return 0;
             if ((a&0xff0)==0x690) snprintf(name,len,"Intel(R) Pentium(R) M processor");return 0;
             if ((a&0xff0)==0x6a0) snprintf(name,len,"Intel(R) Pentium(R) III Xeon processor");return 0;
             if ((a&0xff0)==0x6b0) snprintf(name,len,"Intel(R) Pentium(R) III processor");return 0;
         case 1:
            snprintf(name,len,"Intel(R) Celeron(R) processor");return 0;
         case 2:
            snprintf(name,len,"Intel(R) Pentium(R) III processor");return 0;
         case 3:
            if (a==0x6b1) snprintf(name,len,"Intel(R) Celeron(R) processor");
            else snprintf(name,len,"Intel(R) Pentium(R) III Xeon(TM) processor");
            return 0;
         case 4:
            snprintf(name,len,"Intel(R) Pentium(R) III processor");return 0;
         case 6:
            snprintf(name,len,"Mobile Intel(R) Pentium(R) III Processor-M");return 0;
         case 7:
            snprintf(name,len,"Mobile Intel(R) Celeron(R) processor");return 0;
         case 8:
            if (a>=0xf13) snprintf(name,len,"Intel(R) Genuine processor");
            else snprintf(name,len,"Intel(R) Pentium(R) 4 processor");
            return 0;
         case 9:
            snprintf(name,len,"Intel(R) Pentium(R) 4 processor");return 0;
         case 10:
            snprintf(name,len,"Intel(R) Celeron(R) Processor");return 0;
         case 11:
            if (a<0xf13) snprintf(name,len,"Intel(R) Xeon(TM) processor MP");
            else snprintf(name,len,"Intel(R) Xeon(TM) processor");
            return 0;
         case 12:
            snprintf(name,len,"Intel(R) Xeon(TM) processor MP");return 0;
         case 14:
            if (a<0xf13) snprintf(name,len,"Intel(R) Xeon(TM) processor");
            else snprintf(name,len,"Mobile Intel(R) Pentium(R) 4  processor-M");
            return 0;
         case 15:
            snprintf(name,len,"Mobile Intel(R) Celeron(R) processor");return 0;
         case 17:
            snprintf(name,len,"Mobile Genuine Intel(R) processor");return 0;
         case 18:
            snprintf(name,len,"Intel(R) Celeron(R) M processor");return 0;
         case 19:
            snprintf(name,len,"Mobile Intel(R) Celeron(R) processor");return 0;
         case 20:
            snprintf(name,len,"Intel(R) Celeron(R) Processor");return 0;
         case 21:
            snprintf(name,len,"Mobile Genuine Intel(R) processor");return 0;
         case 22:
            snprintf(name,len,"Intel(R) Pentium(R) M processor");return 0;
         case 23:
            snprintf(name,len,"Mobile Intel(R) Celeron(R) processor");return 0;
      }
      snprintf(name,len,"unknown Genuine Intel(R) processor");return 0;
  }

  /* name older AMD CPUs according to family and model, if brand string is not available */
  if ((!get_cpu_vendor(vendor,13))&&(!strncmp(vendor,"AuthenticAMD",13)))
  {
      a=0x1;
      cpuid(&a,&b,&c,&d);
      if ((a&0xf00)==0x400) snprintf(name,len,"AMD Am486(R) or Am5x86(R) processor");return 0;
      if ((a&0xff0)==0x500) snprintf(name,len,"AMD K5(R) processor");return 0;
      /* AMD K5 model 1 and later should support the brand string feature, just in case they don't... */
      if ((a&0xff0)==0x510) snprintf(name,len,"AMD K5(R) processor");return 0;
      if ((a&0xff0)==0x520) snprintf(name,len,"AMD K5(R) processor");return 0;
      if ((a&0xff0)==0x530) snprintf(name,len,"AMD K5(R) processor");return 0;
      if ((a&0xff0)==0x560) snprintf(name,len,"AMD K6(R) processor");return 0;
      if ((a&0xff0)==0x570) snprintf(name,len,"AMD K6(R) processor");return 0;
      if ((a&0xff0)==0x580) snprintf(name,len,"AMD K6-2(R) processor");return 0;
      if ((a&0xff0)==0x590) snprintf(name,len,"AMD K6-III(R) processor");return 0;
      snprintf(name,len,"unknown AuthenticAMD processor");return 0;
  }

  /* TODO other vendors*/

  return generic_get_cpu_name(name,len);
}

 int get_cpu_family()
 {
      if (!has_cpuid()) return generic_get_cpu_family();
      a=0;
      cpuid(&a,&b,&c,&d);
      if (a>=1)
      {
        a=1;
        cpuid(&a,&b,&c,&d);

        return (((int)a>>8)&0xf)+(((int)a>>20)&0xff);
      }
      return generic_get_cpu_family();
 }
 int get_cpu_model()
 {
      if (!has_cpuid()) return generic_get_cpu_model();
      a=0;
      cpuid(&a,&b,&c,&d);
      if (a>=1)
      {
        a=1;
        cpuid(&a,&b,&c,&d);

        return (((int)a>>4)&0xf)+(((int)a>>12)&0xf0);
      }
      return generic_get_cpu_model();
 }
 int get_cpu_stepping()
 {
      if (!has_cpuid()) return generic_get_cpu_stepping();
      a=0;
      cpuid(&a,&b,&c,&d);
      if (a>=1)
      {
        a=1;
        cpuid(&a,&b,&c,&d);

        return ((int)a&0xf);
      }
      return generic_get_cpu_stepping();
 }

 int get_cpu_isa_extensions(char* features, size_t len)
 {
   unsigned long long max,max_ext;
   char tmp[16];
   char output[32];
   int rdtsc_latency;

   if (!has_cpuid()) return generic_get_cpu_isa_extensions(features,len);

   memset(features,0,len);

   a=0;
   cpuid(&a,&b,&c,&d);
   max=a;

   a=0x80000000;
   cpuid(&a,&b,&c,&d);
   max_ext=a;

   get_cpu_vendor(tmp,sizeof(tmp));

   //identical on Intel an AMD (TODO other vendors)
   if ((!strcmp("AuthenticAMD",&tmp[0]))||(!strcmp("GenuineIntel",&tmp[0])))
   {
     if (max>=1)
     {
       a=1;
       cpuid(&a,&b,&c,&d);

       if (d&(1<<4)) strncat(features,"FPU ",(len-strlen(features))-1);
       /* supported by hardware, but not usable in 64 Bit Mode */
       #if defined _32_BIT
         if (d&(1<<3)) strncat(features,"PSE ",(len-strlen(features))-1);
         if (d&(1<<6)) strncat(features,"PAE ",(len-strlen(features))-1);
         if (d&(1<<17)) strncat(features,"PSE36 ",(len-strlen(features))-1);
       #endif
       if (d&(1<<23)) strncat(features,"MMX ",(len-strlen(features))-1);
       if (d&(1<<25)) strncat(features,"SSE ",(len-strlen(features))-1);
       if (d&(1<<26)) strncat(features,"SSE2 ",(len-strlen(features))-1);
       if (c&1) strncat(features,"SSE3 ",(len-strlen(features))-1);
       if (c&(1<<9)) strncat(features,"SSSE3 ",(len-strlen(features))-1);
       if (c&(1<<19)) strncat(features,"SSE4.1 ",(len-strlen(features))-1);
       if (c&(1<<20)) strncat(features,"SSE4.2 ",(len-strlen(features))-1);
       if (c&(1<<28)) strncat(features,"AVX ",(len-strlen(features))-1);
       if (c&(1<<12)) strncat(features,"FMA ",(len-strlen(features))-1);
       if (c&(1<<25)) strncat(features,"AES ",(len-strlen(features))-1);
       if (d&(1<<8)) strncat(features,"CX8 ",(len-strlen(features))-1);
       if (c&(1<<13)) strncat(features,"CX16 ",(len-strlen(features))-1);
       if (c&(1<<23)) strncat(features,"POPCNT ",(len-strlen(features))-1);
       if (d&(1<<19))
       {
         snprintf(output,sizeof(output),"CLFLUSH(%llu Byte lines) ",((b>>8)&0xff)*8);
         strncat(features,output,(len-strlen(features))-1);
       }
       if (d&(1<<4)) 
       {
         rdtsc_latency=get_rdtsc_latency();
         if (rdtsc_latency>0) snprintf(output,sizeof(output),"RDTSC(%i cycles latency) ",rdtsc_latency);
         else snprintf(output,sizeof(output),"RDTSC ");
         strncat(features,output,(len-strlen(features))-1);
       }
      if (c&(1<<3)) strncat(features,"MONITOR ",(len-strlen(features))-1);
      if (d&(1<<12)) strncat(features,"MTRR ",(len-strlen(features))-1);

     }

     if (max>=7)
     {
        a=7;c=0;
        cpuid(&a,&b,&c,&d);
             
        if (b&(1<<5))  strncat(features,"AVX2 ", (len-strlen(features))-1);
        if (b&(1<<16)) strncat(features,"AVX512 ", (len-strlen(features))-1);
     }

     if (max_ext>=0x80000001)
     {
       a=0x80000001;
       cpuid(&a,&b,&c,&d);

       if (d&(1<<20)) strncat(features,"NX ",(len-strlen(features))-1);
       #if defined _64_BIT
         if (d&(1<<29)) strncat(features,"X86_64 ",(len-strlen(features))-1);
       #endif
     }

     if (max>=6)
     {
       a=6;
       cpuid(&a,&b,&c,&d);
       if (c&(1)) strncat(features,"APERF/MPERF ",(len-strlen(features))-1);
     }
   }
   if (has_cpuid()) strncat(features,"CPUID ",(len-strlen(features))-1);
   //AMD specific
   if (!strcmp("AuthenticAMD",&tmp[0]))
   {
     if (max_ext>=0x80000001)
     {
       a=0x80000001;
       cpuid(&a,&b,&c,&d);

       if (d&(1<<31)) strncat(features,"3DNow ",(len-strlen(features))-1);
       if (d&(1<<30)) strncat(features,"3DNow_EXT ",(len-strlen(features))-1);
       if (d&(1<<22)) strncat(features,"MMX_EXT ",(len-strlen(features))-1);
       if (c&(1<<16)) strncat(features,"FMA4 ",(len-strlen(features))-1);
       if (c&(1<<15)) strncat(features,"LWP ",(len-strlen(features))-1);
       if (c&(1<<6)) strncat(features,"SSE4A ",(len-strlen(features))-1);
       if (c&(1<<5)) strncat(features,"ABM ",(len-strlen(features))-1);
       if (c&(1<<2))
       {
         strncat(features,"SVM",(len-strlen(features))-1);
         if (max_ext>=0x8000000a)
         {
           a=0x8000000a;
           cpuid(&a,&b,&c,&d);
           snprintf(output,sizeof(output),"(rev. %llu) ",a&0xff);
           strncat(features,output,(len-strlen(features))-1);
         }
         else strncat(features," ",(len-strlen(features))-1);
       }
     }

     if (max_ext>=0x80000007)
     {
       a=0x80000007;
       cpuid(&a,&b,&c,&d);

       if ((d&(1<<7))||(d&(1<<1)))
       {
          /* cpu supports frequency scaling
             NOTE this is not included into the feature list, as it can't be determined with cpuid if it is actually used
                  instead sysfs is used to determine scaling policy */
       }
     }
     /*if (max_ext>=0x8000000a)
     {
       a=0x8000000a;
       cpuid(&a,&b,&c,&d);

       // Hardware assisted paging (Nested Paging in AMD Terms)
       if (d&1) strncat(features,"HAP ",(len-strlen(features))-1);
     }*/
   }
   //Intel specific
   if (!strcmp("GenuineIntel",&tmp[0]))
   {
     if (max>=1)
     {
       a=1;
       cpuid(&a,&b,&c,&d);
       if (c&(1<<9))
       {
          /* cpu supports frequency scaling
             NOTE this is not included into the feature list, as it can't be determined with cpuid if it is actually used
                  instead sysfs is used to determine scaling policy */
       }
       if (c&(1<<5)) strncat(features,"VMX ",(len-strlen(features))-1); /* TODO revision */
     }
   }
   //TODO other vendors
   if ((strcmp("AuthenticAMD",&tmp[0]))&&(strcmp("GenuineIntel",&tmp[0]))) return generic_get_cpu_isa_extensions(features,len);

   if (num_threads_per_core()>1) strncat(features,"SMT ",(len-strlen(features))-1);

   return 0;
 }

 int get_cpu_lwp(char* lwpfeatures, size_t len)
  {
    char tmp[16];

    if (!has_cpuid()) return generic_get_cpu_lwp(lwpfeatures,len);

    memset(lwpfeatures,0,len);

    a=0;
    cpuid(&a,&b,&c,&d);

    a=0x80000000;
    cpuid(&a,&b,&c,&d);

    get_cpu_vendor(tmp,sizeof(tmp));
    //AMD LWP
    if (!strcmp("AuthenticAMD",&tmp[0]))
    {
		a=0x80000001;
		cpuid(&a,&b,&c,&d);
		if (c&(1<<15)) {
			a=0x8000001C;
			cpuid(&a,&b,&c,&d);
			if (a&(1<<0)){ //EAX: Supported by OS and HW
				strncat(lwpfeatures,"\n   - by OS and HW: ",(len-strlen(lwpfeatures))-1);
				if (a&(1<<1)) strncat(lwpfeatures,"\n     - LwpVAL: LWPVAL instruction (EventId = 1) is available.",(len-strlen(lwpfeatures))-1);
				if (a&(1<<2)) strncat(lwpfeatures,"\n     - LwpIRE: Instructions retired event (EventId = 2) is available.",(len-strlen(lwpfeatures))-1);
				if (a&(1<<3)) strncat(lwpfeatures,"\n     - LwpBRE: Branch retired event (EventId = 3) is available.",(len-strlen(lwpfeatures))-1);
				if (a&(1<<4)) strncat(lwpfeatures,"\n     - LwpDME: DCache miss event (EventId = 4) is available.",(len-strlen(lwpfeatures))-1);
				if (a&(1<<5)) strncat(lwpfeatures,"\n     - LwpCNH: CPU clocks not halted event (EventId = 5) is available.",(len-strlen(lwpfeatures))-1);
				if (a&(1<<6)) strncat(lwpfeatures,"\n     - LwpRNH: CPU reference clocks not halted event (EventId = 6) is available.",(len-strlen(lwpfeatures))-1);
				if (a&(1<<31)) strncat(lwpfeatures,"\n     - LwpInt: Interrupt on threshold overflow is available.",(len-strlen(lwpfeatures))-1);
			}
			if (d&(1<<0)){ //EDX: Supported by HW
				strncat(lwpfeatures,"\n   - only by HW: ",(len-strlen(lwpfeatures))-1);
				if (d&(1<<1)) strncat(lwpfeatures,"\n     - LwpVAL: LWPVAL instruction (EventId = 1) is available.",(len-strlen(lwpfeatures))-1);
				if (d&(1<<2)) strncat(lwpfeatures,"\n     - LwpIRE: Instructions retired event (EventId = 2) is available.",(len-strlen(lwpfeatures))-1);
				if (d&(1<<3)) strncat(lwpfeatures,"\n     - LwpBRE: Branch retired event (EventId = 3) is available.",(len-strlen(lwpfeatures))-1);
				if (d&(1<<4)) strncat(lwpfeatures,"\n     - LwpDME: DCache miss event (EventId = 4) is available.",(len-strlen(lwpfeatures))-1);
				if (d&(1<<5)) strncat(lwpfeatures,"\n     - LwpCNH: CPU clocks not halted event (EventId = 5) is available.",(len-strlen(lwpfeatures))-1);
				if (d&(1<<6)) strncat(lwpfeatures,"\n     - LwpRNH: CPU reference clocks not halted event (EventId = 6) is available.",(len-strlen(lwpfeatures))-1);
				if (d&(1<<31)) strncat(lwpfeatures,"\n     - LwpInt: Interrupt on threshold overflow is available.",(len-strlen(lwpfeatures))-1);
			}
		}
		else strncat(lwpfeatures,"n/a",(len-strlen(lwpfeatures))-1);
    }
    else strncat(lwpfeatures,"n/a",(len-strlen(lwpfeatures))-1);

    return 0;
  }


/**
 * measures clockrate using the Time-Stamp-Counter
 * @param check if set to 1 only constant TSCs will be used (i.e. power management independent TSCs)
 *              if set to 0 non constant TSCs are allowed (e.g. AMD K8)
 * @param cpu the cpu that should be used, only relevant for the fallback to generic functions
 *            if TSC is available and check is passed or deactivated then it is assumed thet the affinity
 *            has already being set to the desired cpu
 * @return frequency in highest P-State, 0 if no invariant TSC is available
 */
unsigned long long get_cpu_clockrate(int check,int cpu)
{
   unsigned long long start1_tsc,start2_tsc,end1_tsc,end2_tsc;
   unsigned long long start_time,end_time;
   unsigned long long clock_lower_bound,clock_upper_bound,clock;
   unsigned long long clockrate=0;
   int i,num_measurements=0,min_measurements;
   char tmp[_HW_DETECT_MAX_OUTPUT];
   struct timeval ts;

   if (check) 
   {
     /* non invariant TSCs can be used if CPUs run at fixed frequency */
     scaling_governor(-1, tmp, _HW_DETECT_MAX_OUTPUT);
     if (!has_invariant_rdtsc()&&(strcmp(tmp,"performance"))&&(strcmp(tmp,"powersave"))) return generic_get_cpu_clockrate(check,cpu);
     min_measurements=5;
   }
   else min_measurements=20;

   if (!has_rdtsc()) return generic_get_cpu_clockrate(check,cpu);
   
   i=3;
   do
   {
      //start timestamp
      start1_tsc=timestamp();
      gettimeofday(&ts,NULL);
      start2_tsc=timestamp();

      start_time=ts.tv_sec*1000000+ts.tv_usec;

      //waiting
      if (check) usleep(1000*i);    /* sleep */
      else do {end1_tsc=timestamp();} while (end1_tsc<start2_tsc+1000000*i); /* busy waiting */

      //end timestamp
      end1_tsc=timestamp();
      gettimeofday(&ts,NULL);
      end2_tsc=timestamp();

      end_time=ts.tv_sec*1000000+ts.tv_usec;

      clock_lower_bound=(((end1_tsc-start2_tsc)*1000000)/(end_time-start_time));
      clock_upper_bound=(((end2_tsc-start1_tsc)*1000000)/(end_time-start_time));

      // if both values differ significantly, the measurement could have been interrupted between 2 rdtsc's
      if (((double)clock_lower_bound>(((double)clock_upper_bound)*0.999))&&((end_time-start_time)>2000))
      {
        num_measurements++;
        clock=(clock_lower_bound+clock_upper_bound)/2;
        if(clockrate==0) clockrate=clock;
        else if ((check)&&(clock<clockrate)) clockrate=clock;
        else if ((!check)&&(clock>clockrate)) clockrate=clock; 
      }
      i+=2;
    }
    while (((end_time-start_time)<10000)||(num_measurements<min_measurements));

   return clockrate;
}
/**
 * number of caches (of one cpu)
 * @param cpu the cpu that should be used, only relevant for the fallback to generic functions
 *            if cpuid is available it is assumed that the affinity has already been set to the desired cpu
 */
int num_caches(int cpu)
{
  unsigned long long max,max_ext;
  char tmp[16];
  int num;

  if (!has_cpuid()) return generic_num_caches(cpu);

  a=0;
  cpuid(&a,&b,&c,&d);
  max=a;

  a=0x80000000;
  cpuid(&a,&b,&c,&d);
  max_ext=a;

  get_cpu_vendor(&tmp[0],16);

  //AMD specific
  if (!strcmp("AuthenticAMD",&tmp[0]))
  {
    if (max_ext<0x80000006) return generic_num_caches(cpu);

    a=0x80000006;
    cpuid(&a,&b,&c,&d);

    if (((c>>16)==0)||(((c>>12)&0xf)==0)) return 2; /* only L1I and L1D */
    else if (((d>>18)==0)||(((d>>12)&0xf)==0)) return 3; /* L1I, L1D, and L2 */
    else return 4; /* L1I, L1D, L2, and L3 */
  }

  //Intel specific
  if (!strcmp("GenuineIntel",&tmp[0]))
  {
    num=0;
    if (max>=0x00000004)
    {
      do
      {
         a=0x00000004;c=(unsigned long long)num;
         cpuid(&a,&b,&c,&d);

         num++;
       }
       while (a&0x1f);
    }
    else if (max>=0x00000002)
    {
      //TODO use function 02h if 04h is not supported
      return generic_num_caches(cpu);
    }

    return num-1;
  }

  //TODO other vendors

  return generic_num_caches(cpu);
}

/**
 * information about the cache: level, associativity...
 * @param cpu the cpu that should be used, only relevant for the fallback to generic functions
 *            if cpuid is available it is assumed that the affinity has already been set to the desired cpu
 * @param id id of the cache 0 <= id <= num_caches()-1
 * @param output preallocated buffer for the result string
 */
//TODO use sysfs if available to determine cache sharing
int cache_info(int cpu,int id, char* output, size_t len)
{
  unsigned long long max,max_ext;
  char tmp[16];

  int num;

  int size,assoc,linesize,shared,level;

  if (!has_cpuid()) return generic_cache_info(cpu,id,output,len);

  if ((num_caches(cpu)!=-1)&&(id>=num_caches(cpu))) return -1;

  memset(output,0,len);

  a=0;
  cpuid(&a,&b,&c,&d);
  max=a;

  a=0x80000000;
  cpuid(&a,&b,&c,&d);
  max_ext=a;

  get_cpu_vendor(&tmp[0],16);

  //AMD specific
  if ((!strcmp("AuthenticAMD",&tmp[0]))&&(max_ext>=0x80000005))
  {
    if (id==1)
    {
      a=0x80000005;
      cpuid(&a,&b,&c,&d);

      size=(d>>24);
      assoc=(d>>16)&0xff;
      linesize=d&0xff;
      shared=1;
      
      /* Bulldozer reports L1I to be per core not per module */ 
      if (get_cpu_family()==21) {
        shared=2;
      }  

      if (assoc==0) return -1;
      if (shared==1) {
        if (assoc==0x1)
          snprintf(output,len,"Level 1 Instruction Cache: %i KiB, direct mapped, %i Byte cachelines, per cpu",size,linesize);
        else if (assoc==0xff)
          snprintf(output,len,"Level 1 Instruction Cache: %i KiB, fully associative, %i Byte cachelines, per cpu",size,linesize);
        else 
          snprintf(output,len,"Level 1 Instruction Cache: %i KiB, %i-way set associative, %i Byte cachelines, per cpu",size,assoc,linesize);
      }
      else {
        if (assoc==0x1)
          snprintf(output,len,"Level 1 Instruction Cache: %i KiB, direct mapped, %i Byte cachelines, shared among %i cpus",size,linesize,shared);
        else if (assoc==0xff)
          snprintf(output,len,"Level 1 Instruction Cache: %i KiB, fully associative, %i Byte cachelines, shared among %i cpus",size,linesize,shared);
        else 
          snprintf(output,len,"Level 1 Instruction Cache: %i KiB, %i-way set associative, %i Byte cachelines, shared among %i cpus",size,assoc,linesize,shared);      
      }

      return 0;
    }
    if (id==0)
    { 
      a=0x80000005;
      cpuid(&a,&b,&c,&d);

      size=(c>>24);
      assoc=(c>>16)&0xff;
      linesize=c&0xff;

      if (assoc==0) return -1;
      else if (assoc==0x1)
        snprintf(output,len,"Level 1 Data Cache: %i KiB, direct mapped, %i Byte cachelines, per cpu",size,linesize);
      else if (assoc==0xff)
        snprintf(output,len,"Level 1 Date Cache: %i KiB, fully associative, %i Byte cachelines, per cpu",size,linesize);
      else 
        snprintf(output,len,"Level 1 Data Cache: %i KiB, %i-way set associative, %i Byte cachelines, per cpu",size,assoc,linesize);

      return 0;
    }
  }
  //AMD specific
  if ((!strcmp("AuthenticAMD",&tmp[0]))&&(max_ext>=0x80000006))
  {
    if (id==2)
    { 
      a=0x80000006;
      cpuid(&a,&b,&c,&d);

      size=(c>>16);
      assoc=(c>>12)&0xf;
      linesize=c&0xff;
      shared=1;

       switch (assoc)
       {
           case 0x0: size=0;assoc=0;break; /* disabled */
           case 0x6: assoc=8;break;
           case 0x8: assoc=16;break;
           case 0xa: assoc=32;break;
           case 0xb: assoc=48;break;
           case 0xc: assoc=64;break;
           case 0xd: assoc=96;break;
           case 0xe: assoc=128;break;
       }

      /* Bulldozer reports L2 to be per core not per module */ 
      if ((get_cpu_family()==21)) {
            shared=2;
      }

      if (assoc==0)
       snprintf(output,len,"L2 Cache disabled");
      else if (shared == 1) {
      if (assoc==0x1)
        snprintf(output,len,"Unified Level 2 Cache: %i KiB, direct mapped, %i Byte cachelines, per cpu",size,linesize);
      else if (assoc==0xf)
        snprintf(output,len,"Unified Level 2 Cache: %i KiB, fully associative, %i Byte cachelines, per cpu",size,linesize);
      else 
        snprintf(output,len,"Unified Level 2 Cache: %i KiB, %i-way set associative, %i Byte cachelines, per cpu",size,assoc,linesize);
      }
      else {
      if (assoc==0x1)
        snprintf(output,len,"Unified Level 2 Cache: %i KiB, direct mapped, %i Byte cachelines, shared among %i cpus",size,linesize,shared);
      else if (assoc==0xf)
        snprintf(output,len,"Unified Level 2 Cache: %i KiB, fully associative, %i Byte cachelines, shared among %i cpus",size,linesize,shared);
      else 
        snprintf(output,len,"Unified Level 2 Cache: %i KiB, %i-way set associative, %i Byte cachelines, shared among %i cpus",size,assoc,linesize,shared);      
      }

      return 0;
    }
    if (id==3)
    { 
      a=0x80000006;
      cpuid(&a,&b,&c,&d);

      size=(d>>18)*512;
      assoc=(d>>12)&0xf;
      linesize=d&0xff;
      shared=num_cores_per_package();

      switch (assoc)
      {
          case 0x0: size=0;assoc=0;break; /* disabled */
          case 0x6: assoc=8;break;
          case 0x8: assoc=16;break;
          case 0xa: assoc=32;break;
          case 0xb: assoc=48;break;
          case 0xc: assoc=64;break;
          case 0xd: assoc=96;break;
          case 0xe: assoc=128;break;
      }

      /* Magny Cours and Interlagos MCMs report L3 per package, return half the size and num cores to get info per die */
      if ( ( (get_cpu_family()==16)&&(get_cpu_model()==9) ) || ( (get_cpu_family()==21)&&(get_cpu_model()==1) ) ) {
        shared=shared>>1;
        if ((assoc!=0xf)&&(assoc!=0x1)) assoc=assoc>>1;
        size=size>>1;
      }

      if (assoc==0)
       snprintf(output,len,"L3 Cache disabled");
      else if (assoc==0x1)
        snprintf(output,len,"Unified Level 3 Cache: %i KiB, direct mapped, %i Byte cachelines, shared among %i cpus",size,linesize,shared);
      else if (assoc==0xf)
        snprintf(output,len,"Unified Level 3 Cache: %i KiB, fully associative, %i Byte cachelines, shared among %i cpus",size,linesize,shared);
      else 
        snprintf(output,len,"Unified Level 3 Cache: %i KiB, %i-way set associative, %i Byte cachelines, shared among %i cpus",size,assoc,linesize,shared);

      return 0;
    }
  }

  //Intel specific
  if (!strcmp("GenuineIntel",&tmp[0]))
  {
    if ((get_cpu_family()==15)&&(max>=0x00000002)) id--;
    if (id==-1)
    {
      int descriptors[15];
      int i,j,iter;

      a=0x00000002;
      cpuid(&a,&b,&c,&d);

      iter=(a&0xff);

      for (i=0;i<iter;i++)
      {
        size=0;

        a=0x00000002;
        cpuid(&a,&b,&c,&d);

        if (!(a&0x80000000))
        {
          descriptors[0]=(a>>8)&0xff;
          descriptors[1]=(a>>16)&0xff;
          descriptors[2]=(a>>24)&0xff;
        }
        else
        {
          descriptors[0]=0;
          descriptors[1]=0;
          descriptors[2]=0;
        }

        for (j=1;j<4;j++) descriptors[j-1]=(a>>(8*j))&0xff;
        for (j=0;j<4;j++)
        {
          if (!(b&0x80000000)) descriptors[j+3]=(b>>(8*j))&0xff;
          else  descriptors[j+3]=0;
          if (!(c&0x80000000)) descriptors[j+7]=(c>>(8*j))&0xff;
          else  descriptors[j+7]=0;
          if (!(d&0x80000000)) descriptors[j+11]=(d>>(8*j))&0xff;
          else  descriptors[j+11]=0;
        }
        for (j=0;j<15;j++)
        {
            switch(descriptors[j])
            {
                case 0x00: break;
                case 0x70: size=12;assoc=8; break;
                case 0x71: size=16;assoc=8; break;
                case 0x72: size=32;assoc=8; break;
                case 0x73: size=64;assoc=8; break;
            }
            if(size)
            {
              shared=num_threads_per_core();
              if (shared>1)
                snprintf(output,len,"Level 1 Instruction Trace Cache: %i K Microops, %i-way set associative, shared among %i cpus",size,assoc,shared);
              else
               snprintf(output,len,"Level 1 Instruction Trace Cache: %i K Microops, %i-way set associative, per cpu",size,assoc);
            }
        }

      }
    }
    else if (max>=0x00000004)
    {
      int type;
      num=0;
      do
      {
         a=0x00000004;c=(unsigned long long)num;
         cpuid(&a,&b,&c,&d);
         num++;
       }
       while (num<=id);

       level=((a&0xe0)>>5);
       shared=((a&0x03ffc000)>>14)+1;
       linesize=((b&0x0fff)+1);
       size=((((b&0xffc00000)>>22)+1)*(((b&0x3ff000)>>12)+1)*((b&0x0fff)+1)*(c+1))/1024;
       if (a&0x200) assoc=0; else assoc=((b&0xffc00000)>>22)+1;
       type=(a&0x1f);

       /* Hyperthreading, Netburst*/
       if (get_cpu_family()==15) shared=num_threads_per_core();
       /* Hyperthreading, Nehalem/Atom */
       /* TODO check if there are any models that do not work with that */
       if ((get_cpu_family()==6)&&(get_cpu_model()>=26))
       {
         if (level<3) shared=num_threads_per_core();
         if (level==3) shared=num_threads_per_package();
       }

       if (type==2)
       {
          if (assoc)
          {
            if (shared>1) snprintf(output,len,"Level %i Instruction Cache: %i KiB, %i-way set associative, %i Byte cachelines, shared among %i cpus",level,size,assoc,linesize,shared); 
            else snprintf(output,len,"Level %i Instruction Cache: %i KiB, %i-way set associative, %i Byte cachelines, per cpu",level,size,assoc,linesize);
          }
          else
          {
            if (shared>1) snprintf(output,len,"Level %i Instruction Cache: %i KiB, fully associative, %i Byte cachelines, shared among %i cpus",level,size,linesize,shared); 
            else snprintf(output,len,"Level %i Instruction Cache: %i KiB, fully associative, %i Byte cachelines, per cpu",level,size,linesize);
          }
       }
       if (type==1)
       {
          if (assoc)
          {
            if (shared>1) snprintf(output,len,"Level %i Data Cache: %i KiB, %i-way set associative, %i Byte cachelines, shared among %i cpus",level,size,assoc,linesize,shared); 
            else snprintf(output,len,"Level %i Date Cache: %i KiB, %i-way set associative, %i Byte cachelines, per cpu",level,size,assoc,linesize);
          }
          else
          {
            if (shared>1) snprintf(output,len,"Level %i Data Cache: %i KiB, fully associative, %i Byte cachelines, shared among %i cpus",level,size,linesize,shared); 
            else snprintf(output,len,"Level %i Data Cache: %i KiB, fully associative, %i Byte cachelines, per cpu",level,size,linesize);
          }
       }
       if (type==3)
       {
          if (assoc)
          {
            if (shared>1) snprintf(output,len,"Unified Level %i Cache: %i KiB, %i-way set associative, %i Byte cachelines, shared among %i cpus",level,size,assoc,linesize,shared); 
            else snprintf(output,len,"Unified Level %i Cache: %i KiB, %i-way set associative, %i Byte cachelines, per cpu",level,size,assoc,linesize);
          }
          else
          {
            if (shared>1) snprintf(output,len,"Unified Level %i Cache: %i KiB, fully associative, %i Byte cachelines, shared among %i cpus",level,size,linesize,shared); 
            else snprintf(output,len,"Unified Level %i Cache: %i KiB, fully associative, %i Byte cachelines, per cpu",level,size,linesize);
          }
       }
    }
    else if (max>=0x00000002)
    {
      //TODO use function 02h if 04h is not supported
      return generic_cache_info(cpu,id,output,len);
    }

    return 0;
  }
  //TODO other vendors

  return generic_cache_info(cpu,id,output,len);
}

 int cache_level(int cpu, int id) {
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;

   cache_info(cpu,id,tmp,sizeof(tmp));
   beg=strstr(tmp,"Level");
   if (beg==NULL) return generic_cache_level(cpu,id);
   else beg+=6;
   end=strstr(beg," ");
   if (end!=NULL)*end='\0';

   return atoi(beg);   
 }
 unsigned long long cache_size(int cpu, int id){
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;

   cache_info(cpu,id,tmp,sizeof(tmp));
   beg=strstr(tmp,":");
   if (beg==NULL) return generic_cache_size(cpu,id);
   else beg+=2;
   end=strstr(beg,",");
   if (end!=NULL) *end='\0';
   end=strstr(beg,"KiB");
   if (end!=NULL)
   {
     end--;
     *end='\0';
     return atoi(beg)*1024; 
   }
   end=strstr(beg,"MiB");
   if (end!=NULL)
   {
     end--;
     *end='\0';
     return atoi(beg)*1024*1024; 
   }

   return generic_cache_size(cpu,id);
 }
 unsigned int cache_assoc(int cpu, int id){
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;

   cache_info(cpu,id,tmp,sizeof(tmp));
   beg=strstr(tmp,":")+1;
   if (beg==NULL) return generic_cache_assoc(cpu,id);
   else beg++;
   end=strstr(beg,",")+1;
   if (end==NULL) return generic_cache_assoc(cpu,id);
   else end++;
   beg=end;
   end=strstr(beg,",");
   if (end!=NULL) *end='\0';
   end=strstr(tmp,"-way");
   if (end!=NULL) {
     *end='\0';
     return atoi(beg);
   }
   end=strstr(tmp,"fully");
   if (end!=NULL) {
     *end='\0';
     return FULLY_ASSOCIATIVE;
   }
   return generic_cache_assoc(cpu,id);
 }
 int cache_type(int cpu, int id) {
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;

   cache_info(cpu,id,tmp,sizeof(tmp));
   beg=tmp;
   end=strstr(beg,",");
   if (end!=NULL)*end='\0';
   else return generic_cache_type(cpu,id);

   if (strstr(beg,"Unified")!=NULL) return UNIFIED_CACHE;
   if (strstr(beg,"Trace")!=NULL) return INSTRUCTION_TRACE_CACHE;
   if (strstr(beg,"Data")!=NULL) return DATA_CACHE;
   if (strstr(beg,"Instruction")!=NULL) return INSTRUCTION_CACHE;

   return generic_cache_type(cpu,id);
 }
 int cache_shared(int cpu, int id){
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;

   cache_info(cpu,id,tmp,sizeof(tmp));
   beg=strstr(tmp,"among");
   if (beg==NULL) 
   {
     beg=strstr(tmp,"per cpu");
     if (beg!=NULL) return 1;
     else return generic_cache_shared(cpu,id);
   }
   beg+=6;
   end=strstr(beg,"cpus");
   if (end!=NULL)*(end--)='\0';

   return atoi(beg);
 }
 int cacheline_length(int cpu, int id){
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;

   cache_info(cpu,id,tmp,sizeof(tmp));
   beg=strstr(tmp,":")+1;
   if (beg==NULL) return generic_cacheline_length(cpu,id);
   else beg++;
   end=strstr(beg,",")+1;
   if (end==NULL) return generic_cacheline_length(cpu,id);
   else end++;
   beg=end;
   end=strstr(beg,",")+1;
   if (end==NULL) return generic_cacheline_length(cpu,id);
   else end++;
   beg=end;
   end=strstr(beg,"Byte cachelines");
   if (end!=NULL) *(end--)='\0';

   return atoi(beg);
}

int num_tlbs(int cpu)
{
  char tmp[16];
  int num=0;

  if (get_cpu_vendor(tmp,16)==-1) return generic_num_tlbs(cpu);
  /* AMD specific */
  if (!strcmp(tmp,"AuthenticAMD"))
  {
     int max_ext;
     a=0x80000000;
     cpuid(&a,&b,&c,&d);
     max_ext=a;
     if (max_ext>=0x80000005)
     {
       a=0x80000005;
       cpuid(&a,&b,&c,&d);
       if ((a>>16)&0xff) num++;
       if (a&0xff) num++;
       if ((b>>16)&0xff) num++;
       if (b&0xff) num++;
     }
     if (max_ext>=0x80000006)
     {
       a=0x80000006;
       cpuid(&a,&b,&c,&d);
       if ((a>>16)&0xfff) num++;
       if (a&0xfff) num++;
       if ((b>>16)&0xfff) num++;
       if (b&0xfff) num++;
     }
     if (max_ext>=0x80000019)
     {
       a=0x80000019;
       cpuid(&a,&b,&c,&d);
       if ((a>>16)&0xfff) num++;
       if (a&0xfff) num++;
       if ((b>>16)&0xfff) num++;
       if (b&0xfff) num++;
     }

     return num;
  }

  /* Intel specific */
  if (!strcmp(tmp,"GenuineIntel"))
  {
    int descriptors[15];
    int i,j,iter;

    a=0;
    cpuid(&a,&b,&c,&d);
    if (a>=2)
    {
      a=0x00000002;
      cpuid(&a,&b,&c,&d);

      iter=(a&0xff);

      for (i=0;i<iter;i++)
      {
        a=0x00000002;
        cpuid(&a,&b,&c,&d);

        for (j=0;j<4;j++) descriptors[j]=0;   

        /* read three descriptors from EAX */
        if (!(a&0x80000000)) for (j=1;j<4;j++) descriptors[j-1]=(a>>(8*j))&0xff;

        /* read four descriptors from EBX,ECX,EDX */
        for (j=0;j<4;j++)
        {
          if (!(b&0x80000000)) descriptors[j+3]=(b>>(8*j))&0xff; 
          if (!(c&0x80000000)) descriptors[j+7]=(c>>(8*j))&0xff; 
          if (!(d&0x80000000)) descriptors[j+11]=(d>>(8*j))&0xff;
        }

        for (j=0;j<15;j++)
        {

          switch(descriptors[j])
          {
            case 0x00: break;
            case 0x01: num++;break;
            case 0x02: num++;break;
            case 0x03: num++;break;
            case 0x04: num++;break;
            case 0x05: num++;break;
            case 0x0b: num++;break;
            case 0x4f: num++;break; 
            case 0x50: num++;break;
            case 0x51: num++;break;
            case 0x52: num++;break;
            case 0x55: num++;break;
            case 0x56: num++;break;
            case 0x57: num++;break;
            case 0x59: num++;break;
            case 0x5a: num++;break;
            case 0x5b: num++;break;
            case 0x5c: num++;break;
            case 0x5d: num++;break;
            case 0x61: num++;break;
            case 0x63: num++;break;
            case 0x76: num++;break;
            case 0xa0: num++;break;
            case 0xb0: num++;break;
            case 0xb1: num++;break;
            case 0xb2: num++;break;
            case 0xb3: num++;break;
            case 0xb4: num++;break;
            case 0xb5: num++;break;
            case 0xb6: num++;break;
            case 0xbA: num++;break;
            case 0xc0: num++;break;
            case 0xc1: num++;break;
            case 0xc2: num++;break;
            case 0xc3: num++;break;
            case 0xca: num+=2;break;
            default: break;
          }

        }

      }
    }
    else return generic_num_tlbs(cpu);

    return num;
  }

  /* TODO other vendors */
  return generic_num_tlbs(cpu);
}

int tlb_info(int cpu, int id, char* output,size_t len)
{
  char tmp[16];
  char tmp_string[_HW_DETECT_MAX_OUTPUT];
  int type=-1; /* 0 Unified, 1 Inst, 2 Data */
  int level,entries;
  int assoc; /* 0 fully associative, 1 direct mapped, >1 n-way set associative */
  int pagesize;
  int comma;
  int reduced_4M=0;
  int disabled=0;

  if (get_cpu_vendor(tmp,16)==-1) return generic_tlb_info(cpu,id,output,len);

  /* AMD specific */
  if (!strcmp(tmp,"AuthenticAMD"))
  {
     int max_ext;
     int translate=0;

     a=0x80000000;
     cpuid(&a,&b,&c,&d);
     max_ext=a;
     if (max_ext>=0x80000005)
     {
       a=0x80000005;
       cpuid(&a,&b,&c,&d);
       if (b&0xff) {id--;if (id==-1){type=INSTRUCTION_TLB;level=1;entries=(b&0xff);pagesize=0x1;assoc=((b>>8)&0xff);reduced_4M=1;if (assoc==0xff) assoc=0;}}
       if (a&0xff) {id--;if (id==-1){type=INSTRUCTION_TLB;level=1;entries=(a&0xff);pagesize=0x6;assoc=((a>>8)&0xff);reduced_4M=1;if (assoc==0xff) assoc=0;}}
     }
     if (max_ext>=0x80000019)
     {
       a=0x80000019;
       cpuid(&a,&b,&c,&d);
       if (a&0xfff) {id--;if (id==-1){type=INSTRUCTION_TLB;level=1;entries=(a&0xfff);pagesize=0x8;assoc=((a>>12)&0xf);reduced_4M=1;translate=1;}}
     }
     if (max_ext>=0x80000005)
     {
       a=0x80000005;
       cpuid(&a,&b,&c,&d);
       if ((b>>16)&0xff) {id--;if (id==-1){type=DATA_TLB;level=1;entries=((b>>16)&0xff);pagesize=0x1;assoc=((b>>24)&0xff);reduced_4M=1;if (assoc==0xff) assoc=0;}}
       if ((a>>16)&0xff) {id--;if (id==-1){type=DATA_TLB;level=1;entries=((a>>16)&0xff);pagesize=0x6;assoc=((a>>24)&0xff);reduced_4M=1;if (assoc==0xff) assoc=0;}}
     }
     if (max_ext>=0x80000019)
     {
       a=0x80000019;
       cpuid(&a,&b,&c,&d);
       if ((a>>16)&0xfff){id--;if (id==-1){type=DATA_TLB;level=1;entries=((a>>16)&0xfff);pagesize=0x8;assoc=((a>>28)&0xf);reduced_4M=1;translate=1;}}
     }
     if (max_ext>=0x80000006)
     {
       a=0x80000006;
       cpuid(&a,&b,&c,&d);
       if (b&0xfff) {id--;if (id==-1){type=INSTRUCTION_TLB;level=2;entries=(b&0xfff);pagesize=0x1;assoc=((b>>12)&0xf);reduced_4M=1;translate=1;}}
       if (a&0xfff) {id--;if (id==-1){type=INSTRUCTION_TLB;level=2;entries=(a&0xfff);pagesize=0x6;assoc=((a>>12)&0xf);reduced_4M=1;translate=1;}}
     }
     if (max_ext>=0x80000019)
     {
       a=0x80000019;
       cpuid(&a,&b,&c,&d);
       if (b&0xfff) {id--;if (id==-1){type=INSTRUCTION_TLB;level=2;entries=(b&0xfff);pagesize=0x8;assoc=((b>>12)&0xf);reduced_4M=1;translate=1;}}
     }
     if (max_ext>=0x80000006)
     {
       a=0x80000006;
       cpuid(&a,&b,&c,&d);
       if ((b>>16)&0xfff) {id--;if (id==-1){type=DATA_TLB;level=2;entries=((b>>16)&0xfff);pagesize=0x1;assoc=((b>>28)&0xf);reduced_4M=1;translate=1;}}
       if ((a>>16)&0xfff) {id--;if (id==-1){type=DATA_TLB;level=2;entries=((a>>16)&0xfff);pagesize=0x6;assoc=((a>>28)&0xf);reduced_4M=1;translate=1;}}
     }
     if (max_ext>=0x80000019)
     {
       a=0x80000019;
       cpuid(&a,&b,&c,&d);
       if ((b>>16)&0xfff) {id--;if (id==-1){type=DATA_TLB;level=2;entries=((b>>16)&0xfff);pagesize=0x8;assoc=((b>>28)&0xf);reduced_4M=1;translate=1;}}
     }
     if (translate) switch(assoc)
     {
       case 0x0: disabled=1;
       case 0x6: assoc=8;break;
       case 0x8: assoc=16;break;
       case 0xa: assoc=32;break;
       case 0xb: assoc=48;break;
       case 0xc: assoc=64;break;
       case 0xd: assoc=96;break;
       case 0xe: assoc=128;break;
       case 0xf: assoc=0;break;
     }
  }
  /* Intel specific */
  if (!strcmp(tmp,"GenuineIntel"))
  {
    int descriptors[15];
    int i,j,iter;

    a=0;
    cpuid(&a,&b,&c,&d);
    if (a>=2)
    {
      a=0x00000002;
      cpuid(&a,&b,&c,&d);

/*
      printf("EAX: 0x%08llx\n",a);fflush(stdout);
      printf("EBX: 0x%08llx\n",b);fflush(stdout);
      printf("ECX: 0x%08llx\n",c);fflush(stdout);
      printf("EDX: 0x%08llx\n",d);fflush(stdout);
*/

      iter=(a&0xff);

      for (i=0;i<iter;i++)
      {
        a=0x00000002;
        cpuid(&a,&b,&c,&d);

        for (j=0;j<4;j++) descriptors[j]=0;   

        /* read three descriptors from EAX */
        if (!(a&0x80000000)) for (j=1;j<4;j++) descriptors[j-1]=(a>>(8*j))&0xff;

        /* read four descriptors from EBX,ECX,EDX */
        for (j=0;j<4;j++)
        {
          if (!(b&0x80000000)) descriptors[j+3]=(b>>(8*j))&0xff; 
          if (!(c&0x80000000)) descriptors[j+7]=(c>>(8*j))&0xff; 
          if (!(d&0x80000000)) descriptors[j+11]=(d>>(8*j))&0xff;
        }

        for (j=0;j<15;j++)
        {
          /*TODO sort*/

          switch(descriptors[j])
          {

            case 0x00: break;
            /* TODO check if 4M TLBs support 2M pages (at twice the capacity?) */

            /* TLB0 -> 1st level data TLB */
            case 0x57: id--;if (id==-1){type=DATA_TLB;level=1;entries=16;pagesize=0x1;assoc=4;reduced_4M=0;}break;
            case 0x59: id--;if (id==-1){type=DATA_TLB;level=1;entries=16;pagesize=0x1;assoc=FULLY_ASSOCIATIVE;reduced_4M=0;}break;
            case 0x56: id--;if (id==-1){type=DATA_TLB;level=1;entries=16;pagesize=0x4;assoc=4;reduced_4M=0;}break;
            case 0x5a: id--;if (id==-1){type=DATA_TLB;level=1;entries=32;pagesize=0x6;assoc=4;reduced_4M=0;}break;
            /* TLB1 -> 2nd level data TLB */
            case 0xb4: id--;if (id==-1){type=DATA_TLB;level=2;entries=256;pagesize=0x1;assoc=4;reduced_4M=0;}break;
            case 0xba: id--;if (id==-1){type=DATA_TLB;level=2;entries=64;pagesize=0x1;assoc=4;reduced_4M=0;}break;
            case 0x05: id--;if (id==-1){type=DATA_TLB;level=2;entries=32;pagesize=0x4;assoc=4;reduced_4M=0;}break;

            /* Instruction TLB -> 1st level inst. TLB */
            case 0x01: id--;if (id==-1){type=INSTRUCTION_TLB;level=1;entries=32;pagesize=0x1;assoc=4;reduced_4M=0;}break;
            case 0xb2: id--;if (id==-1){type=INSTRUCTION_TLB;level=1;entries=64;pagesize=0x1;assoc=4;reduced_4M=0;}break;
            case 0xb0: id--;if (id==-1){type=INSTRUCTION_TLB;level=1;entries=128;pagesize=0x1;assoc=4;reduced_4M=0;}break;
            case 0x4f: id--;if (id==-1){type=INSTRUCTION_TLB;level=1;entries=32;pagesize=0x1;assoc=4;reduced_4M=0;}break; /* TODO undefined associativity */
            case 0x61: id--;if (id==-1){type=INSTRUCTION_TLB;level=1;entries=48;pagesize=0x1;assoc=FULLY_ASSOCIATIVE;reduced_4M=0;}break;
            case 0xb5: id--;if (id==-1){type=INSTRUCTION_TLB;level=1;entries=64;pagesize=0x1;assoc=8;reduced_4M=0;}break;
            case 0xb6: id--;if (id==-1){type=INSTRUCTION_TLB;level=1;entries=128;pagesize=0x1;assoc=8;reduced_4M=0;}break;
            case 0x50: id--;if (id==-1){type=INSTRUCTION_TLB;level=1;entries=64;pagesize=0x7;assoc=FULLY_ASSOCIATIVE;reduced_4M=0;}break;
            case 0x51: id--;if (id==-1){type=INSTRUCTION_TLB;level=1;entries=128;pagesize=0x7;assoc=FULLY_ASSOCIATIVE;reduced_4M=0;}break;
            case 0x52: id--;if (id==-1){type=INSTRUCTION_TLB;level=1;entries=256;pagesize=0x7;assoc=FULLY_ASSOCIATIVE;reduced_4M=0;}break;
            case 0x02: id--;if (id==-1){type=INSTRUCTION_TLB;level=1;entries=2;pagesize=0x4;assoc=FULLY_ASSOCIATIVE;reduced_4M=0;}break;
            case 0x55: id--;if (id==-1){type=INSTRUCTION_TLB;level=1;entries=7;pagesize=0x6;assoc=FULLY_ASSOCIATIVE;reduced_4M=0;}break;
            case 0xb1: id--;if (id==-1){type=INSTRUCTION_TLB;level=1;entries=8;pagesize=0x6;assoc=4;reduced_4M=1;}break;
            case 0x76: id--;if (id==-1){type=INSTRUCTION_TLB;level=1;entries=8;pagesize=0x6;assoc=FULLY_ASSOCIATIVE;reduced_4M=0;}break;

            /* Data TLB -> 1st level data TLB*/ 
            case 0x03: id--;if (id==-1){type=DATA_TLB;level=1;entries=64;pagesize=0x1;assoc=4;reduced_4M=0;}break;
            case 0xb3: id--;if (id==-1){type=DATA_TLB;level=1;entries=128;pagesize=0x1;assoc=4;reduced_4M=0;}break;
            case 0xa0: id--;if (id==-1){type=DATA_TLB;level=1;entries=32;pagesize=0x1;assoc=FULLY_ASSOCIATIVE;reduced_4M=0;}break;
            case 0xc2: id--;if (id==-1){type=DATA_TLB;level=1;entries=16;pagesize=0x3;assoc=4;reduced_4M=0;}break;
            case 0x5b: id--;if (id==-1){type=DATA_TLB;level=1;entries=64;pagesize=0x5;assoc=FULLY_ASSOCIATIVE;reduced_4M=0;}break;
            case 0x5c: id--;if (id==-1){type=DATA_TLB;level=1;entries=128;pagesize=0x5;assoc=FULLY_ASSOCIATIVE;reduced_4M=0;}break;
            case 0x5d: id--;if (id==-1){type=DATA_TLB;level=1;entries=256;pagesize=0x5;assoc=FULLY_ASSOCIATIVE;reduced_4M=0;}break;
            case 0xc0: id--;if (id==-1){type=DATA_TLB;level=1;entries=8;pagesize=0x5;assoc=4;reduced_4M=0;}break;
            case 0x04: id--;if (id==-1){type=DATA_TLB;level=1;entries=8;pagesize=0x4;assoc=4;reduced_4M=0;}break;
            case 0x0b: id--;if (id==-1){type=DATA_TLB;level=1;entries=4;pagesize=0x4;assoc=FULLY_ASSOCIATIVE;reduced_4M=0;}break;
            case 0x63: id--;if (id==-1){type=DATA_TLB;level=1;entries=4;pagesize=0x8;assoc=4;reduced_4M=0;}break;

            /* STLB -> unified second level TLB */
            case 0xca: id--;if (id==-1){type=UNIFIED_TLB;level=2;entries=512;pagesize=0x1;assoc=4;reduced_4M=0;}break;
            case 0xc1: id--;if (id==-1){type=UNIFIED_TLB;level=2;entries=1024;pagesize=0x3;assoc=8;reduced_4M=0;}break;
            case 0xc3: id--;
                       if (id==-1){type=UNIFIED_TLB;level=2;entries=1536;pagesize=0x3;assoc=6;reduced_4M=0;}
                       if (id==0) {type=UNIFIED_TLB;level=2;entries=16;pagesize=0x8;assoc=4;reduced_4M=0;}
                       break;

          }
        }
      }
    }
  }

  /* TODO other vendors */

  if (type==-1) return generic_tlb_info(cpu,id,output,len);
  memset(output,0,len);
  if (disabled)  strncat(output,"Disabled: ",len-1);
  if (level>0) switch(type)
  {
    case UNIFIED_TLB: snprintf(tmp_string,_HW_DETECT_MAX_OUTPUT,"Unified Level %i TLB",level);break;
    case INSTRUCTION_TLB: snprintf(tmp_string,_HW_DETECT_MAX_OUTPUT,"Level %i Instruction TLB",level);break;
    case DATA_TLB: snprintf(tmp_string,_HW_DETECT_MAX_OUTPUT,"Level %i Data TLB",level);break;
  }
/*  if (level==0) switch(type)
  {
    case UNIFIED_TLB: snprintf(tmp_string,_HW_DETECT_MAX_OUTPUT,"Unified Level %i (loads only) TLB",level);break;
    case INSTRUCTION_TLB: snprintf(tmp_string,_HW_DETECT_MAX_OUTPUT,"Level %i (loads only) Instruction TLB",level);break;
    case DATA_TLB: snprintf(tmp_string,_HW_DETECT_MAX_OUTPUT,"Level %i (loads only) Data TLB",level);break;
  } */

  strncat(output,tmp_string,(len-strlen(output))-1);
  snprintf(tmp_string,_HW_DETECT_MAX_OUTPUT," for ");
  strncat(output,tmp_string,(len-strlen(output))-1);
  comma=0;
  if (pagesize&0x1) {strncat(output,"4K",(len-strlen(output))-1);comma=1;}

  #if defined _32_BIT
    /* TODO check if PAE or PSE are used by the OS*/
    if (pagesize&0x2) {if (comma) strncat(output,", ",(len-strlen(output))-1);strncat(output,"2M",(len-strlen(output))-1);comma=1;}
    if (pagesize&0x4) {if (comma) strncat(output,", ",(len-strlen(output))-1);if(reduced_4M) strncat(output,"4M(half capacity)",(len-strlen(output))-1); else strncat(output,"4M",(len-strlen(output))-1); comma=1;}
  #endif
  #if defined _64_BIT 
    /* 2M supported by all 64 Bit x86*/
    if (pagesize&0x2) {if (comma) strncat(output,", ",(len-strlen(output))-1);strncat(output,"2M",(len-strlen(output))-1);comma=1;}
    /* no 4M pages in 64 Bit Mode -> show only 2M if TLB supports 2M and 4M, show 4M only if 2M is not supported by TLB
       (according to Intels CPUID specification this is the case for a lot of TLBs in Intel CPUs - might be a bug in the docu) 
       TODO check if 4M TLBs support 2M pages (at twice the capacity?) */
    if ((pagesize&0x4)&&(!(pagesize&0x2))) {
     if (reduced_4M) {if (comma) strncat(output,", ",(len-strlen(output))-1); strncat(output,"4M(half capacity)",(len-strlen(output))-1); comma=1;} //should not happen if 2M pages are not supported
     else {if (comma) strncat(output,", ",(len-strlen(output))-1); strncat(output,"4M",(len-strlen(output))-1); comma=1;}
    }
    if (pagesize&0x8) {if (comma) strncat(output,", ",(len-strlen(output))-1);strncat(output,"1G",(len-strlen(output))-1);comma=1;}
  #endif
  snprintf(tmp_string,_HW_DETECT_MAX_OUTPUT," pages: %i entries",entries);
  strncat(output,tmp_string,(len-strlen(output))-1);
  switch (assoc)
  {
    case FULLY_ASSOCIATIVE: snprintf(tmp_string,_HW_DETECT_MAX_OUTPUT,", fully associative");break;
    case DIRECT_MAPPED: snprintf(tmp_string,_HW_DETECT_MAX_OUTPUT,", direct mapped");break;
    default: snprintf(tmp_string,_HW_DETECT_MAX_OUTPUT,", %i-way set associative",assoc);break;
  }
  strncat(output,tmp_string,(len-strlen(output))-1);

  return 0;
}
 //TODO
 /* additional functions to query certain information about the TLB*/
 int tlb_level(int cpu, int id){
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;

   tlb_info(cpu,id,tmp,sizeof(tmp));
   beg=strstr(tmp,"Level");
   if (beg==NULL) return generic_tlb_level(cpu,id);
   else beg+=6;
   end=strstr(beg," ");
   if (end!=NULL)*end='\0';

   return atoi(beg);
 }
 int tlb_entries(int cpu, int id){
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;

   tlb_info(cpu,id,tmp,sizeof(tmp));
   beg=strstr(tmp,":");
   if (beg==NULL) return generic_tlb_entries(cpu,id);
   else beg+=2;
   end=strstr(beg,",");
   if (end!=NULL) *end='\0';
   end=strstr(beg,"entries");
   if (end!=NULL)
   {
     end--;
     *end='\0';
     return atoi(beg); 
   }

   return generic_tlb_entries(cpu,id);
 }
 int tlb_assoc(int cpu, int id){
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;

   tlb_info(cpu,id,tmp,sizeof(tmp));
   beg=strstr(tmp,":")+1;
   if (beg==NULL) return generic_tlb_assoc(cpu,id);
   else beg++;
   end=strstr(beg,",")+1;
   if (end==NULL) return generic_tlb_assoc(cpu,id);
   else end++;
   beg=end;
   end=strstr(beg,",");
   if (end!=NULL) *end='\0';
   end=strstr(tmp,"-way");
   if (end!=NULL) {
     *end='\0';
     return atoi(beg);
   }
   end=strstr(tmp,"fully");
   if (end!=NULL) {
     *end='\0';
     return FULLY_ASSOCIATIVE;
   }
   return generic_tlb_assoc(cpu,id);
 }
 int tlb_type(int cpu, int id){
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;

   tlb_info(cpu,id,tmp,sizeof(tmp));
   beg=tmp;
   end=strstr(beg,":");
   if (end!=NULL)*end='\0';
   else return generic_tlb_type(cpu,id);

   if (strstr(beg,"Unified")!=NULL) return UNIFIED_TLB;
   if (strstr(beg,"Data")!=NULL) return DATA_TLB;
   if (strstr(beg,"Instruction")!=NULL) return INSTRUCTION_TLB;

   return generic_tlb_type(cpu,id);
 }
 int tlb_num_pagesizes(int cpu, int id){
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;
   int num=1;

   tlb_info(cpu,id,tmp,sizeof(tmp));
   beg=strstr(tmp,"for");
   if (beg==NULL) return generic_tlb_num_pagesizes(cpu,id);
   else beg+=4;
   end=strstr(beg,"pages");
   if (end!=NULL)*end='\0';
   else return generic_tlb_num_pagesizes(cpu,id);

   while (strstr(beg,",")!=NULL) {
     beg++;num++;
   }

   return num;
 }
 unsigned long long tlb_pagesize(int cpu, int id,int size_id){
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;
   int num=0;

   tlb_info(cpu,id,tmp,sizeof(tmp));
   beg=strstr(tmp,"for");
   if (beg==NULL) return generic_tlb_pagesize(cpu,id,size_id);
   else beg+=4;
   end=strstr(beg,"pages");
   if (end!=NULL){*end='\0';end--;}
   else return generic_tlb_pagesize(cpu,id,size_id);

   while (num!=size_id){
     if (strstr(beg,",")!=NULL) {beg++;num++;}
     else return generic_tlb_pagesize(cpu,id,size_id);
   }
   end=strstr(beg," ");
   if ((strstr(beg,",")!=NULL)&&(strstr(beg,",")<end)) end=strstr(beg,",");

   end=strstr(beg,"K");
   if (end!=NULL)
   {
     *end='\0';
     return atoi(beg)*1024; 
   }
   end=strstr(beg,"M");
   if (end!=NULL)
   {
     *end='\0';
     return atoi(beg)*1024*1024; 
   }
   end=strstr(beg,"G");
   if (end!=NULL)
   {
     *end='\0';
     return atoi(beg)*1024*1024*1024; 
   }

   return num;
 }

int num_packages()
{
  if ((num_cpus()==-1)||(num_threads_per_package()==-1)) return generic_num_packages();
  else if (!has_htt()) return num_cpus();
  else return num_cpus()/num_threads_per_package();
}

int num_cores_per_package()
{
  char tmp[16];
  int num=-1;

  if (!has_htt()) return 1;
  if (get_cpu_vendor(tmp,16)!=0) return generic_num_cores_per_package();

  if (!strcmp(&tmp[0],"GenuineIntel"))
  {
    /* prefer generic implementation on Processors that might support Hyperthreading */
    if (generic_num_cores_per_package()!=-1)
    {
      /* Hyperthreading, Netburst*/
      if (get_cpu_family()==15) num=generic_num_cores_per_package();
      /* Hyperthreading, Nehalem/Atom*/
      if ((get_cpu_family()==6)&&(get_cpu_model()>=26)) num=generic_num_cores_per_package();
      /* MIC */
      if (get_cpu_family()==11) num=generic_num_cores_per_package();
      if (num!=-1) return num;
    }
    
    a=0;
    cpuid(&a,&b,&c,&d);
    if (a>=4)
    {
      a=4;c=0;
      cpuid(&a,&b,&c,&d);
      num= (a>>26)+1;
    }
    else num=1;

    if (num>num_cpus()) num=num_cpus();
    return num;
  }
  if (!strcmp(&tmp[0],"AuthenticAMD"))
  {
    a=0x80000000;
    cpuid(&a,&b,&c,&d);
    if (a>=0x80000008)
    {
      a=0x80000008;
      cpuid(&a,&b,&c,&d);
      num= (c&0xff)+1;
    }
    else num=1;
    /* consistency checks */
    /* more cores than cpus is not possible -> some cores are deactivated */
    if (num>num_cpus()) num=num_cpus();
    /* if the number of packages is known this cann be checked for multi-socket systems, too
       NOTE depends on valid entries in sysfs */
    if ((generic_num_packages()!=-1)&&(generic_num_packages()*num>num_cpus())) num=num_cpus()/generic_num_packages();

    return num;
  }
  //TODO other vendors

  return generic_num_cores_per_package();
}

int num_threads_per_core()
{
  return num_threads_per_package()/num_cores_per_package();
}

int num_threads_per_package()
{
  int num=-1;
  char tmp[16];

  if (has_cpuid())
  {
   if (!has_htt()) return 1;
   get_cpu_vendor(tmp,16);
   a=0;
   cpuid(&a,&b,&c,&d);
   if (a>=1)
   {
     /* prefer generic implementation on Processors that support Hyperthreading */
     /* TODO check if there are any models above 26 that don't have HT*/
     if ((!strcmp(tmp,"GenuineIntel"))&&(generic_num_threads_per_package()!=-1))
     {
       /* Hyperthreading, Netburst*/
       if (get_cpu_family()==15) num=generic_num_threads_per_package();
       /* Hyperthreading, Nehalem/Atom */
       if ((get_cpu_family()==6)&&(get_cpu_model()>=26)) num=generic_num_threads_per_package();
       /* MIC */
       if (get_cpu_family()==11) num=generic_num_threads_per_package();
       if (num!=-1) return num;
     }

    a=1;
    cpuid(&a,&b,&c,&d);
    num=((b>>16)&0xff);

    /* check if SMT is supported but deactivated (cpuid reports maximum logical processor count, even if some are deactivated in BIOS) */
    /* this simple test will do the trick for single socket systems (e.g. Pentium 4/D) */
    if (num>num_cpus()) num=num_cpus();
    /* distinguishing between a dual socket system that supports but does not use SMT and a single socket system that uses SMT 
       is not as trivial:
       e.g. dual socket single core Xeon with deactivated Hyperthreading vs. single socket single core Xeon with enabled HT
            -> - num_cpus = 2 (reported by sysconf) 
               - num_threads_per_package = 2 (cpuid.1:EBX[23:16] -> maximal logical processor count) 
               - num_cores_per_package = 1  (cpuid.4:EAX[31:26]+1)
    NOTE if sysfs/cpuinfo detection of physical packages fails the dual socket system with deactivated
         Hyperthreading will be reported as single socket system with enabled HyperThreading */
    if ((generic_num_packages()!=-1)&&(generic_num_packages()*num>num_cpus())) num=num_cpus()/generic_num_packages();

    return num;
   }
   else if (generic_num_threads_per_package()!=-1) return generic_num_threads_per_package();
   else return 1;
  }
  else if (generic_num_threads_per_package()!=-1) return generic_num_threads_per_package();
  else return 1;
}

#endif

