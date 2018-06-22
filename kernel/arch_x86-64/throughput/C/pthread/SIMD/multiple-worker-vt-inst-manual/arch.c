/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id$
 * For license details see COPYING in the package base directory
 *******************************************************************/

#define _GNU_SOURCE
#include <sched.h>

#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <sys/time.h>
#include <fcntl.h>

#include "work.h"
#include "arch.h"
#include "cpu.h"
#include "x86.h"

#define MAX_OUTPUT 512

static char output[MAX_OUTPUT];

/** initializes cpuinfo-struct
 * @param print detection-summary is written to stdout when !=0
 */
void init_cpuinfo(cpu_info_t *cpuinfo,int print)
{
  int i,j;
  char *tmp,*tmp2;
  int pagesize_id;

/**
  * read ARM cpuid-register
  */

  /* initialize data structure */
  memset(cpuinfo,0,sizeof(cpu_info_t));  
  strcpy(cpuinfo->architecture,"unknown");
  strcpy(cpuinfo->vendor,"unknown");
  strcpy(cpuinfo->model_str,"unknown");

  /* use functions provided by ${BENCHITROOT}/tolls/hw_detect to determine architecture information*/
  cpuinfo->num_cores=num_cpus();
  cpuinfo->num_cores_per_package=num_cores_per_package();
  cpuinfo->num_threads_per_core=num_threads_per_core();
  cpuinfo->num_phy_cores=num_cpus()/num_threads_per_core();
  cpuinfo->num_threads_per_package=num_threads_per_package();
  cpuinfo->num_packages=num_packages();
  cpuinfo->num_numa_nodes=num_numa_nodes();
  get_architecture(cpuinfo->architecture,sizeof(cpuinfo->architecture));
  get_cpu_vendor(cpuinfo->vendor,sizeof(cpuinfo->vendor));
  get_cpu_name(cpuinfo->model_str,sizeof(cpuinfo->model_str));
  cpuinfo->family=get_cpu_family();
  cpuinfo->model=get_cpu_model();
  cpuinfo->stepping=get_cpu_stepping();
  cpuinfo->num_pagesizes=num_pagesizes();
  if (cpuinfo->num_pagesizes>MAX_PAGESIZES) cpuinfo->num_pagesizes=MAX_PAGESIZES;
  for (i=0;i<cpuinfo->num_pagesizes;i++) cpuinfo->pagesizes[i]=pagesize(i);
  cpuinfo->phys_addr_length=get_phys_address_length();
  cpuinfo->virt_addr_length=get_virt_address_length();
  cpuinfo->clockrate=get_cpu_clockrate(1,0);

  /* setup supported feature list*/
  supported_frequencies(0,output,sizeof(output));
  tmp=strstr(output,"MHz");
  if (tmp!=NULL){
     tmp2=strstr(tmp+3,"MHz");
     if (tmp2!=NULL) cpuinfo->features|=FREQ_SCALING;
  }
  if(!strcmp(cpuinfo->architecture,"x86_64")) cpuinfo->features|=X86_64;
  if (feature_available("FPU")) cpuinfo->features|=FPU;
  if (feature_available("MMX")) cpuinfo->features|=MMX;
  if (feature_available("MMX_EXT")) cpuinfo->features|=MMX_EXT;
  if (feature_available("3DNOW")) cpuinfo->features|=_3DNOW;
  if (feature_available("3DNOW_EXT")) cpuinfo->features|=_3DNOW_EXT;
  if (feature_available("SSE")) cpuinfo->features|=SSE;
  if (feature_available("SSE2")) cpuinfo->features|=SSE2;
  if (feature_available("SSE3")) cpuinfo->features|=SSE3;
  if (feature_available("SSSE3")) cpuinfo->features|=SSSE3;
  if (feature_available("SSE4.1")) cpuinfo->features|=SSE4_1;
  if (feature_available("SSE4.2")) cpuinfo->features|=SSE4_2;
  if (feature_available("SSE4A")) cpuinfo->features|=SSE4A;
  if (feature_available("SSE5")) cpuinfo->features|=SSE5;
  if (feature_available("ABM")) cpuinfo->features|=ABM;
  if (feature_available("POPCNT")) cpuinfo->features|=POPCNT;
  if (feature_available("CX8")) cpuinfo->features|=CX8;
  if (feature_available("CX16")) cpuinfo->features|=CX16;
  if (feature_available("CLFLUSH")) cpuinfo->features|=CLFLUSH;
  if (feature_available("CLFLUSH")) {
    get_cpu_isa_extensions(output, sizeof(output));
    tmp=strstr(output,"CLFLUSH");
    if (tmp!=NULL) tmp+=7;
    if ((tmp!=NULL)&&(*tmp=='(')) {
      tmp++;
      tmp2=strstr(tmp," ");
      *tmp2='\0';
      cpuinfo->clflush_linesize=atoi(tmp);
    }    
  }
  if (feature_available("RDTSC")) cpuinfo->features|=TSC;
  if (has_rdtsc()){
    cpuinfo->features|=TSC;
    cpuinfo->rdtsc_latency=get_rdtsc_latency();
    cpuinfo->tsc_invariant=has_invariant_rdtsc();
  }
  if (feature_available("MONITOR")) cpuinfo->features|=MONITOR;
  if (feature_available("MTRR")) cpuinfo->features|=MTRR;
  if (feature_available("NX")) cpuinfo->features|=NX;
  if (feature_available("CPUID")) cpuinfo->features|=CPUID;
  if (feature_available("AVX")) cpuinfo->features|=AVX;
  if (feature_available("AVX2")) cpuinfo->features|=AVX2;
  if (feature_available("FMA")) cpuinfo->features|=FMA;
  if (feature_available("FMA4")) cpuinfo->features|=FMA4;
  if (feature_available("LWP")) cpuinfo->features|=LWP;
  if (feature_available("AES")) cpuinfo->features|=AES;
  /* determine cache details */  
  for (i=0;i<num_caches(0);i++)
  {
    if (cpuinfo->Cachelevels<cache_level(0,i)) cpuinfo->Cachelevels=cache_level(0,i);
    switch (cache_type(0,i))
    {
      case UNIFIED_CACHE:
        cpuinfo->Cache_unified[cache_level(0,i)-1]=1;
        cpuinfo->U_Cache_Size[cache_level(0,i)-1]=cache_size(0,i);
        cpuinfo->U_Cache_Sets[cache_level(0,i)-1]=cache_assoc(0,i);
        cpuinfo->Cache_shared[cache_level(0,i)-1]=cache_shared(0,i);
        cpuinfo->Cacheline_size[cache_level(0,i)-1]=cacheline_length(0,i);
        break;
      case DATA_CACHE:
        cpuinfo->Cache_unified[cache_level(0,i)-1]=0;
        cpuinfo->D_Cache_Size[cache_level(0,i)-1]=cache_size(0,i);
        cpuinfo->D_Cache_Sets[cache_level(0,i)-1]=cache_assoc(0,i);
        cpuinfo->Cache_shared[cache_level(0,i)-1]=cache_shared(0,i);
        cpuinfo->Cacheline_size[cache_level(0,i)-1]=cacheline_length(0,i);
        break;
      case INSTRUCTION_CACHE:
        cpuinfo->Cache_unified[cache_level(0,i)-1]=0;
        cpuinfo->I_Cache_Size[cache_level(0,i)-1]=cache_size(0,i);
        cpuinfo->I_Cache_Sets[cache_level(0,i)-1]=cache_assoc(0,i);
	// sharing and cacheline width determined by data cache at same level
        break;
      case INSTRUCTION_TRACE_CACHE:
      default:
        break;    
    }
  }
  //AMD (exclusive caches)
  if (!strcmp("AuthenticAMD",cpuinfo->vendor))
  {
    for (i=0;i<cpuinfo->Cachelevels;i++)
    {
      cpuinfo->Cacheflushsize+=cpuinfo->D_Cache_Size[i]+cpuinfo->U_Cache_Size[i];
      cpuinfo->Total_D_Cache_Size+=(cpuinfo->num_cores/cpuinfo->Cache_shared[i])*(cpuinfo->D_Cache_Size[i]+cpuinfo->U_Cache_Size[i]);
      cpuinfo->D_Cache_Size_per_Core+=cpuinfo->D_Cache_Size[i]+cpuinfo->U_Cache_Size[i];  
    }
  }
  //Intel (inclusive caches)
  if (!strcmp("GenuineIntel",cpuinfo->vendor))
  {
    for (i=0;i<cpuinfo->Cachelevels;i++)
    {
      cpuinfo->Cacheflushsize+=cpuinfo->D_Cache_Size[i]+cpuinfo->U_Cache_Size[i];
      cpuinfo->Total_D_Cache_Size=(cpuinfo->num_cores/cpuinfo->Cache_shared[i])*(cpuinfo->D_Cache_Size[i]+cpuinfo->U_Cache_Size[i]);
      cpuinfo->D_Cache_Size_per_Core=cpuinfo->D_Cache_Size[i]+cpuinfo->U_Cache_Size[i];   
		}
  }

  /* determine TLB properties */
  for (i=0;i<num_tlbs(0);i++)
  {
    for (j=0;j<tlb_num_pagesizes(0,i);j++) {
     pagesize_id=0;
     while ((tlb_pagesize(0,i,j)!=cpuinfo->pagesizes[pagesize_id])&&(pagesize_id<MAX_PAGESIZES)) pagesize_id++;
     if (cpuinfo->tlblevels<tlb_level(0,i)) cpuinfo->tlblevels=tlb_level(0,i);
     if (pagesize_id<MAX_PAGESIZES)
     {
      switch (tlb_type(0,i))
      {
       case UNIFIED_TLB:      
         cpuinfo->U_TLB_Size[tlb_level(0,i)-1][pagesize_id]=tlb_entries(0,i);
         cpuinfo->U_TLB_Sets[tlb_level(0,i)-1][pagesize_id]=tlb_assoc(0,i);
        break;
       case DATA_TLB:
         cpuinfo->D_TLB_Size[tlb_level(0,i)-1][pagesize_id]=tlb_entries(0,i);
         cpuinfo->D_TLB_Sets[tlb_level(0,i)-1][pagesize_id]=tlb_assoc(0,i);
         break;
       case INSTRUCTION_TLB:
         cpuinfo->I_TLB_Size[tlb_level(0,i)-1][pagesize_id]=tlb_entries(0,i);
         cpuinfo->I_TLB_Sets[tlb_level(0,i)-1][pagesize_id]=tlb_assoc(0,i);
         break;
       default:
         break;
      }
     }
    }
  }
  
  /* print a summary */
  if (print)
  {
    fflush(stdout);
    printf("\n  hardware detection summary:\n");
    printf("    architecture:   %s\n",cpuinfo->architecture);  
    printf("    vendor:         %s\n",cpuinfo->vendor);  
    printf("    processor-name: %s\n",cpuinfo->model_str);
    printf("    model:          Family %i, Model %i, Stepping %i\n",cpuinfo->family,cpuinfo->model,cpuinfo->stepping);
    printf("    frequency:      %llu MHz\n",cpuinfo->clockrate/1000000);
    if(cpuinfo->num_cores>0) printf("    number of CPUs: %i\n",cpuinfo->num_cores);
    if (cpuinfo->num_threads_per_core>0) {
      if ((cpuinfo->num_numa_nodes>0)&&(cpuinfo->num_packages>0)&&(cpuinfo->num_cores_per_package>0)) printf("                    %i sockets (%i NUMA nodes), %i cores per socket, %i threads per core \n",cpuinfo->num_packages,cpuinfo->num_numa_nodes,cpuinfo->num_cores_per_package,cpuinfo->num_threads_per_core);
      else if ((cpuinfo->num_packages>0)&&(cpuinfo->num_cores_per_package>0))printf("                    %i sockets, %i cores per socket, %i threads per core \n",cpuinfo->num_packages,cpuinfo->num_cores_per_package,cpuinfo->num_threads_per_core);
      else if (cpuinfo->num_cores>0) printf("                    %i cores, %i threads per core \n",cpuinfo->num_cores,cpuinfo->num_threads_per_core);
    }
    fflush(stdout);
    printf("    supported features:");
    //if(cpuinfo->features&X86_64) printf(" X86_64");
    if(cpuinfo->features&FPU) printf(" FPU");
    if(cpuinfo->features&MMX) printf(" MMX");
    if(cpuinfo->features&MMX_EXT) printf(" MMX_EXT");
    if(cpuinfo->features&_3DNOW) printf(" 3DNOW");
    if(cpuinfo->features&_3DNOW_EXT) printf(" 3DNOW_EXT");
    if(cpuinfo->features&SSE) printf(" SSE");
    if(cpuinfo->features&SSE2) printf(" SSE2");
    if(cpuinfo->features&SSE3) printf(" SSE3");
    if(cpuinfo->features&SSSE3) printf(" SSSE3");
    if(cpuinfo->features&SSE4_1) printf(" SSE4.1");
    if(cpuinfo->features&SSE4_2) printf(" SSE4.2");
    if(cpuinfo->features&SSE4A) printf(" SSE4A");
    if(cpuinfo->features&SSE5) printf(" SSE5");
    if(cpuinfo->features&AVX) printf(" AVX");
    if(cpuinfo->features&AVX2) printf(" AVX2");
    if(cpuinfo->features&FMA) printf(" FMA");
    if(cpuinfo->features&FMA4) printf(" FMA4");
    if(cpuinfo->features&LWP) printf(" LWP");
    if(cpuinfo->features&AES) printf(" AES");
    if(cpuinfo->features&POPCNT) printf(" POPCNT");
    if(cpuinfo->features&CX8) printf(" CX8");
    if(cpuinfo->features&CX16) printf(" CX16");
    if(cpuinfo->features&FREQ_SCALING) printf(" FREQ_SCALING");
    if(cpuinfo->features&MONITOR) printf(" MONITOR");
    if(cpuinfo->features&NX) printf(" NX");
    if(cpuinfo->features&CPUID) printf(" CPUID");
    if(cpuinfo->features&MTRR) printf(" MTRR");
    fflush(stdout);
    if(cpuinfo->features&TSC)   printf("\n                        TSC: %i cycles latency",cpuinfo->rdtsc_latency);
    if(cpuinfo->features&CLFLUSH) printf("\n                        CLFLUSH: %i Byte clflush-linesize",cpuinfo->clflush_linesize);
    printf("\n");fflush(stdout);

    if(cpuinfo->Cachelevels)
    {
     for(i=0;i<cpuinfo->Cachelevels;i++)
     {
        printf("    Level%i Cache:\n",i+1);
        if (cpuinfo->Cache_unified[i]) printf("      - Unified Cache for Data and Instructions\n"); else printf("      - Data Cache\n");
        if (cpuinfo->Cache_unified[i])
        {
          if (cpuinfo->U_Cache_Sets[i]==FULLY_ASSOCIATIVE) printf("      - %llu Bytes, fully associative\n",cpuinfo->U_Cache_Size[i]);
          else if (cpuinfo->U_Cache_Sets[i]==DIRECT_MAPPED) printf("      - %llu Bytes, direct mapped\n",cpuinfo->U_Cache_Size[i]);
          else printf("      - %llu Bytes, %i-way set-associative\n",cpuinfo->U_Cache_Size[i],cpuinfo->U_Cache_Sets[i]);
        }
        else
        {
          //if (cpuinfo->I_Cache_Sets[i]==FULLY_ASSOCIATIVE) printf("      - %llu Bytes I-Cache, fully associative\n",cpuinfo->I_Cache_Size[i]);
          //else if (cpuinfo->I_Cache_Sets[i]==DIRECT_MAPPED) printf("      - %llu Bytes I-Cache, direct mapped\n",cpuinfo->I_Cache_Size[i]);
          //else printf("      - %llu Bytes I-Cache, %i-way set-associative\n",cpuinfo->I_Cache_Size[i],cpuinfo->I_Cache_Sets[i]);
          if (cpuinfo->D_Cache_Sets[i]==FULLY_ASSOCIATIVE) printf("      - %llu Bytes, fully associative\n",cpuinfo->D_Cache_Size[i]);
          else if (cpuinfo->D_Cache_Sets[i]==DIRECT_MAPPED)printf("      - %llu Bytes, direct mapped\n",cpuinfo->D_Cache_Size[i]);
          else printf("      - %llu Bytes, %i-way set-associative\n",cpuinfo->D_Cache_Size[i],cpuinfo->D_Cache_Sets[i]);
        }
        if ((cpuinfo->Cache_shared[i])>1) printf("      - shared between %i CPU(s)\n",cpuinfo->Cache_shared[i]);
        else printf("      - per CPU\n");
        printf("      - %i Byte Cachelines\n",cpuinfo->Cacheline_size[i]);fflush(stdout);
     }
    }

    if (cpuinfo->num_pagesizes)
    {
      printf("    supported pagesizes:");
      for (i=0;i<cpuinfo->num_pagesizes;i++)
      {
        if(i) printf(",");
        if(cpuinfo->pagesizes[i]>=(1024*1048576)) printf(" %llu GiByte",cpuinfo->pagesizes[i]/(1024*1048576));
        else if(cpuinfo->pagesizes[i]>=1048576) printf(" %llu MiByte",cpuinfo->pagesizes[i]/1048576);
        else if(cpuinfo->pagesizes[i]>=1024) printf(" %llu KiByte",cpuinfo->pagesizes[i]/1024);
      }
      printf("\n");fflush(stdout);
    }
    if (cpuinfo->virt_addr_length) printf("    virtual address length:  %u bits\n",cpuinfo->virt_addr_length);
    if (cpuinfo->phys_addr_length) printf("    physical address length: %u bits\n",cpuinfo->phys_addr_length);
    fflush(stdout);
    
    if ((cpuinfo->tlblevels)&&(cpuinfo->num_pagesizes))
    {
      int tmp;
      char tmpstring[256];
      for(i=0;i<=cpuinfo->tlblevels;i++)
      {
        tmp=0;
        for(j=0;j<cpuinfo->num_pagesizes;j++)
        {
           if (cpuinfo->I_TLB_Size[i][j]!=0) tmp=1;
        }
        if (tmp)
        {
          printf("    Level%i ITLB:\n",i+1);
          for(j=0;j<cpuinfo->num_pagesizes;j++)
          {
            if(cpuinfo->pagesizes[j]>=(1024*1048576)) sprintf(tmpstring,"%llu GiByte pages",cpuinfo->pagesizes[j]/(1024*1048576));
            else if(cpuinfo->pagesizes[j]>=1048576) sprintf(tmpstring,"%llu MiByte pages",cpuinfo->pagesizes[j]/1048576);
            else if(cpuinfo->pagesizes[j]>=1024) sprintf(tmpstring,"%llu KiByte pages",cpuinfo->pagesizes[j]/1024);

            if (cpuinfo->I_TLB_Size[i][j]!=0)
            {
              if (cpuinfo->I_TLB_Sets[i][j]==FULLY_ASSOCIATIVE) printf("      %i entries for %s, fully associative\n",cpuinfo->I_TLB_Size[i][j],tmpstring);
              else if (cpuinfo->I_TLB_Sets[i][j]==DIRECT_MAPPED) printf("      %i entries for %s, direct mapped\n",cpuinfo->I_TLB_Size[i][j],tmpstring);              
              else printf("      %i entries for %s, %i-way set associative\n",cpuinfo->I_TLB_Size[i][j],tmpstring,cpuinfo->I_TLB_Sets[i][j]);
            }
          }
        }
        tmp=0;
        for(j=0;j<cpuinfo->num_pagesizes;j++)
        {
           if (cpuinfo->D_TLB_Size[i][j]!=0) tmp=1;
        }
        if (tmp)
        {
          printf("    Level%i DTLB:\n",i+1);
          for(j=0;j<cpuinfo->num_pagesizes;j++)
          {
            if(cpuinfo->pagesizes[j]>=(1024*1048576)) sprintf(tmpstring,"%llu GiByte pages",cpuinfo->pagesizes[j]/(1024*1048576));
            else if(cpuinfo->pagesizes[j]>=1048576) sprintf(tmpstring,"%llu MiByte pages",cpuinfo->pagesizes[j]/1048576);
            else if(cpuinfo->pagesizes[j]>=1024) sprintf(tmpstring,"%llu KiByte pages",cpuinfo->pagesizes[j]/1024);
            if (cpuinfo->D_TLB_Size[i][j]!=0)
            {

              if (cpuinfo->D_TLB_Sets[i][j]>1) printf("      %i entries for %s, %i-way set associative\n",cpuinfo->D_TLB_Size[i][j],tmpstring,cpuinfo->D_TLB_Sets[i][j]);
              else if (cpuinfo->D_TLB_Sets[i][j]==1) printf("      %i entries for %s, direct mapped\n",cpuinfo->D_TLB_Size[i][j],tmpstring);
              else printf("      %i entries for %s, fully associative\n",cpuinfo->D_TLB_Size[i][j],tmpstring);
            }
          }
        }
        tmp=0;
        for(j=0;j<cpuinfo->num_pagesizes;j++)
        {
           if (cpuinfo->U_TLB_Size[i][j]!=0) tmp=1;
        }
        if (tmp)
        {
          printf("    Level%i TLB (code and data):\n",i+1);
          for(j=0;j<cpuinfo->num_pagesizes;j++)
          {
            if(cpuinfo->pagesizes[j]>=(1024*1048576)) sprintf(tmpstring,"%llu GiByte pages",cpuinfo->pagesizes[j]/(1024*1048576));
            else if(cpuinfo->pagesizes[j]>=1048576) sprintf(tmpstring,"%llu MiByte pages",cpuinfo->pagesizes[j]/1048576);
            else if(cpuinfo->pagesizes[j]>=1024) sprintf(tmpstring,"%llu KiByte pages",cpuinfo->pagesizes[j]/1024);
            if (cpuinfo->U_TLB_Size[i][j]!=0)
            {

              if (cpuinfo->U_TLB_Sets[i][j]>1) printf("      %i entries for %s, %i-way set associative\n",cpuinfo->U_TLB_Size[i][j],tmpstring,cpuinfo->U_TLB_Sets[i][j]);
              else if (cpuinfo->U_TLB_Sets[i][j]==1) printf("      %i entries for %s, direct mapped\n",cpuinfo->U_TLB_Size[i][j],tmpstring);
              else printf("      %i entries for %s, fully associative\n",cpuinfo->U_TLB_Size[i][j],tmpstring);
            }
          }
        }
        fflush(stdout);
      }
    }
  }
  fflush(stdout);
}

/** pin process to a cpu
 */
int cpu_set(int id)
{
  cpu_set_t  mask;

  CPU_ZERO( &mask );
  CPU_SET(id , &mask );
  return sched_setaffinity(0,sizeof(cpu_set_t),&mask);
}

/** check if a cpu is allowed to be used
 */
int cpu_allowed(int id)
{
  cpu_set_t  mask;

  CPU_ZERO( &mask );
  if (!sched_getaffinity(0,sizeof(cpu_set_t),&mask))return CPU_ISSET(id,&mask);

  return 0;
}

/** flushes content of buffer from all cache-levels
 * @param buffer pointer to the buffer
 * @param size size of buffer in Bytes
 * @return 0 if successful
 *         -1 if not available
 */
int inline clflush(void* buffer,unsigned long long size,cpu_info_t cpuinfo)
{
  #if defined (__x86_64__)
  unsigned long long addr,passes,linesize;

  if(!(cpuinfo.features&CLFLUSH) || !cpuinfo.clflush_linesize) return -1;
  
  addr = (unsigned long long) buffer;
  linesize = (unsigned long long) cpuinfo.clflush_linesize;

  __asm__ __volatile__("mfence;"::: "memory"); 

  for(passes = (size/linesize);passes>0;passes--){
      __asm__ __volatile__("clflush (%%rax);":: "a" (addr));
      addr+=linesize;
  }

  __asm__ __volatile__("mfence;"::: "memory"); 

  #endif

  return 0;
}

/** misuses non temporal stores to flush cache
 * alternative for clflush
 * @param buffer pointer to the buffer
 * @param size size of buffer in Bytes
 * @return 0 if successful
 *         -1 if not available
 */
int inline write_nt(void* buffer,unsigned long long size,cpu_info_t cpuinfo)
{
  #if defined (__x86_64__)
  unsigned long long addr,passes,linesize;

  if(!(cpuinfo.features&SSE2)) return -1;

  addr = (unsigned long long) buffer;
  linesize = 8;
  
  __asm__ __volatile__("mfence;"::: "memory"); 
  for(passes = (size/linesize);passes>0;passes--){
      __asm__ __volatile__("mov (%%rax),%%rbx;movnti %%rbx, (%%rax);":: "a" (addr): "%rbx");
      addr+=linesize;
  }

  __asm__ __volatile__("mfence;"::: "memory"); 
  #endif

  return 0;
}

/** prefetches content of buffer 
 * @param buffer pointer to the buffer
 * @param size size of buffer in Bytes
 * @return 0 if successful
 *         -1 if not available
 */
int inline prefetch(void* buffer,unsigned long long size, cpu_info_t cpuinfo)
{
  #if defined (__x86_64__)
  unsigned long long addr,passes,linesize;
  int i;

  if(!(cpuinfo.features&SSE)) return -1;

  addr = (unsigned long long) buffer;
  linesize = 256;
  for (i=cpuinfo.Cachelevels;i>0;i--){
    if (cpuinfo.Cacheline_size[i-1]<linesize) linesize=cpuinfo.Cacheline_size[i-1];
  }

  for(passes = (size/linesize);passes>0;passes--){
    __asm__ __volatile__("prefetcht1 (%%rax);":: "a" (addr));
    addr+=linesize;
  }
  #endif

  return 0;
}

