/**
* @file cpu.h
*  interface definition of hardware detection routines
* 
* Author: Daniel Molka (daniel.molka@zih.tu-dresden.de)
*/
#ifndef __cpu_h
#define __cpu_h

/* needed for CPU_SET macros and sched_{set|get}affinity() functions (is not available with older glibc versions) */
/* TODO check availability in MAC OS, AIX */
#if (defined(linux) || defined(__linux__)) && defined(AFFINITY)
 #define _GNU_SOURCE
 #include <sched.h>
#endif
/* needed for sched_getcpu() (is not available with older glibc versions) */
/* TODO check availability in MAC OS, AIX */
#if (defined(linux) || defined(__linux__)) && defined(SCHED_GETCPU)
 #define _GNU_SOURCE
 #include <utmpx.h>
#endif

#include <string.h>
#include <time.h>
#include <sys/time.h>
#include <stdio.h>

/*
 * definitions for cache and TLB properties
 */
#define INSTRUCTION_CACHE        0x01
#define DATA_CACHE               0x02
#define UNIFIED_CACHE            0x03
#define INSTRUCTION_TRACE_CACHE  0x04
#define INSTRUCTION_TLB          0x01
#define DATA_TLB                 0x02
#define UNIFIED_TLB              0x03

/* associativity, >1 is n-way set-associative */
#define FULLY_ASSOCIATIVE        0
#define DIRECT_MAPPED            1


#define _HW_DETECT_MAX_OUTPUT 512

/**
 * check the basic architecture of the mashine, each architecture needs its own implementation
 * e.g. the implementation for __ARCH_X86 is in the file x86.c
 */
#if ((defined (__x86_64__))||(defined (__x86_64))||(defined (x86_64))||(defined (__i386__))||(defined (__i386))||(defined (i386))||(defined (__i486__))||(defined (__i486))||(defined (i486))||(defined (__i586__))||(defined (__i586))||(defined (i586))||(defined (__i686__))||(defined (__i686))||(defined (i686)))
 /* see x86.c */
 #define __ARCH_X86
#elif ((defined (__ARM__))||(defined (__ARM))||(defined (ARM))||(defined (__ARMv7__))||(defined (__ARMv7))||(defined (ARMv7)))
 /* see arm.c */	
 #define __ARCH_ARM
 #else
 /* see generic.c */
 #define __ARCH_UNKNOWN
#endif

/*
 * scheduling related functions needed for pinning processes during operations that need to be performed on a certain CPU
 */

 /** 
  * sets affinity to a certain cpu
  */
 extern int set_cpu(int cpu);

 /**
  * restores original affinity after changing with set_cpu() 
  */
 extern int restore_affinity();

 /** 
   * tries to determine on which cpu the program is being run 
   * @return -1 in case of an error, else number of the cpu the program runs on
   */
 extern int get_cpu();

/*
 * The following functions use architecture independent information provided by the OS 
 */

 /**
  * Determine number of CPUs in System
  * @return number of CPUs in the System
  */
 extern int num_cpus();

 /**
  * try to estimate ISA using compiler macros
  */
 extern void get_architecture(char* arch, size_t len);

 /** 
  * tries to determine the physical package, a cpu belongs to
  * @param cpu number of the cpu, -1 -> cpu the program runs on
  * @return -1 in case of an error, else physical package ID
  */
 extern int get_pkg(int cpu);

 /** 
  * tries to determine the core ID, a cpu belongs to
  * @param cpu number of the cpu, -1 -> cpu the program runs on
  * @return -1 in case of an error, else core ID
  */
 extern int get_core_id(int cpu);

 /**
  * determines how many NUMA Nodes are in the system
  * @return -1 in case of errors, 1 -> UMA, >1 -> NUMA
  */
 extern int num_numa_nodes();

 /** 
  * tries to determine the NUMA Node, a cpu belongs to
  * @param cpu number of the cpu, -1 -> cpu the program runs on
  * @return -1 in case of an error, else NUMA Node
  */
 extern int get_numa_node(int cpu);

 /**
  * frequency scaling information
  */
 extern int supported_frequencies(int cpu, char* output, size_t len);
 extern int scaling_governor(int cpu, char* output, size_t len);
 extern int scaling_driver(int cpu, char* output, size_t len);

/* 
 * The following functions are architecture specific
 */

 /**
  * basic information about cpus
  * TODO add cpu parameter
  */
 extern int get_cpu_vendor(char* vendor, size_t len);
 extern int get_cpu_name(char* name, size_t len);
 extern int get_cpu_codename(char* name, size_t len);
 #if ((defined (__ARM__))||(defined (__ARM))||(defined (ARM))||(defined (__ARMv7__))||(defined (__ARMv7))||(defined (ARMv7)))
 	extern void get_cpu_family(char* family, size_t len);
	extern void get_cpu_model(char* model, size_t len);
	extern void get_cpu_stepping(char* stepping, size_t len);
 #else
 	extern int get_cpu_family();
	extern int get_cpu_model();
 	extern int get_cpu_stepping();
 #endif
 extern int get_cpu_gate_length();

 /**
  * additional features (e.g. SSE)
  * TODO add cpu parameter
  */
 extern int get_cpu_isa_extensions(char* features, size_t len);

 extern int get_cpu_lwp(char* lwpfeatures, size_t len);

 /**
  * tests if a certain feature is supported
  * TODO add cpu parameter
  */
 extern int feature_available(char* feature);
 

 /**
  * measures clockrate using cpu-internal counters (if available)
  * @param check if set to 1 additional checks are performed if the result is reliable
  *              see implementations in the architecture specific and generic parts for mor details
  * @param cpu the cpu that should be used, cpu affinity has to be set to the desired cpu before calling this function
  *            used to determine which cpu should be checked (e.g. relevant for finding the appropriate directory in sysfs)
  */
 extern unsigned long long get_cpu_clockrate(int check,int cpu);

 /**
  * returns a timestamp from cpu-internal counters (if available)
  */
 extern unsigned long long timestamp();

 /**
  * number of caches (of one cpu). Not equivalent to the number of cachelevels, as Inst and Data Caches for the same level
  * are counted as 2 individual cache!
  * @param cpu the cpu that should be used, cpu affinity has to be set to the desired cpu before calling this function
  *            used to determine which cpu should be checked (e.g. relevant for finding the appropriate directory in sysfs)
  */
 extern int num_caches(int cpu);

 /**
  * information about the cache: level, associativity...
  * @param cpu the cpu that should be used, cpu affinity has to be set to the desired cpu before calling this function
  *            used to determine which cpu should be checked (e.g. relevant for finding the appropriate directory in sysfs)
  * @param id id of the cache 0 <= id <= num_caches()-1
  * @param output preallocated buffer for the result string
  */
 extern int cache_info(int cpu, int id, char* output, size_t len);
 /* additional functions to query certain information about a cache */
 extern int cache_level(int cpu, int id);
 extern unsigned long long cache_size(int cpu, int id);
 extern unsigned int cache_assoc(int cpu, int id);
 extern int cache_type(int cpu, int id);
 extern int cache_shared(int cpu, int id);
 extern int cacheline_length(int cpu, int id);

 /**
  * number of tlbs (of one cpu). Not equivalent to number of TLB levels, as ITLBs and DTLBs as well as TLBs for different
  * pagesizes are counted individually!
  * @param cpu the cpu that should be used, cpu affinity has to be set to the desired cpu before calling this function
  *            used to determine which cpu should be checked (e.g. relevant for finding the appropriate directory in sysfs)
  */
 extern int num_tlbs(int cpu);
 /**
  * information about the tlb: level, number of entries...
  * @param cpu the cpu that should be used, cpu affinity has to be set to the desired cpu before calling this function
  *            used to determine which cpu should be checked (e.g. relevant for finding the appropriate directory in sysfs)
  * @param id id of the TLB 0 <= id <= num_tlbs()-1
  * @param output preallocated buffer for the result string
  */
 extern int tlb_info(int cpu, int id, char* output, size_t len);
 /* additional functions to query certain information about a tlb */
 extern int tlb_level(int cpu, int id);
 extern int tlb_entries(int cpu, int id);
 extern int tlb_assoc(int cpu, int id);
 extern int tlb_type(int cpu, int id);
 extern int tlb_num_pagesizes(int cpu, int id);
 extern unsigned long long tlb_pagesize(int cpu, int id,int size_id);

 /**
  * paging related information
  * TODO add cpu parameter
  */
 extern int get_virt_address_length();
 extern int get_phys_address_length();
 extern int num_pagesizes(); 
 extern long long pagesize(int id); /* 0 <= id < num_pagesizes() */

 /**
  * the following four functions estimate how the CPUs are distributed among packages
  * num_cpus() = num_packages() * num_threads_per_package()
  * num_threads_per_package() = num_cores_per_package() * num_threads_per_core()
  */
 extern int num_packages();
 extern int num_cores_per_package();   /* >1 -> Multicore */
 extern int num_threads_per_core();    /* >1 -> SMT support */
 extern int num_threads_per_package(); /* >1 Multicore or SMT or both */

/*
 * fallback functions used for unsupported architectures and in case of errors
 * or unavailable information in the architecture dependent detection
 * see generic.c
 */
 extern int generic_get_cpu_vendor(char* vendor, size_t len);
 extern int generic_get_cpu_name(char* name, size_t len);
 extern int generic_get_cpu_codename(char* name, size_t len);
 extern int generic_get_cpu_family();
 extern int generic_get_cpu_model();
 extern int generic_get_cpu_stepping();
 extern int generic_get_cpu_gate_length();
 extern int generic_get_cpu_isa_extensions(char* features, size_t len);
 extern int generic_get_cpu_lwp(char* lwpfeatures, size_t len);
 extern unsigned long long generic_get_cpu_clockrate(int check,int cpu);
 extern unsigned long long generic_timestamp();
 extern int generic_num_caches(int cpu);
 extern int generic_cache_info(int cpu, int id, char* output, size_t len);
 extern int generic_cache_level(int cpu, int id);
 extern unsigned long long generic_cache_size(int cpu, int id);
 extern unsigned int generic_cache_assoc(int cpu, int id);
 extern int generic_cache_type(int cpu, int id);
 extern int generic_cache_shared(int cpu, int id);
 extern int generic_cacheline_length(int cpu, int id);
 extern int generic_num_tlbs(int cpu);
 extern int generic_tlb_info(int cpu, int id, char* output, size_t len);
 extern int generic_tlb_level(int cpu, int id);
 extern int generic_tlb_entries(int cpu, int id);
 extern int generic_tlb_assoc(int cpu, int id);
 extern int generic_tlb_type(int cpu, int id);
 extern int generic_tlb_num_pagesizes(int cpu, int id);
 extern unsigned long long generic_tlb_pagesize(int cpu, int id,int size_id);
 extern int generic_num_packages();
 extern int generic_num_cores_per_package();
 extern int generic_num_threads_per_core();
 extern int generic_num_threads_per_package();
 extern int generic_get_virt_address_length();
 extern int generic_get_phys_address_length();
 extern int generic_num_pagesizes();
 extern long long generic_pagesize(int id);

#endif

