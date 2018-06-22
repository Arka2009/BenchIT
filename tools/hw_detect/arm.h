typedef struct arm_cpu_info
{
  unsigned int vendor;
  //char model_str[48];
  unsigned int architecture;
  unsigned int features;
  unsigned int clflush_linesize;
  unsigned int rdtsc_latency;
  unsigned int tsc_invariant;
  unsigned int Cachelevels;
  unsigned int DCacheline_size;
  unsigned int DCache_assoc;
  unsigned int DCache_size;
  unsigned int ICacheline_size;
  unsigned int ICache_assoc;
  unsigned int ICache_size;
  //unsigned int Cache_unified[MAX_CACHELEVELS];
  //unsigned int Cache_shared[MAX_CACHELEVELS];
  //unsigned int Cacheline_size[MAX_CACHELEVELS];
  //unsigned int I_Cache_Size[MAX_CACHELEVELS];
  //unsigned int I_Cache_Sets[MAX_CACHELEVELS];
  //unsigned int D_Cache_Size[MAX_CACHELEVELS];
  //unsigned int D_Cache_Sets[MAX_CACHELEVELS];
  //unsigned int U_Cache_Size[MAX_CACHELEVELS];
  //unsigned int U_Cache_Sets[MAX_CACHELEVELS];
  unsigned int Total_D_Cache_Size;
  unsigned int D_Cache_Size_per_Core;
  unsigned int num_pagesizes;
  //unsigned int pagesizes[MAX_PAGESIZES];
  unsigned int virt_addr_length;
  unsigned int phys_addr_length;
  unsigned int tlblevels;
  //unsigned int I_TLB_Size[MAX_TLBLEVELS][MAX_PAGESIZES];
  //unsigned int I_TLB_Sets[MAX_TLBLEVELS][MAX_PAGESIZES];
  //unsigned int D_TLB_Size[MAX_TLBLEVELS][MAX_PAGESIZES];
  //unsigned int D_TLB_Sets[MAX_TLBLEVELS][MAX_PAGESIZES];
  //unsigned int U_TLB_Size[MAX_TLBLEVELS][MAX_PAGESIZES];
  //unsigned int U_TLB_Sets[MAX_TLBLEVELS][MAX_PAGESIZES];
  unsigned int TLB_unified;
  unsigned int TLB_size;
  unsigned int TLB_DLsize;
  unsigned int TLB_ILsize;
  unsigned int Cacheflushsize;
  unsigned int family,model,variant,revision;
  unsigned long int clockrate;
} arm_cpu_info_t;

/**
 * check if Performance Monitor Registers are accessible in User-Mode -> Check User Enable Register (PMUSERENR.EN)
 */
//int has_rdtsc();
int is_pmuserenr();

/**
 * measures latency of the timestampcounter
 * @return latency in cycles, -1 if not available
 */
//int get_rdtsc_latency();

/**
 * measures latency of overflow-detection (cmp)
 * @return latency in cycles, -1 if not available
 */

/**
 * measures latency of overflow-detection (cmp + count)
 * @return latency in cycles, -1 if not available
 */

 extern void read_hw_register();

/* 
 * The following functions are architecture specific
 */
 
 /**
  * basic information about cpus
  * TODO add cpu parameter
  */

 extern int get_cpu_variant();
 extern int get_cpu_revision();

