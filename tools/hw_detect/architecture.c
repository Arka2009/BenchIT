/**
* @file architecture.c
*  implements the commandline interface of hardware detection
*  calls architecture specific implementations
*
* Author: Daniel Molka (daniel.molka@zih.tu-dresden.de)
*/

#include <stdlib.h>
#include <unistd.h>

#include "cpu.h"
#include "properties.h"
#if ((defined (__ARM__))||(defined (__ARM))||(defined (ARM))||(defined (__ARMv7__))||(defined (__ARMv7))||(defined (ARMv7)))
#include "arm.h"
#endif

/**
 * display usage information
 */
static void usage()
{
     printf("usage: cpuinfo [option [arg]] [-cpu <ID>]\n");
     printf("options:\n");
     printf("  --help:                  this help screen\n");
     /*TODO --info <cmd> with further help*/
     printf("  --all:                   System summary\n");
     printf("  cpu_name:                Name of the CPU\n");
     printf("  cpu_vendor:              Vendor of the CPU\n");
     printf("  cpu_codename:            Codename of the CPU\n");
     printf("  cpu_isa:                 Instruction Set of the CPU\n");
     printf("  cpu_family:              Family of the CPU\n");
     printf("  cpu_model:               Model of the CPU\n");
     printf("  cpu_stepping:            Stepping of the CPU\n");
     printf("  cpu_gate_length:         manufacturing process in nm\n");
     printf("  cpu_features:            ISA extensions of the CPU\n");
     printf("  cpu_lwp:            		lightweight profiling support of the CPU\n");
     printf("  cpu_clockrate:           Clockrate of the CPU\n");
     printf("  cpu_clockrate_no_check:  Clockrate of the CPU (allows use of unreliable sources)\n");
     printf("  num_cpus:                Number of CPUs in the System\n");
     printf("  frequency_scaling:       supported frequencies and governor\n");
     printf("  timestamp:               returns a timestamp from internal counter register\n");
     printf("  get_cpu_id:              ID of the CPU the programm is currently running on\n");
     printf("  get_core_id:             ID of the core the programm is currently running on\n");
     printf("  num_packages:            Number of Packages (Sockets) in the System\n");
     printf("  get_package_id:          ID of the physical Packages the programm is currently running on\n");
     printf("  num_numa_nodes:          Number of NUMA Nodes in the System (1 -> UMA)\n");
     printf("  get_numa node :          NUMA Node the programm is currently running on\n");
     printf("  num_cores_per_package:   Number of Cores in a Package  (>1 -> Multicore)\n");
     printf("  num_threads_per_core:    Number of Threads per Core    (>1 -> SMT support)\n");
     printf("  num_threads_per_package: Number of Threads per Package (>1 -> SMT or Multicore)\n");
     printf("  num_caches:              Number of Caches in the CPU (per Core)\n");
     printf("  cache_info <ID>:         Type of the Cache (0 <= ID < num_caches)\n");
     printf("  num_tlbs:                Number of TLBs in the CPU (per Core)\n");
     printf("  tlb_info <ID>:           Type of the TLB (0 <= ID < num_tlbs)\n");
     printf("  physical_address_length  supported physical address length\n");
     printf("  virtual_address_length   supported virtual address length\n");
     printf("  pagesizes                supported page sizes\n");
	 printf("  memsize                  Amount of memory in the system\n");     
     printf("-cpu <ID>:\n");
     printf("  run on specific CPU: 0 <= ID < number of CPUs\n");
}

/**
 * list information about a certain CPU
 */
static void show_cpu_info(int i)
{
   unsigned long long res;
   long long size;
   int j,num;
   char output[_HW_DETECT_MAX_OUTPUT];
   char *pos,*old,*tmp;

   if (i==-1) printf("CPU properties:\n");
   else printf("CPU%i:\n",i);

   res=get_core_id(i);
   if (res!=-1) printf("  Core ID:          %llu\n",res);
   else printf("  Core ID:          n/a\n");
   res=get_pkg(i);
   if (res!=-1) printf("  Physical Package: %llu\n",res);
   else printf("  Physical Package: n/a\n");
   res=num_numa_nodes();
   if ((res!=-1)&&(res!=0)&&(res!=1))
   {
     res=get_numa_node(i);
     if (res!=-1) printf("  NUMA Node:        %llu\n",res);
     else printf("  NUMA Node:        n/a\n");
   }

   strncpy(output,"n/a",sizeof(output));get_cpu_vendor(output,sizeof(output));printf("  Vendor:           %s\n",output);
   strncpy(output,"n/a",sizeof(output));get_cpu_name(output,sizeof(output));printf("  Name:             %s\n",output);

   #if ((defined (__ARM__))||(defined (__ARM))||(defined (ARM))||(defined (__ARMv7__))||(defined (__ARMv7))||(defined (ARMv7)))
   get_cpu_family(output, sizeof(output));
   printf("  Model:            Family: %s, ",output);
   get_cpu_model(output, sizeof(output));
   printf("Model: %s, ",output);
   get_cpu_stepping(output, sizeof(output));
   printf("Stepping: %s\n",output);
   #else
   res=get_cpu_family();
   if (res!=-1) printf("  Model:            Family: %llu, ",res);
   else printf("  Model:            Family: n/a, ");
   res=get_cpu_model();
   if (res!=-1) printf("Model: %llu, ",res);
   else printf("Model: n/a, ");
   res=get_cpu_stepping();
   if (res!=-1) printf("Stepping: %llu\n",res);
   else printf("Stepping: n/a\n");
   #endif
   res=get_cpu_clockrate(1,i);
   if (res!=0) printf("  Clockrate:        %llu MHz\n",res/1000000);
   else
   {
      res=get_cpu_clockrate(0,i);
      if (res!=0) printf("  Clockrate:        %llu MHz (Warning: estimated using unreliable source)\n",res/1000000);
      else printf("  Clockrate:        n/a\n");
   }

   res=supported_frequencies(i,output,sizeof(output));
   if (res!=-1)
   {
     printf("  Supported Freqs:  %s",output);
     res=scaling_governor(i,output,sizeof(output));
     if (res!=-1) printf(", Governor: %s",output);
     res=scaling_driver(i,output,sizeof(output));
     if (res!=-1) printf(", Driver: %s",output);
     printf("\n");
   }

   strncpy(output,"n/a",sizeof(output));get_cpu_codename(output,sizeof(output));printf("  Codename:         %s\n",output);
   res=get_cpu_gate_length();
   if (res!=-1) printf("  Technology(ITRS): %llu nm\n",res);
   else printf("  Technology(ITRS): n/a\n");

   strncpy(output,"n/a",sizeof(output));get_cpu_isa_extensions(output,sizeof(output));
   printf("  ISA extensions:   ");
   tmp=output;pos=tmp;
   do
   {
     old=pos-1;
     pos=strstr(pos," ");
     if ((((pos!=NULL)&&(strstr(pos,")")<strstr(pos,"(")))||((pos!=NULL)&&(strstr(pos,")")!=NULL)&&(strstr(pos,"(")==NULL))) && (strstr(pos,")")-tmp>70))
     {
        *old='\0';
        printf("%s\n",tmp);
        tmp=old+1;
        if (strlen(tmp)>0) printf("                    ");
     }
     if ((pos!=NULL)&&(pos-tmp>70))
     {
        *pos='\0';pos++;
        printf("%s\n",tmp);
        tmp=pos;
        if (strlen(tmp)>0) printf("                    ");
     }
     else if ((pos==NULL)||((pos!=NULL)&&(strlen(pos)==1)))
     {
        printf("%s\n",tmp);
        if (pos!=NULL) pos++;
     }
     else pos++;
   }
   while ((pos!=NULL)&&(*pos!='\0'));
   res=get_phys_address_length();
   if (res!=-1) printf("  Phys Addr Length: %llu Bit\n",res);
   else printf("  Phys Addr Length: n/a\n");
   res=get_virt_address_length();
   if (res!=-1) printf("  Virt Addr Length: %llu Bit\n",res);
   else printf("  Virt Addr Length: n/a\n");

   num=num_pagesizes();
   if (num!=-1)
   {
    printf("  Pagesizes:        ");
    for(j=0;j<num;j++)
    {
     size=pagesize(j);
     if (size!=-1)
     {
       if (size>=1073741824)printf("%lliG ",size>>30);
       else if (size>1048576)printf("%lliM ",size>>20);
       else if (size>1024)printf("%lliK ",size>>10);
       else printf("%llu Byte ",res);
     }
    }
    printf("\n");
   }

   res=num_caches(i);
   if (res!=-1)
   {
     printf("  Caches:\n");
     for (j=0;j<res;j++)
     {
        snprintf(output,sizeof(output),"n/a");
        if (cache_info(i,j,output,sizeof(output))!=-1) printf("   - %s\n",output);
     }
   }
   res=num_tlbs(i);
   if (res!=-1)
   {
     printf("  TLBs:\n");
     for (j=0;j<res;j++)
     {
        snprintf(output,sizeof(output),"n/a");
        if (tlb_info(i,j,output,sizeof(output))!=-1) printf("   - %s\n",output);
     }
   }
   strncpy(output,"n/a",sizeof(output));
   #if (!((defined (__ARM__))||(defined (__ARM))||(defined (ARM))||(defined (__ARMv7__))||(defined (__ARMv7))||(defined (ARMv7))))
   get_cpu_lwp(output,sizeof(output));
   printf("  LWP support: %s\n",output);
   #endif
}

int main(int argc, char** argv)
{
  char output[_HW_DETECT_MAX_OUTPUT];
  strcpy((char*)&output,"n/a");
  unsigned long long res;
  int cpu=-1,err,i, num;
  long long size;  
  char *endptr;

  #if ((defined (__ARM__))||(defined (__ARM))||(defined (ARM))||(defined (__ARMv7__))||(defined (__ARMv7))||(defined (ARMv7)))
  read_hw_register();
  #endif

  //printf("output-size: %lu\n",sizeof(output));

  /* system summary */
  if ((argc==1)||(!strcmp(argv[1],"--all")))
  {
     get_architecture(output,sizeof(output));printf("Architecture:   %s\n",output);
     printf("Number of (logical) CPUs: %i\n",num_cpus());
     res=num_packages();
     if (res!=-1) printf(" - Number of packages (sockets):   %llu\n",res);
     else printf(" - Number of packages (sockets):   n/a\n");
     res=num_cores_per_package();
     if (res!=-1) printf(" - Number of cores per package:    %llu\n",res);
     else printf(" - Number of cores per package:    n/a\n");
     res=num_threads_per_core();
     if (res!=-1) printf(" - Number of threads per core:     %llu\n",res);
     else printf(" - Number of threads per core:     n/a\n");
     res=num_threads_per_package();
     if (res!=-1) printf(" - Number of threads per package:  %llu\n",res);
     else printf(" - Number of threads per package:  n/a\n");
     res=num_numa_nodes();
     if ((res!=-1)&&(res!=0)&&(res!=1)) printf(" - Number of NUMA Nodes:           %llu\n",res);
     #if defined(AFFINITY)
     for (i=0;i<num_cpus();i++)
     {
        err=set_cpu(i);
        if(err==-2) printf("CPU%i: not allowed to run on\n",i);
        else if (err) printf("CPU%i: could not set affinity\n",i);
        else show_cpu_info(i);
        restore_affinity();
     }
     #else
       if (num_cpus()>1) printf("CPU affinity not available, running on any CPU\n");
       show_cpu_info(cpu);
     #endif
     return 0;
  }

  if (!strcmp(argv[1],"--help"))
  {
     usage();
     return 0;
  }

  if (!strcmp(argv[1], "arch_short"))
  {
	get_cpu_name(output,sizeof(output));

	for(i = 0; i < ARCH_SHORT_COUNT; i++)
	{
		if((strstr(output, archshrt_data[i].name) != NULL) && archshrt_data[i].cores_per_pkg == num_cores_per_package())
		{
			puts(archshrt_data[i].arch_short);
			return 0;
		}
	}
	puts("unknown");
	return -1;
  }
  
  if ((argc==4)&&(!(strcmp(argv[2],"-cpu"))))
  {
    cpu=(int)strtol(argv[3],&endptr,10);
    if ((cpu<0)||(cpu>num_cpus()-1)||((*endptr)!='\0'))
    {
      printf("Error: unknown CPU: %s\n",argv[3]);
      return -1;
    }
    err=set_cpu(cpu);
    if(err)
    {
       printf("Error: CPU affinity not available\n");
       return -1;
    }
  }

  if ((argc==5)&&(!(strcmp(argv[3],"-cpu"))))
  {
    cpu=(int)strtol(argv[4],&endptr,10);
    if ((cpu<0)||(cpu>num_cpus()-1)||((*endptr)!='\0'))
    {
      printf("Error: unknown CPU: %s\n",argv[4]);
      return -1;
    }
    err=set_cpu(cpu);
    if(err)
    {
       printf("Error: CPU affinity not available\n");
       return -1;
    }
  }

  /*TODO other illegal input */
  if (((argc>4)&&(!(strcmp(argv[2],"-cpu"))))||((argc>5)&&(!(strcmp(argv[3],"-cpu"))))||(argc>6))
  {
     printf("Error: illegal command\n");
     usage();
     return -1;
  }

  if(!strcmp(argv[1],"cpu_isa"))
  {
     get_architecture(output,sizeof(output));
     printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"cpu_vendor"))
  {
     get_cpu_vendor(output,sizeof(output));
     printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"cpu_name"))
  {
     get_cpu_name(output,sizeof(output));
     printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"cpu_codename"))
  {
     get_cpu_codename(output,sizeof(output));
     printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"cpu_family"))
  {
     #if ((defined (__ARM__))||(defined (__ARM))||(defined (ARM))||(defined (__ARMv7__))||(defined (__ARMv7))||(defined (ARMv7)))
     get_cpu_family(output, sizeof(output));
     printf("%s\n",output);
     #else
     res=get_cpu_family();
     if (res!=-1) printf("%llu\n",res);
     else printf("%s\n",output);
     #endif
     return 0;
  }

  if(!strcmp(argv[1],"cpu_model"))
  {
     #if ((defined (__ARM__))||(defined (__ARM))||(defined (ARM))||(defined (__ARMv7__))||(defined (__ARMv7))||(defined (ARMv7)))
     get_cpu_model(output, sizeof(output));
     printf("%s\n",output);
     #else
     res=get_cpu_model();
     if (res!=-1) printf("%llu\n",res);
     else printf("%s\n",output);
     #endif
     return 0;
  }

  if(!strcmp(argv[1],"cpu_stepping"))
  {
     #if ((defined (__ARM__))||(defined (__ARM))||(defined (ARM))||(defined (__ARMv7__))||(defined (__ARMv7))||(defined (ARMv7)))
     get_cpu_stepping(output, sizeof(output));
     printf("%s\n",output);
     #else
     res=get_cpu_stepping();
     if (res!=-1) printf("%llu\n",res);
     else printf("%s\n",output);
     #endif
     return 0;
  }

  if(!strcmp(argv[1],"cpu_gate_length"))
  {
     res=get_cpu_gate_length();
     if (res!=-1) printf("%llu\n",res);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"cpu_features"))
  {
     get_cpu_isa_extensions(output,sizeof(output));
     printf("%s\n",output);
     return 0;
  }

  #if (!((defined (__ARM__))||(defined (__ARM))||(defined (ARM))||(defined (__ARMv7__))||(defined (__ARMv7))||(defined (ARMv7))))
  if(!strcmp(argv[1],"cpu_lwp"))
  {
	 strncpy(output,"n/a",sizeof(output));
	 get_cpu_lwp(output,sizeof(output));
	 printf("  LWP support: %s\n",output);
     return 0;
  }
  #endif

  if(!strcmp(argv[1],"cpu_clockrate"))
  {
     res=get_cpu_clockrate(1,cpu);
     if (res!=0) printf("%llu\n",res);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"cpu_clockrate_no_check"))
  {
     res=get_cpu_clockrate(0,cpu);
     if (res!=0) printf("%llu\n",res);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"frequency_scaling"))
  {
     res=supported_frequencies(cpu,output,sizeof(output));
     if (res!=-1)
     {
       printf("Supported Frequencies: %s",output);
       res=scaling_governor(cpu,output,sizeof(output));
       if (res!=-1) printf(", Governor: %s",output);
       res=scaling_driver(cpu,output,sizeof(output));
       if (res!=-1) printf(", Driver: %s",output);
       printf("\n");
     }
     else printf("n/a\n");
     return 0;
  }

  if(!strcmp(argv[1],"timestamp"))
  {
     res=timestamp();
     if (res!=-1) printf("%llu\n",res);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"get_cpu_id"))
  {
     res=get_cpu();
     if (res!=-1) printf("%llu\n",res);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"get_core_id"))
  {
     res=get_core_id(cpu);
     if (res!=-1) printf("%llu\n",res);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"get_package_id"))
  {
     res=get_pkg(cpu);
     if (res!=-1) printf("%llu\n",res);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"num_packages"))
  {
     res=num_packages();
     if (res!=-1) printf("%llu\n",res);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"num_numa_nodes"))
  {
     res=num_numa_nodes();
     if ((res!=-1)&&(res!=0)) printf("%llu\n",res);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"get_numa_node"))
  {
     res=get_numa_node(cpu);
     if (res!=-1) printf("%llu\n",res);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"num_cores_per_package"))
  {
     res=num_cores_per_package();
     if (res!=-1) printf("%llu\n",res);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"num_threads_per_core"))
  {
     res=num_threads_per_core();
     if (res!=-1) printf("%llu\n",res);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"num_threads_per_package"))
  {
     res=num_threads_per_package();
     if (res!=-1) printf("%llu\n",res);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"num_caches"))
  {
     res=num_caches(cpu);
     if (res!=-1) printf("%llu\n",res);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"cache_info"))
  {
     res=cache_info(cpu,atoi(argv[2]),output,sizeof(output));
     if (res!=-1) printf("%s\n",output);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"num_tlbs"))
  {
     res=num_tlbs(cpu);
     if (res!=-1) printf("%llu\n",res);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"tlb_info"))
  {
     res=tlb_info(cpu,atoi(argv[2]),output,sizeof(output));
     if (res!=-1) printf("%s\n",output);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"physical_address_length"))
  {
     res=get_phys_address_length();
     if (res!=-1) printf("%llu Bit\n",res);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"virtual_address_length"))
  {
     res=get_virt_address_length();
     if (res!=-1) printf("%llu Bit\n",res);
     else printf("%s\n",output);
     return 0;
  }

  if(!strcmp(argv[1],"pagesizes"))
  {
     num=num_pagesizes();
     if (num!=-1)
     {
      for(i=0;i<num;i++)
      {
       size=pagesize(i);
       if (size!=-1)
       {
         if (size>=1073741824)printf("%lliG ",size>>30);
         else if (size>1048576)printf("%lliM ",size>>20);
         else if (size>1024)printf("%lliK ",size>>10);
         else printf("%lli Byte ",size);
       }
      }
      printf("\n");
     }
     return 0;
  }
  
  if(!strcmp(argv[1], "memsize"))
  {
    if ((sysconf(_SC_PHYS_PAGES)!=-1) && (sysconf(_SC_PAGESIZE)!=-1)) 
    {
    	printf("%llu\n", (unsigned long long)sysconf(_SC_PHYS_PAGES) * sysconf(_SC_PAGESIZE));
    	return 0;
    }  	
    else
    {
    	printf("n/a\n");
    	return -1;
    }
  }
  
  if(!strcmp(argv[1], "num_cpus"))
  {
  	num = num_cpus();
  	if(num != -1)
  	{
  		printf("%d\n", num_cpus());
  		return 0;
  	}
  	else
  	{
  		printf("n/a\n");
  		return -1;
  	}
  }  

  if ((argc==3)&&(!strcmp(argv[1],"-cpu")))
  {
   cpu=(int)strtol((argv[2]),&endptr,10);
   if ((cpu>=0)&&(cpu<num_cpus())&&(*endptr=='\0'))
   {
     err=set_cpu(cpu);

     if(err)
     {
        printf("Error: CPU affinity not available\n");
        return -1;
     }

     show_cpu_info(cpu);
     return 0;
   }
  }

  printf("Error: unknown option: %s\n",argv[1]);
  usage();
  return -1;
}

