/**
* @file generic.c
*  fallback implementations of the hardware detection using information provided by the opperating system
*  used for unsupported architectures, in case of errors in the architecture specific detection, and if
*  there is no architecture specific method to implement a function.
* 
* Author: Daniel Molka (daniel.molka@zih.tu-dresden.de)
*/
#include "cpu.h"
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <dirent.h>
#include "properties.h"
#include "regex.h"

/* buffer for some generic implementations */
// TODO remove global variables to allow thread safe execution of detection
static char output[_HW_DETECT_MAX_OUTPUT];
static char path[_HW_DETECT_MAX_OUTPUT];

#if (defined(linux) || defined(__linux__)) && defined (AFFINITY)
/* needed for restore_affinity function */
static cpu_set_t orig_cpuset;
static unsigned long long orig_cpu_mask;
static int restore=0;
#endif

/*
 * internally used routines
 */

/**
 * list element for counting unique package_ids, core_ids etc.
 */
typedef struct id_element {
	int id, count;
	struct id_element *next;
} id_le;

static void insert_element(int id, id_le **list)
{
	id_le *new_element, *ptr;
	
	new_element = malloc(sizeof(id_le));
	new_element->id = id;
	new_element->count = 1;
	new_element->next = NULL;
	
	if(*list == NULL) {
		*list = new_element;
	}
	else {
		ptr = *list;
		while(ptr->next != NULL) {
			ptr = ptr->next;
		}
		ptr->next = new_element;
	}
}

static void free_id_list(id_le **list)
{
	id_le * ptr, *tofree;
	ptr = *list;
	
	if(ptr != NULL)
	{
		while(ptr != NULL) {
			tofree = ptr;
			ptr = ptr->next;
			free(tofree);			 
		}
	}
	*list = NULL;		
}

static int id_total_count(id_le *list)
{
	int c = 0;
	if(list != NULL) {
		c++;
		while(list->next != NULL) {
			c++;
			list = list->next;
		}
	}
	return c;
}

/* not used yet
static int get_id_count(int id, id_le *list)
{
	if(list == NULL)
		return 0;
		
	while(list->next != NULL && list->id != id) list = list->next;
	if(list->id == id)
		return list->count;
	else
		return 0;
}
*/

static void inc_id_count(int id, id_le **list)
{
	id_le *ptr;
	ptr = *list;
	
	if(ptr == NULL) 
		insert_element(id, list);
	else
	{
		while(ptr->next != NULL && ptr->id != id) ptr = ptr->next;
		if(ptr->id == id)
			ptr->count++;
		else
			insert_element(id, list);
	}
}

/**
 * reads a certain data element from /proc/cpuinfo 
 */
static int get_proc_cpuinfo_data(char *element, char *result, int proc);

static int match_str(char * mstr, char * pattern, int * n)
{
	char * pend;
	int l;
	if (mstr == NULL || n == NULL || pattern == NULL)
		return 0;
	l = strlen(pattern);
	if(!strncmp(mstr, pattern, l)) {
		*n = strtol(mstr+l, &pend, 10);
		if(pend == NULL)
			return 0;
		//check if there are any following non-number characters:
		if(strlen(pend) > 0)
			return 0;
	}
	else return 0;

	return -1;
}

/*
 * Wraps glibc regular expression pattern matching
 */
static int regex_match(const char *str, const char *pattern) {
	int status;
	regex_t re;

	if(regcomp(&re, pattern, REG_NOSUB) != 0) {
		return 0;
	}
	status = regexec(&re, str, (size_t)0, NULL, 0);

	regfree(&re);
 
	if(status != 0) {
		return 0;
	}
	return 1;
} 

/**
 * reads the file from path into buffer
 */
static int read_file(char * path, char * buffer, int bsize)
{
	FILE * f;
	long size;

	if((path == NULL) || (buffer == NULL)) return 0;
	memset(buffer, 0, bsize); bsize--;
	if((f=fopen(path, "rb")) != NULL)
	{
		fseek(f, 0, SEEK_END);
		size=ftell(f);
		rewind(f);
		fread(buffer, 1, (bsize < size) ? bsize : size, f);
		fclose(f);
	}
	else return 0;

	while(*buffer++) if(*buffer == '\n') *buffer = 0;

	return -1;
}

/* 
 * architecture independent fallback implementations 
 */

 /**
  * Determine number of CPUs in System
  */
int num_cpus()
{
   struct dirent **namelist;
   int ndir, c, num=0, m;
   char tmppath[_HW_DETECT_MAX_OUTPUT];
   char buf[20];

   /* try sysconf online cpus */
   num=sysconf(_SC_NPROCESSORS_ONLN);

   /* extract information from sysfs */
   if (num<=0) { 
     strcpy(path, "/sys/devices/system/cpu/");
     ndir = scandir(path, &namelist, 0, 0);
     if(ndir >= 0)
     {
	     c = 0;
	     while(ndir--) {
		     if(match_str(namelist[ndir]->d_name, "cpu", &m)) {
			strncpy(tmppath, path,sizeof(tmppath));
			snprintf(buf, sizeof(buf),"cpu%i", m);
			strcat(tmppath, buf);
			strcat(tmppath, "/online");
			read_file(tmppath, output, sizeof(output));
			if (strncmp(output,"0",1)!=0) {
				c++;
			}
		     }
		     free(namelist[ndir]);
	     }
	     free(namelist);
	     if(c > 0) num = c;
	     else num = -1;
     }
   }

   /*TODO proc/cpuinfo*/

   /* try sysconf configured cpus */
   if (num<=0) num=sysconf(_SC_NPROCESSORS_CONF);

   /*assume 1 if all detection methods fail*/
   if (num<1) num=1;

   return num;
}


void generic_get_architecture(char* arch)
{
	get_proc_cpuinfo_data("arch", arch, 0);
}

/** 
 *sets affinity to a certain cpu 
 */
int set_cpu(int cpu)
{
#if (defined(linux) || defined(__linux__)) && defined (AFFINITY)
    cpu_set_t cpuset;
    unsigned long long mask;
    int err=-1,i;

    /* test if the CPU is allowed to be used (sched_setaffinity otherwise would overwrite taskset settings) */
    err=sched_getaffinity(0, sizeof(cpu_set_t), &orig_cpuset);
    if ((!err)&&(!CPU_ISSET(cpu,&orig_cpuset))) return -2;

    CPU_ZERO(&cpuset);
    CPU_SET(cpu,&cpuset);
    err=sched_setaffinity(0, sizeof(cpu_set_t), &cpuset);
    if (!err) {restore=1;err=sched_getaffinity(0, sizeof(cpu_set_t), &cpuset);}

    if (!CPU_ISSET(cpu,&cpuset)) err=-1;
    for (i=0;i<num_cpus();i++) if ((i!=cpu)&&(CPU_ISSET(i,&cpuset))) err=-1;

    /* if affinity functions are not available and in case of an error try fallback implementation without macros */
    if(err)
    {
      /* test if the CPU is allowed to be used (sched_setaffinity otherwise would overwrite taskset settings) */
      err=sched_getaffinity(0, sizeof(unsigned long long), (cpu_set_t*) &orig_cpu_mask);
      if ((!err)&&(!(orig_cpu_mask&(1<<cpu)))) return -2;

      mask=(1<<cpu);
      err=sched_setaffinity(0, sizeof(unsigned long long), (cpu_set_t*) &mask);
      if (!err) {restore=2;err=sched_getaffinity(0, sizeof(unsigned long long), (cpu_set_t*) &mask);}
      if (mask!=(1<<cpu)) err=-1;
    }

    return err;
#else
  return -1;
#endif
}

/** 
 * restores original affinity after changing with set_cpu() 
 */
int restore_affinity()
{
  #if (defined(linux) || defined(__linux__)) && defined (AFFINITY)
    if (restore==1) sched_setaffinity(0, sizeof(cpu_set_t), &orig_cpuset);
    if (restore==2) sched_setaffinity(0, sizeof(unsigned long long), (cpu_set_t*) &orig_cpu_mask);
    restore=0;
  #endif
  return 0;
}

/** 
 * tries to determine on which cpu the program is being run 
 */
int get_cpu()
{
  int cpu=-1;
    #if (defined(linux) || defined(__linux__)) && defined (SCHED_GETCPU)
      cpu = sched_getcpu();
    #endif
  return cpu;
}

/** 
 * tries to determine the physical package, a cpu belongs to
 */
int get_pkg(int cpu)
{
	int pkg=0;
	char buffer[_HW_DETECT_MAX_OUTPUT];

	if ((num_cpus()==1)||(num_packages()==1)) return 0;

	if (cpu==-1) cpu=get_cpu();
	if (cpu!=-1)
	{

		sprintf(path, "/sys/devices/system/cpu/cpu%i/topology/physical_package_id", cpu);

		if(!read_file(path, buffer, sizeof(buffer)))
			pkg = -1;
		else
			pkg=atoi(buffer);

		if (pkg==-1)
		{
			/* get the physical package id from /proc/cpuinfo */
			if(!get_proc_cpuinfo_data("physical id", buffer, cpu)) pkg = atoi(buffer);
 			/* if the number of cpus equals the number of packages assume pkg_id = cpu_id*/
			else if (num_cpus()==num_packages()) pkg = cpu;
			/* if there is only one core per package assume pkg_id = core_id */
			else if (num_cores_per_package()==1) pkg = get_core_id(cpu);
			/* if the number of packages equals the number of numa nodes assume pkg_id = numa node */
			else if (num_numa_nodes()==num_packages()) pkg = get_numa_node(cpu);

			/* NOTE pkg_id in UMA Systems with multiple sockets and more than 1 Core per socket can't be determined
			without correct topology information in sysfs*/
		}
	}
	return pkg;
}

/** 
 * tries to determine the core ID, a cpu belongs to
 */
int get_core_id(int cpu)
{
  int core=-1;
  char buffer[10];

  if (num_cpus()==1) return 0;

  if (cpu==-1) cpu=get_cpu();
  if (cpu!=-1)
  {
     sprintf(path, "/sys/devices/system/cpu/cpu%i/topology/core_id", cpu);

     if(!read_file(path, buffer, sizeof(buffer)))
	     core = -1;
     else
	     core=atoi(buffer); 
  }
  if (core==-1)
  {
    /* if each package contains only one cpu assume core_id = package_id = cpu_id */
    if (num_cores_per_package()==1) core = 0;

    /* NOTE core_id can't be determined without correct topology information in sysfs if there are multiple cores per package 
       TODO /proc/cpuinfo */
  }
  return core;
}

/**
 * determines how many NUMA Nodes are in the system
 */
int num_numa_nodes()
{
   struct dirent **namelist;
   int ndir, c, m;

   strcpy(path, "/sys/devices/system/node/");

   ndir = scandir(path, &namelist, 0, 0);
   if(ndir >= 0)
   {
	c = 0;
	while(ndir--) {
		if(match_str(namelist[ndir]->d_name, "node", &m)) c++;
		free(namelist[ndir]);
	}
	free(namelist);
	if(c > 0) return c;
   }
   return -1;
}

/** 
 * tries to determine the NUMA Node, a cpu belongs to
 */
int get_numa_node(int cpu)
{
  int node=-1, ndir, m;
  struct dirent **namelist;
  struct stat statbuf;

  if (cpu==-1) cpu=get_cpu();
  if (cpu!=-1)
  {
     strcpy(path, "/sys/devices/system/node/");
     ndir = scandir(path, &namelist, 0, 0);
     if (ndir >= 0)
     {
	     while(ndir--)
	     {
		     if(match_str(namelist[ndir]->d_name, "node", &m))
		     {
			     sprintf(path, "/sys/devices/system/node/node%i/cpu%i", m, cpu);
			     if(!stat(path, &statbuf)) {
				     node = m;
			     }
		     }
		     free(namelist[ndir]);
	     }
	     free(namelist);
     }
  }

  return node;
}

 /**
  * frequency scaling
  */
int supported_frequencies(int cpu, char* output, size_t len)
{
  FILE *f;
  int *freqs = NULL;
  int i, in, found=0;
  char buffer[14];

  if (len<1) return -1;
  if (cpu==-1) cpu=get_cpu();  
  if (cpu!=-1)
  {
     snprintf(path,_HW_DETECT_MAX_OUTPUT, "/sys/devices/system/cpu/cpu%i/cpufreq/scaling_available_frequencies", cpu);

    output[0] = '\0';
    if((f=fopen(path,"r")) != NULL)
    {
      i=0;
      while(fscanf(f, "%d", &in) != EOF)
      {
        freqs=realloc(freqs, (i+1) * sizeof(int));
	freqs[i] = in;
	i++;
      }

      for (i--; i >= 0; i--)
      {
         freqs[i] /= 1000;
	 snprintf(buffer,14, "%d MHz", freqs[i]);
	 if(i > 0) strcat(buffer, " ");
	 strncat(output, buffer,(len-strlen(output))-1);
      }
      free(freqs);
      
    }
    else {
      snprintf(path,_HW_DETECT_MAX_OUTPUT, "/sys/devices/system/cpu/cpu%i/cpufreq/scaling_min_freq", cpu);
      if(read_file(path, buffer, sizeof(buffer)))
      {
        in = atoi(buffer);
        in /= 1000;
        found = 1;
        snprintf(buffer,14, "%d MHz ", in);
        strncat(output, buffer,(len-strlen(output))-1);
      }
      sprintf(path, "/sys/devices/system/cpu/cpu%i/cpufreq/scaling_max_freq", cpu);
      if(read_file(path, buffer, sizeof(buffer)))
      {
        in = atoi(buffer);
	in /= 1000;
	found = 1;
	snprintf(buffer,14, "%d MHz", in);
	strncat(output, buffer,(len-strlen(output))-1);
      }

      if(!found) return -1;
    }

    return 0;
  }
  else return -1;
}

 int scaling_governor(int cpu, char* output, size_t len)
 {
  if (cpu==-1) cpu=get_cpu();
  if (cpu!=-1)
  {
     snprintf(path,sizeof(path), "/sys/devices/system/cpu/cpu%d/cpufreq/scaling_governor", cpu);
     if(!read_file(path, output, len)) return -1;

     return 0;
  }
  else return -1;
 }

 int scaling_driver(int cpu, char* output, size_t len)
 {
  if (cpu==-1) cpu=get_cpu();
  if (cpu!=-1)
  {
     snprintf(path,sizeof(path), "/sys/devices/system/cpu/cpu%d/cpufreq/scaling_driver", cpu);
     if(!read_file(path, output, len)) return -1;

     return 0;
  }
  else return -1;
 }

 /*
  * generic implementations for architecture dependent functions
  */


 /**
  * basic information about cpus
  */
  
int generic_get_cpu_codename(char* name, size_t len)
{
	int i;
	char tmpname[_HW_DETECT_MAX_OUTPUT];
	#if ((defined (__ARM__))||(defined (__ARM))||(defined (ARM))||(defined (__ARMv7__))||(defined (__ARMv7))||(defined (ARMv7)))
	char family[_HW_DETECT_MAX_OUTPUT];
	char model[_HW_DETECT_MAX_OUTPUT];
	#endif	
	
	#if (defined (__ARCH_UNKNOWN))
		generic_get_cpu_name(tmpname,len);
	#else
		get_cpu_name(tmpname,len);		
	#endif

	for(i=0; i < CPU_DATA_COUNT; i++)
	{
	//TODO: Add Support for ARM CPUs (e.g. Tegra - Kal-El, Wayne, Cortex-A15 = Eagle)
		#if ((defined (__ARM__))||(defined (__ARM))||(defined (ARM))||(defined (__ARMv7__))||(defined (__ARMv7))||(defined (ARMv7)))
		get_cpu_family(family, sizeof(family));
		get_cpu_model(model,sizeof(model));	
		strncpy(name, "unknown", len);
		break;
		#else
		if(regex_match(tmpname, cpu_data[i].name) && (get_cpu_family() == cpu_data[i].family) && (get_cpu_model() == cpu_data[i].model)) {
			strncpy(name, cpu_data[i].codename, len);
			break;
		}
		#endif
	}

	if (strlen(name) == 0)
	{
		snprintf(name,len,"n/a");
		return -1;
	}

	return 0;
}		

int get_cpu_codename(char *name, size_t len)
{
	return generic_get_cpu_codename(name,len);
}

// TODO size_t len parameter		
static int get_proc_cpuinfo_data(char *element, char *result, int proc)
{
	FILE *f;
	char buffer[_HW_DETECT_MAX_OUTPUT];
	int h, cur_proc = -1;

	if(!element || !result) return -1;

	if((f=fopen("/proc/cpuinfo", "r")) != NULL) {
		while(!feof(f)) {
			fgets(buffer, sizeof(buffer), f);
			if(!strncmp(buffer, "processor", 9)) {
				cur_proc = atoi(strstr(buffer, ":")+2);
			}		
			if(cur_proc == proc && !strncmp(buffer, element, strlen(element))) {
				strncpy(result, strstr(buffer, ":")+2,_HW_DETECT_MAX_OUTPUT);
				h=strlen(result)-1;
				if(result[h] == '\n') result[h] = '\0';
				fclose(f);
				return 0;
			}
		}
		fclose(f);
	}
	return -1;
}
  
int generic_get_cpu_vendor(char* vendor,size_t len)
{
	return get_proc_cpuinfo_data("vendor", vendor, 0);
}

int generic_get_cpu_name(char* name, size_t len) 
{
	return get_proc_cpuinfo_data("model name", name, 0);
}

int generic_get_cpu_family()
{
	char buffer[_HW_DETECT_MAX_OUTPUT];
	if(!get_proc_cpuinfo_data("cpu family", buffer, 0))
		return atoi(buffer);
	else if(!get_proc_cpuinfo_data("family", buffer, 0))
		return atoi(buffer);
	else
		return -1;	
}

int generic_get_cpu_model()
{
	char buffer[_HW_DETECT_MAX_OUTPUT];
	if(!get_proc_cpuinfo_data("model", buffer, 0))
		return atoi(buffer);
	else
		return -1;
}

int generic_get_cpu_stepping()
{
	char buffer[_HW_DETECT_MAX_OUTPUT];
	if(!get_proc_cpuinfo_data("stepping", buffer, 0))
		return atoi(buffer);
	else if(!get_proc_cpuinfo_data("revision", buffer, 0))
		return atoi(buffer);
	else
		return -1;
}

int generic_get_cpu_gate_length()
{
	int i, res = -1;
	char tmpname[_HW_DETECT_MAX_OUTPUT];
	#if ((defined (__ARM__))||(defined (__ARM))||(defined (ARM))||(defined (__ARMv7__))||(defined (__ARMv7))||(defined (ARMv7)))
	char family[_HW_DETECT_MAX_OUTPUT];
	char model[_HW_DETECT_MAX_OUTPUT];
	#endif

	get_cpu_name(tmpname,sizeof(tmpname));
	for(i=0; i < CPU_DATA_COUNT; i++)
	{
		//TODO: add gate length for ARM CPUs
		#if ((defined (__ARM__))||(defined (__ARM))||(defined (ARM))||(defined (__ARMv7__))||(defined (__ARMv7))||(defined (ARMv7)))
		get_cpu_family(family, sizeof(family));
		get_cpu_model(model,sizeof(model));	
		res = 0;
		#else
		if(regex_match(tmpname, cpu_data[i].name) && (get_cpu_family() == cpu_data[i].family) && (get_cpu_model() == cpu_data[i].model)) {
			res = cpu_data[i].node;
			break;
		}
		#endif
	}

	return res;
}

int get_cpu_gate_length()
{
	return generic_get_cpu_gate_length();
}

int feature_available(char* feature)
{
        char buffer[_HW_DETECT_MAX_OUTPUT];
        get_cpu_isa_extensions(buffer,sizeof(buffer));
        
        if (strstr(buffer,feature)!=NULL) return 1;
        else return 0;
}

 /**
  * additional features (e.g. SSE)
  */
 int generic_get_cpu_isa_extensions(char* features, size_t len){return -1;}  /*TODO /proc/cpuinfo */
 int generic_get_cpu_lwp(char* lwpfeatures, size_t len){return -1;}

unsigned long long generic_get_cpu_clockrate_proccpuinfo_fallback(int cpu)
{
	char buffer[_HW_DETECT_MAX_OUTPUT];
	if(!get_proc_cpuinfo_data("cpu MHz", buffer, cpu))
		return atoll(buffer)*1000000;
	else
		return 0;
}

 /**
  * read clockrate from sysfs
  * @param check ignored
  * @param cpu used to find accosiated directory in sysfs
  */
 unsigned long long generic_get_cpu_clockrate(int check, int cpu)
 {
   char tmp[_HW_DETECT_MAX_OUTPUT];
   unsigned long long in;
 
   if (cpu == -1) cpu=get_cpu();
   if (cpu == -1) return 0;

   memset(tmp, 0, sizeof(tmp));
   scaling_governor(cpu, tmp,sizeof(tmp));

   sprintf(path, "/sys/devices/system/cpu/cpu%i/cpufreq/", cpu);

   if ((!strcmp(tmp,"performance"))||(!strcmp(tmp,"powersave")))
   {
      strcpy(tmp, path); strcat(tmp, "scaling_cur_freq");
      if (!read_file(tmp, output, _HW_DETECT_MAX_OUTPUT)) {
		strcpy(tmp, path); strcat(tmp, "cpuinfo_cur_freq");
		if (!read_file(tmp, output, _HW_DETECT_MAX_OUTPUT))
			return generic_get_cpu_clockrate_proccpuinfo_fallback(cpu);
      }
   }
   else
   {
      strcpy(tmp, path); strcat(tmp, "scaling_max_freq");
      if (!read_file(tmp, output, _HW_DETECT_MAX_OUTPUT)) {
	 	strcpy(tmp, path); strcat(tmp, "cpuinfo_max_freq");
	 	if (!read_file(tmp, output, _HW_DETECT_MAX_OUTPUT))
	 		return generic_get_cpu_clockrate_proccpuinfo_fallback(cpu);
      }
   }
   in = atoll(output);
   in *= 1000;
   
   return in;
 }

 /**
  * returns a timestamp from cpu-internal counters (if available)
  */
 unsigned long long generic_timestamp()
 {
   struct timeval tv;

   if (gettimeofday(&tv,NULL)==0) return ((unsigned long long)tv.tv_sec)*1000000+tv.tv_usec;
   else return 0;
 }

 /**
  * number of caches (of one cpu)
  */
int generic_num_caches(int cpu)
{
  struct dirent **namelist;
  int ndir, c, m;

  if (cpu==-1) cpu=get_cpu();
  if (cpu==-1) return -1;

  sprintf(path, "/sys/devices/system/cpu/cpu%i/cache/", cpu);
  ndir = scandir(path, &namelist, 0, 0);
  if(ndir >= 0)
  {
	  c = 0;
	  while(ndir--) {
		  if(match_str(namelist[ndir]->d_name, "index", &m)) c++;
		  free(namelist[ndir]);
	  }
	  free(namelist);
	  if(c > 0) return c;
  }
  return -1;
}


int cpu_map_to_list(char * input, char * buffer, int bsize)
{
	int pos = 0;
	char * current;
	int cur_hex;
	char * tmp;
	char buf[20];
	
	if(input == NULL || buffer == NULL || bsize <= 0) return 0;

	tmp = malloc((strlen(input)+1) * sizeof(char));
	memcpy(tmp, input, strlen(input)+1);
	memset(buffer, 0, bsize);

	while(strlen(tmp))
	{
		current = &(tmp[strlen(tmp)-1]);
		if(*current != ',')
		{
			cur_hex = (int)strtol(current, NULL, 16);
			if (cur_hex&0x1) { sprintf(buf, "cpu%i ", pos); strcat(buffer, buf); }
			if (cur_hex&0x2) { sprintf(buf, "cpu%i ", pos+1); strcat(buffer, buf); }
			if (cur_hex&0x4) { sprintf(buf, "cpu%i ", pos+2); strcat(buffer, buf); }
			if (cur_hex&0x8) { sprintf(buf, "cpu%i ", pos+3); strcat(buffer, buf); }
			pos += 4;
		}
		*current = '\0';
	}

	return -1;
}


/**
 * information about the cache: level, associativity...
 */
int generic_cache_info(int cpu, int id, char* output, size_t len)
{
	char tmp[_HW_DETECT_MAX_OUTPUT], tmp2[_HW_DETECT_MAX_OUTPUT];
	char tmppath[_HW_DETECT_MAX_OUTPUT];
	struct stat statbuf;

	if (cpu==-1) cpu=get_cpu();
	if (cpu==-1) return -1;

	snprintf(path,sizeof(path), "/sys/devices/system/cpu/cpu%i/cache/index%i/", cpu, id);
	memset(output, 0, len);
	if(stat(path, &statbuf)) //path doesn't exist
		return -1;

	strncpy(tmppath, path,_HW_DETECT_MAX_OUTPUT);
	strncat(tmppath, "level",(_HW_DETECT_MAX_OUTPUT-strlen(tmppath))-1);

	if(read_file(tmppath, tmp, _HW_DETECT_MAX_OUTPUT)) {
		snprintf(tmp2, _HW_DETECT_MAX_OUTPUT-1, "Level %s", tmp);
		strncat(output, tmp2,(len-strlen(output))-1);
	}

	strncpy(tmppath, path,_HW_DETECT_MAX_OUTPUT);
	strncat(tmppath, "type",(_HW_DETECT_MAX_OUTPUT-strlen(tmppath))-1);
	if(read_file(tmppath, tmp, _HW_DETECT_MAX_OUTPUT)) {
		if(!strcmp(tmp, "Unified")) {
			strncpy(tmp2, output,_HW_DETECT_MAX_OUTPUT-1);
			snprintf(output,len, "%s ", tmp);
			strncat(output, tmp2,(len-strlen(output))-1);
		}
		else {
			strncat(output, " ",(len-strlen(output))-1);
			strncat(output, tmp,(len-strlen(output))-1);
		}
	}
	strncat(output, " Cache,",(len-strlen(output))-1);

	strncpy(tmppath, path,_HW_DETECT_MAX_OUTPUT);
	strncat(tmppath, "size",(_HW_DETECT_MAX_OUTPUT-strlen(tmppath))-1);
	if(read_file(tmppath, tmp, _HW_DETECT_MAX_OUTPUT)) {
		strncat(output, " ",(len-strlen(output))-1);
		strncat(output, tmp,(len-strlen(output))-1);
	}

	strncpy(tmppath, path,_HW_DETECT_MAX_OUTPUT);
	strncat(tmppath, "ways_of_associativity",(_HW_DETECT_MAX_OUTPUT-strlen(tmppath))-1);
	if(read_file(tmppath, tmp, _HW_DETECT_MAX_OUTPUT)) {
		strncat(output, ", ",(len-strlen(output))-1);
		strncat(output, tmp,(len-strlen(output))-1);
		strncat(output, "-way set associative",(len-strlen(output))-1);
	}

	strncpy(tmppath, path,_HW_DETECT_MAX_OUTPUT);
	strncat(tmppath, "coherency_line_size",(_HW_DETECT_MAX_OUTPUT-strlen(tmppath))-1);
	if(read_file(tmppath, tmp, _HW_DETECT_MAX_OUTPUT)) {
		strncat(output, ", ",(len-strlen(output))-1);
		strncat(output, tmp,(len-strlen(output))-1);
		strncat(output, " Byte cachelines",(len-strlen(output))-1);
	}

	strncpy(tmppath, path,_HW_DETECT_MAX_OUTPUT);
	strncat(tmppath, "shared_cpu_map",(_HW_DETECT_MAX_OUTPUT-strlen(tmppath))-1);
	if(read_file(tmppath, tmp, _HW_DETECT_MAX_OUTPUT)) {
		cpu_map_to_list(tmp, tmp2, _HW_DETECT_MAX_OUTPUT);
		snprintf(tmppath,_HW_DETECT_MAX_OUTPUT, "cpu%i ", cpu);
		if(!strcmp(tmp2, tmppath))
		{
			strncat(output, ", exclusive for ",(len-strlen(output))-1);
			strncat(output, tmppath,(len-strlen(output))-1);
		}
		else 
		{
			strncat(output, ", shared among ",(len-strlen(output))-1);
			strncat(output, tmp2,(len-strlen(output))-1);
		}
	}
	return 0;
}
/* additional functions to query certain information about the cache */
 int generic_cache_level(int cpu, int id) {
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;

   generic_cache_info(cpu,id,tmp,sizeof(tmp));
   beg=strstr(tmp,"Level");
   if (beg==NULL) return -1;
   else beg+=6;
   end=strstr(beg," ");
   if (end!=NULL)*end='\0';

   return atoi(beg);   
 }
 unsigned long long generic_cache_size(int cpu, int id) {
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;

   generic_cache_info(cpu,id,tmp,sizeof(tmp));
   beg=strstr(tmp,",");
   if (beg==NULL) return -1;
   else beg+=2;
   end=strstr(beg,",");
   if (end!=NULL) *end='\0';
   end=strstr(beg,"K");
   if (end!=NULL)
   {
     end--;
     *end='\0';
     return atoi(beg)*1024; 
   }
   end=strstr(beg,"M");
   if (end!=NULL)
   {
     end--;
     *end='\0';
     return atoi(beg)*1024*1024; 
   }

   return -1; 
 }
 unsigned int generic_cache_assoc(int cpu, int id) {
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;

   generic_cache_info(cpu,id,tmp,sizeof(tmp));
   beg=strstr(tmp,",")+1;
   if (beg==NULL) return -1;
   else beg++;
   end=strstr(beg,",")+1;
   if (end==NULL) return -1;
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
   return -1;
 }
 int generic_cache_type(int cpu, int id) {
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;

   generic_cache_info(cpu,id,tmp,sizeof(tmp));
   beg=tmp;
   end=strstr(beg,",");
   if (end!=NULL)*end='\0';
   else return -1;

   if (strstr(beg,"Unified")!=NULL) return UNIFIED_CACHE;
   if (strstr(beg,"Trace")!=NULL) return INSTRUCTION_TRACE_CACHE;
   if (strstr(beg,"Data")!=NULL) return DATA_CACHE;
   if (strstr(beg,"Instruction")!=NULL) return INSTRUCTION_CACHE;

   return -1;
 }
 int generic_cache_shared(int cpu, int id) {
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;
   int num=0;

   generic_cache_info(cpu,id,tmp,sizeof(tmp));
   beg=strstr(tmp,",")+1;
   if (beg==NULL) return -1;
   else beg++;
   end=strstr(beg,",")+1;
   if (end==NULL) return -1;
   else end++;
   beg=end;
   end=strstr(beg,",")+1;
   if (end==NULL) return -1;
   else end++;
   beg=end;
   end=strstr(beg,",")+1;
   if (end==NULL) return -1;
   else end++;
   beg=end;

   while (strstr(beg,"cpu")!=NULL)
   {
     end=strstr(beg,"cpu");
     beg=end+1;
     num++;
   }

   if (num!=0) return num;
   else return -1;
}
 int generic_cacheline_length(int cpu, int id) {
   char tmp[_HW_DETECT_MAX_OUTPUT];
   char *beg,*end;

   generic_cache_info(cpu,id,tmp,sizeof(tmp));
   beg=strstr(tmp,",")+1;
   if (beg==NULL) return -1;
   else beg++;
   end=strstr(beg,",")+1;
   if (end==NULL) return -1;
   else end++;
   beg=end;
   end=strstr(beg,",")+1;
   if (end==NULL) return -1;
   else end++;
   beg=end;
   end=strstr(beg,"Byte cachelines");
   if (end!=NULL) *(end--)='\0';

   return atoi(beg);
}

 /**
  * number of tlbs (of one cpu)
  */
 int generic_num_tlbs(int cpu){return -1;} /*TODO /proc/cpuinfo */
 /**
  * information about the tlb: level, number of entries...
  */
 int generic_tlb_info(int cpu, int id, char* output, size_t len){return -1;}/* TODO /proc/cpuinfo */
 /* additional functions to query certain information about the TLB*/
 int generic_tlb_level(int cpu, int id){return -1;}
 int generic_tlb_entries(int cpu, int id){return -1;}
 int generic_tlb_assoc(int cpu, int id){return -1;}
 int generic_tlb_type(int cpu, int id){return -1;}
 int generic_tlb_num_pagesizes(int cpu, int id){return -1;}
 unsigned long long generic_tlb_pagesize(int cpu, int id,int size_id){return -1;}

  /**
  * the following four functions describe how the CPUs are distributed among packages
  * num_cpus() = num_packages() * num_threads_per_package()
  * num_threads_per_package() = num_cores_per_package() * num_threads_per_core()
  */
int generic_num_packages()
{
	struct dirent **namelist;
	int ndir, m, num = -1;
	char tmppath[_HW_DETECT_MAX_OUTPUT];
	char buf[20];
	id_le * pkg_id_list = NULL;


	strcpy(path, "/sys/devices/system/cpu/");
	ndir = scandir(path, &namelist, 0, 0);
	if(ndir >= 0)
	{
		while(ndir--) {
			if(match_str(namelist[ndir]->d_name, "cpu", &m)) {
				strncpy(tmppath, path,sizeof(tmppath));
				snprintf(buf, sizeof(buf),"cpu%i", m);
				strcat(tmppath, buf);
				strcat(tmppath, "/online");
				read_file(tmppath, output, sizeof(output));
				if (strncmp(output,"0",1)!=0) {
					strncpy(tmppath, path,sizeof(tmppath));
					snprintf(buf, sizeof(buf),"cpu%i", m);
					strcat(tmppath, buf);
					strcat(tmppath, "/topology/physical_package_id");
					if(read_file(tmppath, output, sizeof(output)))
						inc_id_count(atoi(output), &pkg_id_list);
				}
			}
			free(namelist[ndir]);
		}
		free(namelist);
		num = id_total_count(pkg_id_list);
		free_id_list(&pkg_id_list);
	}
	return num;
}

int generic_num_cores_per_package()
{
	struct dirent **namelist;
	int ndir, m, n, num = 0, pkg_id_tocount = -1;
	char tmppath[_HW_DETECT_MAX_OUTPUT];
	char buf[20];
	id_le * core_id_list = NULL;

	strcpy(path, "/sys/devices/system/cpu/");
	ndir = scandir(path, &namelist, 0, 0);
	if(ndir >= 0)
	{
		while(ndir--) {
			if(match_str(namelist[ndir]->d_name, "cpu", &m)) {
				strncpy(tmppath, path,sizeof(tmppath));
				snprintf(buf, sizeof(buf),"cpu%i", m);
				strcat(tmppath, buf);
				strcat(tmppath, "/online");
				read_file(tmppath, output, sizeof(output));
				if (strncmp(output,"0",1)!=0) {
					strcpy(tmppath, path);
					sprintf(buf, "cpu%i", m);
					strcat(tmppath, buf);
					strcat(tmppath, "/topology/physical_package_id");
					read_file(tmppath, output, _HW_DETECT_MAX_OUTPUT);
					m = atoi(output);
					if(pkg_id_tocount == -1) pkg_id_tocount = m;

					strcpy(tmppath, path);
					strcat(tmppath, buf);
					strcat(tmppath, "/topology/core_id");
					read_file(tmppath, output, _HW_DETECT_MAX_OUTPUT);
					n = atoi(output);

					if(m == pkg_id_tocount) /*FIXME: only counts cores from first package_id that is found, assumes that every package has the same amount of cores*/
					{
						//if (num<n+1) num=n+1; //doesn't work if there is a gap in between the ids
						inc_id_count(n, &core_id_list);
					}
				}
			}
			free(namelist[ndir]);
		}
		free(namelist);
		num = id_total_count(core_id_list);
                free_id_list(&core_id_list);
	}
	else return -1;

	if (num==0) return -1;
	return num;
}

int generic_num_threads_per_core()
{
	struct dirent **namelist;
	int ndir, m, n, num = 0, pkg_id_tocount = -1, core_id_tocount = -1;
	char tmppath[_HW_DETECT_MAX_OUTPUT];
	char buf[20];

	strcpy(path, "/sys/devices/system/cpu/");
	ndir = scandir(path, &namelist, 0, 0);
	if(ndir >= 0)
	{
		while(ndir--) {
			if(match_str(namelist[ndir]->d_name, "cpu", &m)) {
				strncpy(tmppath, path,sizeof(tmppath));
				snprintf(buf, sizeof(buf),"cpu%i", m);
				strcat(tmppath, buf);
				strcat(tmppath, "/online");
				read_file(tmppath, output, sizeof(output));
				if (strncmp(output,"0",1)!=0) {
					strcpy(tmppath, path);
					sprintf(buf, "cpu%i", m);
					strcat(tmppath, buf);
					strcat(tmppath, "/topology/core_id");
					read_file(tmppath, output, _HW_DETECT_MAX_OUTPUT);
					m = atoi(output);
					if(core_id_tocount == -1) core_id_tocount = m;
				
					strcpy(tmppath, path);
					strcat(tmppath, buf);
					strcat(tmppath, "/topology/physical_package_id");
					read_file(tmppath, output, _HW_DETECT_MAX_OUTPUT);
					n = atoi(output);
					if(pkg_id_tocount == -1) pkg_id_tocount = n;

					if(m == core_id_tocount && n == pkg_id_tocount) /*FIXME: only counts threads from the first core_id and package_id that are found, assumes that every core has the same amount of threads*/
					{
						num++;
					}
				}
			}
			free(namelist[ndir]);
		}
		free(namelist);
	}
	else return -1;

	if (num == 0) num = generic_num_threads_per_package() / generic_num_cores_per_package();
	if (num != generic_num_threads_per_package() / generic_num_cores_per_package()) return -1;

	return num;
}

int generic_num_threads_per_package()
{

	struct dirent **namelist;
	int ndir, m, num = 0, pkg_id_tocount = -1;
	char tmppath[_HW_DETECT_MAX_OUTPUT];
	char buf[20];

	/*TODO proc/cpuinfo*/

	strcpy(path, "/sys/devices/system/cpu/");
	ndir = scandir(path, &namelist, 0, 0);
	if(ndir >= 0)
	{
		while(ndir--) {
			if(match_str(namelist[ndir]->d_name, "cpu", &m)) {
				strncpy(tmppath, path,sizeof(tmppath));
				snprintf(buf, sizeof(buf),"cpu%i", m);
				strcat(tmppath, buf);
				strcat(tmppath, "/online");
				read_file(tmppath, output, sizeof(output));
				if (strncmp(output,"0",1)!=0) {
					strcpy(tmppath, path);
					sprintf(buf, "cpu%i", m);
					strcat(tmppath, buf);
					strcat(tmppath, "/topology/physical_package_id");
					read_file(tmppath, output, _HW_DETECT_MAX_OUTPUT);
					m = atoi(output);
					if(pkg_id_tocount == -1) pkg_id_tocount = m;
				
					if(m == pkg_id_tocount) /*FIXME: only counts threads from first package_id that is found and assumes that every package has the same amount of threads*/
					{
						num++;
					}
				}
			}
			free(namelist[ndir]);
		}
		free(namelist);
	}
	else return -1;

	if (num == 0) return -1;
	return num;
}

 /**
  * paging related information
  */
int generic_get_virt_address_length()
{
	char buffer[_HW_DETECT_MAX_OUTPUT], *pch;
	
	if(!get_proc_cpuinfo_data("address sizes", buffer, 0))
	{
		pch = strstr(buffer, ",")+2;
		pch = strtok(pch, "bits virtual");
		return atoi(pch);
	}
	else return -1;
}
 
int generic_get_phys_address_length()
{
	char buffer[_HW_DETECT_MAX_OUTPUT], *pch;
	
	if(!get_proc_cpuinfo_data("address sizes", buffer, 0))
	{
		pch = strtok(buffer, "bits physical");
		return atoi(pch);
	}
	else return -1;
}

int generic_num_pagesizes()
{
	if(sysconf(_SC_PAGESIZE) != -1)
		return 1;
	else
		return -1;
}

long long generic_pagesize(int id)
{
	return sysconf(_SC_PAGESIZE);
}

/* see cpu.h */
#if defined (__ARCH_UNKNOWN)

 /*
  * use generic implementations for unknown architectures
  */

 void get_architecture(char * arch) { generic_get_architecture(arch); }
 int get_cpu_vendor(char* vendor){return generic_get_cpu_vendor(vendor);}
 int get_cpu_name(char* name){return generic_get_cpu_name(name);}
 int get_cpu_family(){return generic_get_cpu_family();}
 int get_cpu_model(){return generic_get_cpu_model();}
 int get_cpu_stepping(){return generic_get_cpu_stepping();}
 int get_cpu_isa_extensions(char* features) {return generic_get_cpu_isa_extensions(features);}
 int get_cpu_lwp(char* lwpfeatures) {return generic_get_cpu_lwp(lwpfeatures);}
 unsigned long long get_cpu_clockrate(int check, int cpu){return generic_get_cpu_clockrate(check,cpu);}
 unsigned long long timestamp(){return generic_timestamp();}
 int num_caches(int cpu) {return generic_num_caches(cpu);} 
 int cache_info(int cpu,int id, char* output) {return generic_cache_info(cpu,id,output);}
 int cache_level(int cpu, int id) {return generic_cache_level(cpu,id);};
 unsigned long long cache_size(int cpu, int id){return generic_cache_size(cpu,id);};
 unsigned int cache_assoc(int cpu, int id){return generic_cache_assoc(cpu,id);};
 int cache_type(int cpu, int id){return generic_cache_type(cpu,id);};
 int cache_shared(int cpu, int id){return generic_cache_shared(cpu,id);};
 int cacheline_length(int cpu, int id){return generic_cacheline_length(cpu,id);};
 int num_tlbs(int cpu) {return generic_num_tlbs(cpu);}
 int tlb_info(int cpu, int id, char* output) {return generic_tlb_info(cpu,id,output);}
 int tlb_level(int cpu, int id) {return generic_tlb_level(cpu,id)};
 int tlb_entries(int cpu, int id){return generic_tlb_entries(cpu,id)};
 int tlb_assoc(int cpu, int id){return generic_tlb_assoc(cpu,id)};
 int tlb_type(int cpu, int id){return generic_tlb_type(cpu,id)};
 int tlb_num_pagesizes(int cpu, int id){return generic_tlb_num_pagesizes(cpu,id)};
 unsigned long long tlb_pagesize(int cpu, int id, int size_id){return generic_tlb_pagesize(cpu,id,size_id)};
 int num_packages(){return generic_num_packages();}
 int num_cores_per_package(){return generic_num_cores_per_package();}
 int num_threads_per_core(){return generic_num_threads_per_core();}
 int num_threads_per_package(){return generic_num_threads_per_package();}
 int get_virt_address_length(){return generic_get_virt_address_length();}
 int get_phys_address_length(){return generic_get_phys_address_length();}
 int num_pagesizes(){return generic_num_pagesizes();}
 long long pagesize(int id){return generic_pagesize(id);}

#endif

