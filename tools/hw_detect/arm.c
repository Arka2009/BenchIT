/** 
* @file arm.c
*  architecture specific part of the hardware detection for ARM architectures
*  currently only ARMv7 CPUs are supported, support for ARMv8 is in preparation
* 
* Author: Roland Martin Oldenburg (roland_martin.oldenburg@zih.tu-dresden.de)
*/
//#include "cpu.h"
#include "arm.h"
#include "cpu.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <math.h>

//#include "properties.h"

/*
 * Path to the Linux kernelmodule, which is needed to read out cpuid information
 */
#define CPUID_PATH /sys/kernel/cpuid_kset/cpuid

#if ((defined (__ARMv8__))||(defined (__ARMv8))||(defined (ARMv8)))
    #define _64_BIT
#elif ((defined (__ARMv7__))||(defined (__ARMv7))||(defined (ARMv7)))
    #define _32_BIT
#endif

static volatile arm_cpu_info_t *cpuinfo;

void read_hw_register(){
	cpuinfo = (arm_cpu_info_t*) calloc( 1,sizeof( arm_cpu_info_t ));
	FILE *fp;
        char mainid[10];
        char cachetype[10];
	char cache_size_id[10];
        char tlbtype[10];
	int cpu;
	int cache;
	int ccsidr;
	int tlb;
        fp=fopen("/sys/kernel/cpuid_kset/cpuid/mainid", "r"); 
        fscanf(fp, "%s", mainid);
        fclose(fp);

        fp=fopen("/sys/kernel/cpuid_kset/cpuid/cachetype", "r"); 
        fscanf(fp, "%s", cachetype);
        fclose(fp);

	fp=fopen("/sys/kernel/cpuid_kset/cpuid/ccsidr", "r"); 
        fscanf(fp, "%s", cache_size_id);
        fclose(fp);

        fp=fopen("/sys/kernel/cpuid_kset/cpuid/tlbtype", "r"); 
        fscanf(fp, "%s", tlbtype);
        fclose(fp);

	/* Convert strings to integer */
	cpu = atoi(mainid);
	cache = atoi(cachetype);
	ccsidr = atoi(cache_size_id);
	tlb = atoi(tlbtype);	

	/* Main ID Register */
	__asm__(
	"LDR r4, =0xfffffff0\n"	
	"\tBIC %[revision], %[main], r4\n"
	: [revision]"=r"(cpuinfo->revision)
        : [main]"r"(cpu)
	); 

	__asm__(
	"LDR r4, =0xffff000f\n"	
	"\tBIC %[model], %[main], r4\n"
	"\tLSR %[model], #4\n"
	: [model]"=r"(cpuinfo->model)
        : [main]"r"(cpu)
	); 	
	
	__asm__(
	"LDR r4, =0xfff0ffff\n"	
	"\tBIC %[arch], %[main], r4\n"
	"\tLSR %[arch], #16\n"
	: [arch]"=r"(cpuinfo->architecture)
        : [main]"r"(cpu)
	); 

	__asm__(
	"LDR r4, =0xff0fffff\n"	
	"\tBIC %[variant], %[main], r4\n"
	"\tLSR %[variant], #20\n"
	: [variant]"=r"(cpuinfo->variant)
        : [main]"r"(cpu)
	);

	__asm__(
	"LDR r4, =0x00ffffff\n"	
	"\tBIC %[vendor], %[main], r4\n"
	"\tLSR %[vendor], #24\n"
	: [vendor]"=r"(cpuinfo->vendor)
        : [main]"r"(cpu)
	);

	/* TLB Type Register */
	__asm__(
	"LDR r4, =0xfffffffe\n"	
	"\tBIC %[unified], %[tlb], r4\n"
	: [unified]"=r"(cpuinfo->TLB_unified)
        : [tlb]"r"(tlb)
	); 

	__asm__(
	"LDR r4, =0xfffffffd\n"	
	"\tBIC %[tlbsize], %[tlb], r4\n"
	"\tLSR %[tlbsize], #1\n"
	: [tlbsize]"=r"(cpuinfo->TLB_size)
        : [tlb]"r"(tlb)
	); 

	__asm__(
	"LDR r4, =0xffff00ff\n"	
	"\tBIC %[DLsize], %[tlb], r4\n"
	"\tLSR %[DLsize], #8\n"
	: [DLsize]"=r"(cpuinfo->TLB_DLsize)
        : [tlb]"r"(tlb)
	); 

	__asm__(
	"LDR r4, =0xff00ffff\n"	
	"\tBIC %[ILsize], %[tlb], r4\n"
	"\tLSR %[ILsize], #16\n"
	: [ILsize]"=r"(cpuinfo->TLB_ILsize)
        : [tlb]"r"(tlb)
	); 

	/* CCSIDR */
	__asm__(
	"LDR r4, =0xfffffff8\n"	
	"\tBIC %[CLsize], %[ccsidr], r4\n"
	: [CLsize]"=r"(cpuinfo->DCacheline_size)
        : [ccsidr]"r"(ccsidr)
	); 

	__asm__(
	"LDR r4, =0xffffe007\n"	
	"\tBIC %[Cassoc], %[ccsidr], r4\n"
	"\tLSR %[Cassoc], #3\n"
	: [Cassoc]"=r"(cpuinfo->DCache_assoc)
        : [ccsidr]"r"(ccsidr)
	); 

	__asm__(
	"LDR r4, =0xf0001fff\n"	
	"\tBIC %[Csize], %[ccsidr], r4\n"
	"\tLSR %[Csize], #13\n"
	: [Csize]"=r"(cpuinfo->DCache_size)
        : [ccsidr]"r"(ccsidr)
	); 

}

void get_architecture(char* arch, size_t len){
	switch (cpuinfo->architecture){
	case 1:	//0x1
		strncpy(arch,"ARMv4",len);
		break;
	case 2:	//0x2
		strncpy(arch,"ARMv4T",len);
		break;
	case 3:	//0x3
		strncpy(arch,"ARMv5",len);
		break;
	case 4:	//0x4
		strncpy(arch,"ARMv5T",len);
		break;
	case 5:	//0x5
		strncpy(arch,"ARMv5TE",len);
		break;
	case 6:	//0x6
		strncpy(arch,"ARMv5TEJ",len);
		break;
	case 7:	//0x7
		strncpy(arch,"ARMv6",len);
		break;
	case 15:	//0xf Definied by CPUID scheme
		strncpy(arch,"ARMv7",len);
		break;
	default:
		strncpy(arch,"n/a",len);
	}
	
}

int get_cpu_vendor(char* vendor, size_t len){

	switch (cpuinfo->vendor){
	case 65:	//0x41
		strncpy(vendor,"ARM Limited",len);
		break;
	case 68:	//0x44
		strncpy(vendor,"Digital Equipment Corporation",len);
		break;
	case 77:	//0x4D
		strncpy(vendor,"Motorola, Freescale Semiconductor Inc.",len);
		break;
	case 81:	//0x51
		strncpy(vendor,"QUALCOMM Inc.",len);
		break;
	case 86:	//0x56
		strncpy(vendor,"Marvell Semiconductor Inc.",len);
		break;
	case 105:	//0x69
		strncpy(vendor,"Intel Corporation",len);
		break;
	default:
		strncpy(vendor,"n/a",len);
	}
	return 0;
}

int get_cpu_name(char* name, size_t len){
	switch (cpuinfo->model){
	case 3077:	//0xC05
		strncpy(name,"Cortex-A5",len);
		break;	
	case 3079:	//0xC07
		strncpy(name,"Cortex-A7",len);
		break;	
	case 3080:	//0xC08
		strncpy(name,"Cortex-A8",len);
		break;
	case 3081:	//0xC09
		strncpy(name,"Cortex-A9",len);
		break;
	case 3087:	//0xC0F
		strncpy(name,"Cortex-A15",len);
		break;
	default:
		strncpy(name,"n/a",len);
	}
	return 0;
}

void get_cpu_model(char* model, size_t len){
	switch (cpuinfo->model){
	case 3077:	
		strncpy(model,"0xC05",len);
		break;	
	case 3079:	
		strncpy(model,"0xC07",len);
		break;	
	case 3080:	
		strncpy(model,"0xC08",len);
		break;
	case 3081:	
		strncpy(model,"0xC09",len);
		break;
	case 3087:
		strncpy(model,"0xC0F",len);
		break;
	default:
		strncpy(model,"n/a",len);
	}
}

void get_cpu_stepping(char* stepping, size_t len){
	sprintf(stepping,"r%dp%d",cpuinfo->variant,cpuinfo->revision);
}

void get_cpu_family(char* family, size_t len){
	if ((3072<=cpuinfo->model) && (cpuinfo->model<=3087)){
		strncpy(family,"Cortex-A Series",len);
	}
	else{
		strncpy(family,"n/a",len);
	} 
}

unsigned long long get_cpu_clockrate(int check,int cpu){
	return generic_get_cpu_clockrate(check,cpu);
}

int get_phys_address_length(){
	if (cpuinfo->model == 3081) return 32;
	else return generic_get_phys_address_length();
}

int get_virt_address_length(){
	if (cpuinfo->architecture == 15) return 32;
	else return generic_get_virt_address_length();	
}

unsigned long long timestamp(){
	return generic_timestamp();
}

int num_caches(int cpu){
	if (cpuinfo->model == 3081) return 3;
	else return generic_num_caches(cpu);
} 

int cache_info(int cpu,int id, char* output,size_t len){
	return generic_cache_info(cpu,id,output,len);
}

int cache_level(int cpu, int id){
	if (cpuinfo->model == 3081){
		switch(id){
		case 0:
			return 1;
		case 1:
			return 1;
		case 2:		
			return 2;
		default:
			return generic_cache_level(cpu,id);
		}
	}
	else return generic_cache_level(cpu,id);
}

unsigned long long cache_size(int cpu, int id){
	if (cpuinfo->model == 3081){
		switch(id){
		case 0:
			return ((cpuinfo->DCache_size + 1) * 128);
		case 1:
			return ((cpuinfo->DCache_size + 1) * 128);
		case 2:		
			return 1048576;
		default:
			return generic_cache_size(cpu,id);
		}
	}
	else return generic_cache_size(cpu,id);
}
 
unsigned int cache_assoc(int cpu, int id){
	//if (cpuinfo->model == 3081){
		switch(id){
		case 0:
			return (cpuinfo->DCache_assoc + 1);
		case 1:
			return (cpuinfo->DCache_assoc + 1);
		case 2:		
			return 16;
		default:
			return generic_cache_assoc(cpu,id);
		}
	//}
	//else return generic_cache_assoc(cpu,id);
}
 
int cache_type(int cpu, int id){
	if (cpuinfo->model == 3081){
		switch(id){
		case 0:
			return INSTRUCTION_CACHE;
		case 1:
			return DATA_CACHE;
		case 2:	
			return UNIFIED_CACHE;
		default:
			return generic_cache_type(cpu,id);
		}
	}
	else return generic_cache_type(cpu,id);
}
 
int cache_shared(int cpu, int id){
	if (cpuinfo->model == 3081){
		switch (id){
		case 0:
			return 1;
		case 1:
			return 1;
		case 2:
			return 2;
		default:
			return generic_cache_shared(cpu,id);
		}
	}
	else return generic_cache_shared(cpu,id);
}
 
int cacheline_length(int cpu, int id){	
	//if (cpuinfo->model == 3081){
  		switch (id){	
		case 0:
			return (1 << (cpuinfo->DCacheline_size + 2))*4; //4 Byte per word
		case 1:
			return (1 << (cpuinfo->DCacheline_size + 2))*4;
		case 2:
			return 32;
		default:
			return generic_cacheline_length(cpu,id);	
		}
	//}
	//else return generic_cacheline_length(cpu,id);
}
 
int num_tlbs(int cpu){
	if (cpuinfo->model == 3081) return 3;
	else return generic_num_tlbs(cpu);
}
 
int tlb_info(int cpu, int id, char* output, size_t len){
	return generic_tlb_info(cpu,id,output,len);
}
 
int tlb_level(int cpu, int id){
	if (cpuinfo->model == 3081){
  		switch (id){	
		case 0:
			return 1;
		case 1:
			return 1;
		case 2:
			return 2;
		default:
			return generic_tlb_level(cpu,id);	
		}
	}
	else return generic_tlb_level(cpu,id);
}
 
int tlb_entries(int cpu, int id){
	if (cpuinfo->model == 3081){
  		switch (id){	
		case 0:
			return 32;
		case 1:
			return 32;
		case 2:
			if (cpuinfo->TLB_size) return 128;
			else return 64;
		default:
			return generic_tlb_entries(cpu,id);	
		}
	}
	else return generic_tlb_entries(cpu,id);
}
 
int tlb_assoc(int cpu, int id){
	if (cpuinfo->model == 3081){
  		switch (id){	
		case 0:
			return FULLY_ASSOCIATIVE;
		case 1:
			return FULLY_ASSOCIATIVE;
		case 2:
			return 2;
		default:
			return generic_tlb_assoc(cpu,id); 	
		}
	}
	else return generic_tlb_assoc(cpu,id);
}

int tlb_type(int cpu, int id){
	if (cpuinfo->model == 3081){
  		switch (id){	
		case 0:
			return INSTRUCTION_TLB;
		case 1:
			return DATA_TLB;
		case 2:
			return UNIFIED_TLB;
		default:
			return generic_tlb_type(cpu,id);	
		}
	}	
	else return generic_tlb_type(cpu,id);
}

int tlb_num_pagesizes(int cpu, int id){
	if (cpuinfo->model == 3081){
  		switch (id){	
		case 0:
			return 4;
		case 1:
			return 4; 
		case 2:
			return 4;	
		default:
			return generic_tlb_num_pagesizes(cpu,id);
		}
	}
	else return generic_tlb_num_pagesizes(cpu,id);
}

unsigned long long tlb_pagesize(int cpu, int id, int size_id){
	if (cpuinfo->model == 3081){
  		//switch (id){	
		//case 0:
		//	return 0;
		//case 1:
		//	return 0;
		//case 2:
			switch (size_id){
			case 0:
				return 4096;
			case 1:
				return 65536;
			case 2:
				return 1048576;
			case 3:
				return 16777216;
			default:
				return 4096;
			}
		//	break;
		//default:
		//	return generic_tlb_pagesize(cpu,id,size_id);		
		//}
	}
	else return generic_tlb_pagesize(cpu,id,size_id);
}

int num_packages(){
	return generic_num_packages();
}

int num_pagesizes(){
	switch (cpuinfo->model){
	/*case 3077:	
		strncpy(model,"0xC05",len);
		break;	
	case 3079:	
		strncpy(model,"0xC07",len);
		break;	
	case 3080:	
		strncpy(model,"0xC08",len);
		break;*/
	case 3081:	
		//strncpy(model,"0xC09",len);
		return 4;
	/*case 3087:
		strncpy(model,"0xC0F",len);
		break;*/
	default:
		return 1;
	}
}

long long pagesize(int id){
	switch(cpuinfo->model){	
	case 3081:		
		switch (id){
		case 0:
			return 4096;
		case 1:
			return 65536;
		case 2: 
			return 1048576;
		case 3:
			return 16777216;
		default:
			return 4096;
		}
		break;
	default:
		printf("WARN: Calling generic_pagesize(%i) \n", id );
		return generic_pagesize(id);
	}
}

int num_cores_per_package(){
	return generic_num_cores_per_package();
}

int num_threads_per_package(){
	return generic_num_threads_per_package();
}

int num_threads_per_core()
{
  return num_threads_per_package()/num_cores_per_package();
}

/* CPU Feature List -> Processor Feature Register 0 und 1 ([c1,0] , [c1,1]) */
int get_cpu_isa_extensions(char* features, size_t len){
	return generic_get_cpu_isa_extensions(features, len);
}

/*
 * ARM specific routines
 * Instead of Stepping, ARM uses Revisions like 'r1p2'
 */ 
int get_cpu_variant(){
	return cpuinfo->variant;
}

int get_cpu_revision(){
	return cpuinfo->revision;
}





//#endif

/*void main(void){
	int retval;
	char model_str[48];
	char architecture[10];	
	char vendor[13];
	char stepping[5];
	
	read_hw_register();
	printf("Revision: r%dp%d\n", cpuinfo->variant, cpuinfo->revision);
	retval = get_cpu_name(model_str,sizeof(model_str));
	get_cpu_stepping(stepping,sizeof(stepping));
	printf("Stepping: %s\n", stepping);
	printf("CPU Model: %s\n", model_str);
	get_architecture(architecture,sizeof(architecture));
	printf("Architecture: %s\n", architecture);
	retval = get_cpu_vendor(vendor,sizeof(vendor));
	printf("Vendor: %s\n", vendor);
	printf("Number Cores per Package: %d\n", num_cores_per_package());
}*/
