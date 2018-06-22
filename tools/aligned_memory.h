/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: aligned_memory.h 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/tools/aligned_memory.h $
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* functions for aligned malloc and free
 * see ../kernel/numerical/gemv/C/SSE_Intrinsics/0/aligned_m128
 *******************************************************************/

/*
 * use this functions:
 *
 *  void *_aligned_malloc(size_t size, size_t alignment);
 *  void _aligned_free(void *memblock);
 */

#ifndef __BENCHIT_ALIGNED_MEMORY_H
#define __BENCHIT_ALIGNED_MEMORY_H 1

#include <errno.h>
#include <stddef.h> /* ptrdiff_t */
#include <stdint.h> /* uintptr_t */

#define NOT_POWER_OF_TWO(n) (((n) & ((n) - 1)))
#define UI(p) ((uintptr_t) p)
static void *ptr_align(void *p0, size_t alignment, size_t offset) {
     return (void *) (((UI(p0) + (alignment + sizeof(void*)) + offset) & (~UI(alignment - 1))) - offset);
}

void *_aligned_offset_malloc(size_t size, size_t alignment, size_t offset) {
    void *p0, *p;

    if (NOT_POWER_OF_TWO(alignment)) {
        errno = EINVAL;
	return((void*) 0);
    }
    if (size == 0) return((void*) 0);
    if (alignment < sizeof(void *)) alignment = sizeof(void *);

/* including the extra sizeof(void*) is overkill on a 32-bit
    machine, since malloc is already 8-byte aligned, as long
    as we enforce alignment >= 8 ...but oh well */
    p0 = malloc(size + (alignment + sizeof(void*)));
    if (!p0) return((void*) 0);
    p = ptr_align(p0, alignment, offset);
    *(((void **) p) - 1) = p0;
    return p;
}

void *_aligned_malloc(size_t size, size_t alignment) {
    return _aligned_offset_malloc(size, alignment, 0);
}

void _aligned_free(void *memblock) {
    if (memblock) free(*(((void **) memblock) - 1));
}

#endif /* __BENCHIT_ALIGNED_MEMORY_H */

