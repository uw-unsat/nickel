/*
 * Don't add #pragma once or anything else in this header.
 * It is included by other files.
 */

#if !defined(__HYPERCALL)
#define __HYPERCALL(x, ...)
#endif

/* Enclave creation */

__HYPERCALL(create, pageid_t epn_secs, pageid_t epn_pml4)
__HYPERCALL(add_pdpt, pageid_t epn_pml4, size_t index, pageid_t epn_pdpt)
__HYPERCALL(add_pd, pageid_t epn_pdpt, size_t index, pageid_t epn_pd)
__HYPERCALL(add_pt, pageid_t epn_pd, size_t index, pageid_t epn_pt)
__HYPERCALL(add_frame, pageid_t epn_pt, size_t index, pageid_t epn_frame)
__HYPERCALL(copy_frame, pageid_t epn_frame, spn_t spn)
__HYPERCALL(map_shared, pageid_t epn_pt, size_t index, spn_t src)
__HYPERCALL(add_thread, pageid_t epn_secs, pageid_t epn_tcs, uint64_t entry)

/* Enclave execution */

__HYPERCALL(seal, pageid_t epn_secs)
__HYPERCALL(enter, pageid_t thread_id, uint64_t arg0, uint64_t arg1, uint64_t arg2)
__HYPERCALL(resume, pageid_t thread_id)

/* Enclave destruction */

__HYPERCALL(stop, pageid_t epn_secs)
__HYPERCALL(remove, pageid_t epn)
__HYPERCALL(destroy, pageid_t epn_secs)

/* Dynamic memory management */

__HYPERCALL(alloc_spare, pageid_t epn_secs, pageid_t epn_spare)
__HYPERCALL(reclaim_spare, pageid_t epn_spare)

/* Other */

__HYPERCALL(get_shared_pages, void)
__HYPERCALL(stat, void)
