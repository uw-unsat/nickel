/*
 * Don't add #pragma once or anything else in this header.
 * It is included by other files.
 */

#if !defined(__HYPERCALL)
#define __HYPERCALL(x, ...)
#endif

__HYPERCALL(get_epc_base, void)
__HYPERCALL(get_epc_size, void)
__HYPERCALL(create_enclave, epn_t secs_epn, uint64_t size, uint64_t baseaddr, uint64_t xfrm)
__HYPERCALL(add_regular, epn_t reg_epn, epn_t secs_epn, spn_t src_spn,
                    uint64_t address, uint64_t perm)
__HYPERCALL(add_thread, epn_t tcs_epn, epn_t secs_epn, spn_t src_spn, uint64_t address)
__HYPERCALL(seal_enclave, epn_t secs_epn)
__HYPERCALL(enter_thread, uintptr_t tcs_va, uint64_t aep)
__HYPERCALL(resume_thread, uintptr_t tcs_va, uint64_t aep)
