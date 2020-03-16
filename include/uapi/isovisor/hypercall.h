#pragma once

#include "types.h"

unsigned long os_get_epc_base(void);
size_t os_get_epc_size(void);
long os_create_enclave(epn_t secs_epn, uint64_t size, uint64_t baseaddr, uint64_t xfrm);
long os_add_regular(epn_t reg_epn, epn_t secs_epn, spn_t src_spn, uint64_t address, uint64_t perm);
long os_add_thread(epn_t tcs_epn, epn_t secs_epn, spn_t src_spn, uint64_t address);
long os_seal_enclave(epn_t secs_epn);
long os_enter_thread(uintptr_t tcs_va, uint64_t aep);
long os_resume_thread(uintptr_t tcs_va, uint64_t aep);
