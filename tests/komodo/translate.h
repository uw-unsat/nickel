#pragma once

#include <sys/types.h>

#define X86_INSN_LEN            16

extern uint32_t arm_insns[];
extern uint8_t x86_insns[SZ_4K / X86_INSN_LEN][X86_INSN_LEN];

size_t translate_test_enclave(void);
