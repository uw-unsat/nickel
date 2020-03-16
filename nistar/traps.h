#pragma once

#include <asm/ptrace.h>

void current_thread_tf(struct pt_regs **tf);
