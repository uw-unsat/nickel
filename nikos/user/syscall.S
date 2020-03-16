#include <io/linkage.h>
#include "asm-offsets.h"

#define __SYSCALL(x) ENTRY(x); movq $SYS_##x, %rax; syscall; retq; ENDPROC(x)
#include <mcertikos/syscall.inc>
#undef __SYSCALL
