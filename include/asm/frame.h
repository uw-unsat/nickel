#pragma once

/*
 * These are stack frame creation macros.  They should be used by every
 * callable non-leaf asm function to make kernel stack traces more reliable.
 */

.macro FRAME_BEGIN
        push    %rbp
        movq    %rsp, %rbp
.endm

.macro FRAME_END
        pop     %rbp
.endm

#define FRAME_OFFSET    8
