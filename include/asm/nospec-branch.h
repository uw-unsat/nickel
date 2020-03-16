#pragma once

/*
 * JMP_NOSPEC and CALL_NOSPEC macros can be used instead of a simple
 * indirect jmp/call which may be susceptible to the Spectre variant 2
 * attack.
 */
.macro JMP_NOSPEC reg:req
        jmp     *\reg
.endm

.macro CALL_NOSPEC reg:req
        call    *\reg
.endm
