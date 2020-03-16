#pragma once

#ifdef __ASSEMBLER__

/* Some toolchains use other characters (e.g. '`') to mark new line in macro */
#ifndef ASM_NL
#define ASM_NL           ;
#endif

#define __ALIGN         .p2align 4, 0x90

#define ALIGN           __ALIGN

#ifndef ENTRY
#define ENTRY(name) \
        .global name ASM_NL \
        ALIGN ASM_NL \
        name:
#endif

#ifndef END
#define END(name) \
        .size name, .-name
#endif

/* If symbol 'name' is treated as a subroutine (gets called, and returns)
 * then please use ENDPROC to mark 'name' as STT_FUNC for the benefit of
 * static analysis tools such as stack depth analyzer.
 */
#ifndef ENDPROC
#define ENDPROC(name) \
        .type name, @function ASM_NL \
        END(name)
#endif

#define GLOBAL(name)    \
        .globl name;    \
        name:

#endif  /* __ASSEMBLER__ */
