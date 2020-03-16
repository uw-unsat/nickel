#include <io/linkage.h>

ENTRY(memcpy)
        movq %rdi, %rax
        movq %rdx, %rcx
        rep movsb
        ret
ENDPROC(memcpy)

/*
 * ISO C memset - set a memory block to a byte value. This function uses
 * enhanced rep stosb to override the fast string function.
 * The code is simpler and shorter than the fast string function as well.
 *
 * rdi   destination
 * rsi   value (char)
 * rdx   count (bytes)
 *
 * rax   original destination
 */
ENTRY(memset)
        movq %rdi,%r9
        movb %sil,%al
        movq %rdx,%rcx
        rep stosb
        movq %r9,%rax
        ret
ENDPROC(memset)
