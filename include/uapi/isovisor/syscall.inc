/*
 * Don't add #pragma once or anything else in this header.
 * It is included by other files.
 */

#if !defined(__SYSCALL)
#define __SYSCALL(x, ...)
#endif

__SYSCALL(exit, void)
