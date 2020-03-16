/*
 * Don't add #pragma once or anything else in this header.
 * It is included by other files.
 */

#ifndef __SYSCALL
#define __SYSCALL(x, ...)
#endif

__SYSCALL(exit, long retcode)
__SYSCALL(unmap_spare, pageid_t id_pt, size_t index, pageid_t id_frame)
__SYSCALL(map_spare, pageid_t id_pt, size_t index, pageid_t id_spare)