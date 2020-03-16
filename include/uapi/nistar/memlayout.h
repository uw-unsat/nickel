#pragma once

#include <io/mmu.h>
#include <io/sizes.h>

/* TLS ends 2M below 2^47 */
#define USER_TLS_SIZE           SZ_4K
#define USER_TLS_END            UINT64_C(0x7fffffe00000)
#define USER_TLS_START          (USER_TLS_END - USER_TLS_SIZE)
#define USER_STACK_TOP          USER_TLS_START

/* PCI hole ends 1G below 2^47 */
#define USER_PCI_END            (UINT64_C(0x800000000000) - 2 * SZ_1G)
#define USER_PCI_SIZE           SZ_1G
#define USER_PCI_START          (USER_PCI_END - USER_PCI_SIZE)

/* ld.so starts from 256M */
#define LDSO_START              UINT64_C(0x000010000000)

#define BRK_SIZE                SZ_1G
#define BRK_START               UINT64_C(0x000040000000)
#define BRK_END                 (BRK_START + BRK_SIZE)

#define FS_FILE_STRUCT_SIZE     SZ_1M
#define FS_FILE_STRUCT_START    (BRK_START - SZ_2M)
#define FS_FILE_STRUCT_END      (FS_FILE_STRUCT_START + FS_FILE_STRUCT_SIZE)

#define FS_FILE_INODE_SIZE      SZ_1M
#define FS_FILE_INODE_START     (FS_FILE_STRUCT_END)
#define FS_FILE_INODE_END       (FS_FILE_INODE_START + FS_FILE_INODE_SIZE)

/* mmap starts from 8G */
#define MMAP_SIZE               SZ_1G
#define MMAP_START              UINT64_C(0x000200000000)
#define MMAP_END                (MMAP_START + MMAP_SIZE)

#define FS_FILE_MAP_START       UINT64_C(0x000300000000)
#define FS_FILE_MAP_END         UINT64_C(0x002300000000)
