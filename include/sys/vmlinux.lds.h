#pragma once

#include <asm/setup.h>
#include <io/mmu.h>
#include <io/sizes.h>

#define __VMLINUX_SYMBOL(x)     x
#define __VMLINUX_SYMBOL_STR(x) #x

/* Indirect, so macros are expanded before pasting. */
#define VMLINUX_SYMBOL(x)       __VMLINUX_SYMBOL(x)
#define VMLINUX_SYMBOL_STR(x)   __VMLINUX_SYMBOL_STR(x)

/* Align . to a 8 byte boundary equals to maximum function alignment. */
#define ALIGN_FUNCTION()        . = ALIGN(8)

/* Section used for early init (in .S files) */
#define HEAD_TEXT  *(.head.text)

#define ENTRY_TEXT                                                      \
                . = ALIGN(PAGE_SIZE);                                   \
                VMLINUX_SYMBOL(__entry_text_start) = .;                 \
                *(.entry.text)                                          \
                . = ALIGN(PAGE_SIZE);                                   \
                VMLINUX_SYMBOL(__entry_text_end) = .;

#define ENTRY_TRAMPOLINE                                                \
                . = ALIGN(PAGE_SIZE);                                   \
                VMLINUX_SYMBOL(__entry_trampoline) = .;                 \
                *(.entry_trampoline)                                    \
                . = ALIGN(PAGE_SIZE);

#define TEXT_TEXT                                                       \
                ALIGN_FUNCTION();                                       \
                *(.text .text.*)

#define DATA_DATA                                                       \
                *(.data .data.*)
