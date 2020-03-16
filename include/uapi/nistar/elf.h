#pragma once

#include <nistar/syscall.h>

void *load_elf(int fd, usymlink_t *upud, char *name, uintptr_t *basep);
