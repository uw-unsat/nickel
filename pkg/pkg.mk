# libc
include pkg/musl.mk

# libc required
include pkg/compiler-rt.mk
include pkg/libbacktrace.mk

include pkg/picosat.mk
include pkg/boolector.mk

include pkg/riscvemu.mk
include pkg/sparse.mk
include pkg/sqlite3.mk
include pkg/tcc.mk
include pkg/toybox.mk
include pkg/ubpf.mk
include pkg/uno.mk

# libc not required
include pkg/uip.mk
