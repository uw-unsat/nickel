import sys
import z3

import cparser

import libirpy.datatypes as dt
import libirpy.itypes as itypes
import libirpy.util as util
import libirpy.typedefs as td


proc_flags = cparser.parse('include/asm/processor-flags.h')
mmu = cparser.parse('include/io/mmu.h')


def get_macro(state, name):
    val = state.macros[name].rightside.strip()
    try:
        return int(val)
    except:
        return val


# populate irpy typedefs (mostly for other modules t use)

def _populate_types():
    module = sys.modules[__name__]
    for k in dir(td):
        if k.startswith('_'):
            continue
        setattr(module, k, getattr(td, k))

_populate_types()


def BIT64(i):
    return z3.BitVecVal(1 << i, 64)


X86_RFLAGS_IF_BIT = get_macro(proc_flags, 'X86_RFLAGS_IF_BIT')
X86_RFLAGS_IF = BIT64(X86_RFLAGS_IF_BIT)  # Interrupt Flag

PTE_PRESENT  = BIT64(get_macro(mmu, 'PTE_BIT_PRESENT'))
PTE_RW       = BIT64(get_macro(mmu, 'PTE_BIT_RW'))
PTE_USER     = BIT64(get_macro(mmu, 'PTE_BIT_USER'))
PTE_PWT      = BIT64(get_macro(mmu, 'PTE_BIT_PWT'))
PTE_PCD      = BIT64(get_macro(mmu, 'PTE_BIT_PCD'))
PTE_ACCESSED = BIT64(get_macro(mmu, 'PTE_BIT_ACCESSED'))
PTE_DIRTY    = BIT64(get_macro(mmu, 'PTE_BIT_DIRTY'))
PTE_PSE      = BIT64(get_macro(mmu, 'PTE_BIT_PSE'))
PTE_GLOBAL   = BIT64(get_macro(mmu, 'PTE_BIT_GLOBAL'))
PTE_SOFTW1   = BIT64(get_macro(mmu, 'PTE_BIT_SOFTW1'))
PTE_SOFTW2   = BIT64(get_macro(mmu, 'PTE_BIT_SOFTW2'))
PTE_SOFTW3   = BIT64(get_macro(mmu, 'PTE_BIT_SOFTW3'))
PTE_SOFTW4   = BIT64(get_macro(mmu, 'PTE_BIT_SOFTW4'))
PTE_NX       = BIT64(get_macro(mmu, 'PTE_BIT_NX'))


# Shut up python linters about undef variables
uint128_t    = td.uint128_t
uint64_t     = td.uint64_t
size_t       = td.uint64_t
bool_t       = td.bool_t

#
pid_t = uint64_t
page_id_t = uint64_t


NR_PROCS     = 64
NR_CHILDREN  = 4
NR_PAGES     = 16
NR_ELF_FILES = 4


PROC_STATE_FREE = 0
PROC_STATE_RUN  = 1


PID_IDLE = 1

ELF_VA_SLOT = 2


def load_elf(*args, **kwargs):
    return


def is_page_valid(pn):
    return z3.And(z3.UGT(pn, 0), z3.ULT(pn, NR_PAGES))


def is_idx_valid(idx):
    return z3.ULT(idx, 512)


def is_off_valid(idx):
    return z3.ULT(idx, 2 * 1024 * 1024 / 8)


def is_proc_valid(pid):
    return z3.ULT(pid, NR_PROCS)


def parent(pid):
    return util.If(pid == 0, pid, z3.UDiv(pid - 1, NR_CHILDREN))


def is_child(pid, child):
    return z3.And(z3.UGT(pid * NR_CHILDREN, child), z3.ULE(pid * NR_CHILDREN + NR_CHILDREN))


def is_valid_child(state, pid, child):
    return z3.And(z3.UGT(pid * NR_CHILDREN, child),
                  z3.ULE(pid * NR_CHILDREN + state.procs[pid].nr_children, child))


def is_free_child(state, pid, child):
    return z3.And(
        z3.UGT(child, pid * NR_CHILDREN + state.procs[pid].nr_children),
        z3.ULE(child, pid * NR_CHILDREN + NR_CHILDREN))


def FreshStructPtr(ctx, name, sname):
    return dt.fresh_ptr(ctx, util.fresh_name(name), itypes.parse_type(ctx, sname))
