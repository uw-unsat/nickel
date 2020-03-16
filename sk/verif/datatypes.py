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
uint32_t     = td.uint32_t
size_t       = td.uint64_t
bool_t       = td.bool_t


partition_t       = uint32_t
pid_t             = uint64_t
port_name_t       = z3.StringSort()
port_id_t         = uint64_t
port_type_t       = uint64_t
port_direction_t  = uint64_t
time_t            = uint64_t
buffer_size_t     = uint64_t
message_t         = z3.StringSort()
status_t          = uint64_t


# Port Direction
PORT_DIRECTION_SOURCE = 0
PORT_DIRECTION_DESTINATION = 1

# Port Types
PORT_TYPE_QUEUEING = 0
PORT_TYPE_SAMPLING = 1


PORT_INVALID = z3.BoolVal(False)
PORT_VALID   = z3.BoolVal(True)
port_valid_t = bool_t


# Error code
NO_ERROR        = z3.BitVecVal( 0, 64)
NO_ACTION       = z3.BitVecVal(-1, 64)
NOT_AVAILABLE   = z3.BitVecVal(-2, 64)
INVALID_PARAM   = z3.BitVecVal(-3, 64)
INVALID_CONFIG  = z3.BitVecVal(-4, 64)
INVALID_MODE    = z3.BitVecVal(-5, 64)
TIMED_OUT       = z3.BitVecVal(-6, 64)


# Proc status
PROC_DORMANT     = z3.BitVecVal(0, status_t)
PROC_READY       = z3.BitVecVal(1, status_t)
PROC_RUNNING     = z3.BitVecVal(2, status_t)
PROC_WAITING     = z3.BitVecVal(3, status_t)
PROC_STATUS_LAST = z3.BitVecVal(4, status_t)

NR_PARTITIONS = 8

def is_partition_valid(part):
    return z3.BoolVal(True)
    # return z3.ULT(part, NR_PARTITIONS)


def port_id_partition(port):
    assert port.size() == 64
    return z3.Extract(63, 32, port)
