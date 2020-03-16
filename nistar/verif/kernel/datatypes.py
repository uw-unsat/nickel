import sys
import z3
import copy
from collections import namedtuple

import cparser

import libirpy.datatypes as dt
import libirpy.itypes as itypes
import libirpy.util as util
import libirpy.typedefs as td

import spec


nistar_types = cparser.parse('include/uapi/nistar/types.h')
proc_flags = cparser.parse('include/asm/processor-flags.h')
mmu = cparser.parse('include/io/mmu.h')


def get_macro(state, name):
    val = state.macros[name].rightside.strip()
    try:
        return int(val)
    except:
        return val


# populate irpy typedefs (mostly for other modules to use)
def _populate_types():
    module = sys.modules[__name__]
    for k in dir(td):
        if k.startswith('_'):
            continue
        setattr(module, k, getattr(td, k))

_populate_types()


def BIT64(i):
    return z3.BitVecVal(1 << i, 64)


# 4 pages
KPAGE_SIZE           = 4096 * 4 / 8
PAGE2M_SIZE          = 4096 * 512 / 8
CONTAINER_NR_PAGES   = KPAGE_SIZE
LABEL_NR_TAGS        = KPAGE_SIZE / 2
SCHED_NR_QUANTA      = get_macro(nistar_types, 'SCHED_NR_QUANTA')
PGTABLE_NR_PTES      = get_macro(nistar_types, 'PGTABLE_NR_PTES')
DIRECTORY_NR_ENTRIES = get_macro(nistar_types, 'PGTABLE_NR_PTES')

IDLE_THREAD         = 0


MAX_VAL            = lambda n: z3.BitVecVal(2 ** n.size() - 1, n.size())
PAGE_ID_INVALID    = td.MAX_INT64
PAGE2M_ID_INVALID  = td.MAX_INT64
TAG_INVALID        = td.MAX_INT128


TLS_NR_SLOTS   = ((2 << 20) / 8)
USER_TLS_SIZE  = 4096
USER_TLS_END   = 0x7fffffe00000
USER_TLS_START = (USER_TLS_END - USER_TLS_SIZE)
USER_STACK_TOP = USER_TLS_START


PAGE_NAME_LEN = 32 / 8
PAGE_METADATA_LEN = 96 / 8


# page types
PAGE_TYPE_NONE       =  0
PAGE_TYPE_UNTYPED    =  1
PAGE_TYPE_LABEL      =  2
PAGE_TYPE_CONTAINER  =  3
PAGE_TYPE_PGD        =  4
PAGE_TYPE_PUD        =  5
PAGE_TYPE_PMD        =  6
PAGE_TYPE_GATE       =  7
PAGE_TYPE_THREAD     =  8
PAGE_TYPE_BLOCK      =  9
PAGE_TYPE_LAST       =  10
PAGE_TYPE_RESERVED   =  11

THREAD_STATE_NONE      =  0
THREAD_STATE_RUNNABLE  =  1
THREAD_STATE_HALTED    =  2

LABEL_TYPE_SECRECY = 0
LABEL_TYPE_INTEGRITY = 1
LABEL_TYPE_THREAD_OWNERSHIP = 2
LABEL_TYPE_GATE_OWNERSHIP = 3
LABEL_TYPE_GATE_GUARD = 4
LABEL_TYPE_LAST = 5

NR_PAGES   = 8192
NR_PAGES2M = 512

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


def page_type_normal(type):
    return z3.And(
            type != PAGE_TYPE_NONE,
            type != PAGE_TYPE_LABEL,
            type != PAGE_TYPE_LAST,
            type != PAGE_TYPE_RESERVED)


def quantum_is_valid(id):
        return z3.ULT(id, SCHED_NR_QUANTA)


def page_is_valid(id):
        return z3.ULT(id, NR_PAGES)


def upage_is_valid(id):
        return z3.ULT(id, NR_PAGES2M)


page2m_is_valid = upage_is_valid


# Shut up python linters about undef variables
uint128_t    = td.uint128_t
uint64_t     = td.uint64_t
size_t       = td.uint64_t
bool_t       = td.bool_t
tag_t        = td.uint128_t
page_id_t    = td.uint64_t
upage_id_t   = td.uint64_t
quantum_id_t = td.uint64_t
gen_t        = td.uint64_t


def FreshStructPtr(ctx, name, sname):
    return dt.fresh_ptr(ctx, util.fresh_name(name), itypes.parse_type(ctx, sname))


Domain = namedtuple('Domain', ['secrecy', 'integrity', 'ownership'])


class Label(object):
    def __init__(self, has, idx, tags, data, id=None, check=False):
        self.has = has
        self.idx = idx
        self.tags = tags
        self.data = data
        self.gep_idx = z3.BitVecVal(0, size_t)
        self.id = id
        self.check = check

    def __repr__(self):
        return "<{!r}, {!r}, {!r}, {!r}>".format(self.has, self.idx, self.tags, self.data)

    def __str__(self):
        return "<{!r}, {!r}, {!r}, {!r}>".format(self.has, self.idx, self.tags, self.data)

    def copy(self):
        return copy.deepcopy(self)

    def ite(self, other, cond):
        if self is other:
            return self

        return Label(util.If(cond, self.has, other.has),
                     util.If(cond, self.idx, other.idx),
                     util.If(cond, self.tags, other.tags),
                     util.If(cond, self.data, other.data))

    def construct_type(self, ctx):
        return itypes.parse_type(ctx, '%struct.label*')

    def packing_invariants(self):
        """Emit packing invariants"""
        has = self.has
        idx = self.idx
        tags = self.tags
        data = self.data

        conj = []

        slot = util.FreshBitVec('pack.slot', uint64_t)
        tag = util.FreshBitVec('pack.tag', tag_t)

        # For every tag in data, label `has` that tag.
        # except for holes in the array for TAG_INVALID
        conj.append(z3.ForAll([slot], z3.Implies(
            z3.And(
                tags(slot) != TAG_INVALID,
                z3.ULT(slot, LABEL_NR_TAGS)),
            has(tags(slot)))))

        # idx is always valid
        conj.append(z3.ForAll([tag], z3.Implies(has(tag),
            z3.ULT(idx(tag), LABEL_NR_TAGS))))

        # has(tag) (by-)implies idx inverses data
        conj.append(z3.ForAll([tag], z3.Implies(
            tag != TAG_INVALID,
            has(tag) == (tags(idx(tag)) == tag))))

        # no label contains TAG_INVALID
        conj.append(z3.Not(has(TAG_INVALID)))

        # data and tag correspondance
        conj.append(z3.ForAll([slot], z3.Implies(z3.ULT(slot, LABEL_NR_TAGS),
            z3.Concat(data(slot * 2 + 1), data(slot * 2)) == tags(slot))))

        return z3.And(*conj)

    def invariants(self, kernelstate=None, ctx=None):
        conj = []
        if kernelstate:
            if self.check:
                conj.append(spec.lemmas.label_tags_unused(kernelstate, self.has))
        return z3.And(*conj)

    def getelementptr(self, ctx, a, b, c, type=None):
        other = self.copy()
        assert util.as_long(a) == 0
        assert util.as_long(b) == 0
        other.gep_idx += c
        return other

    def read(self, ctx):
        return z3.Concat(self.data.getelementptr(ctx, self.gep_idx * 2 + 1).read(ctx),
                         self.data.getelementptr(ctx, self.gep_idx * 2).read(ctx))

    def write(self, ctx, tag):
        tag_hi = z3.Extract(127, 64, tag)
        tag_lo = z3.Extract(63, 0, tag)
        self.data.getelementptr(ctx, self.gep_idx * 2).write(ctx, tag_lo)
        self.data.getelementptr(ctx, self.gep_idx * 2 + 1).write(ctx, tag_hi)
        ctx.globals['#label'].label[self.id][tag] = True


def FreshLabel(name, check=False):
    has = util.FreshFunction("{}.has".format(name), tag_t, bool_t)
    idx = util.FreshFunction("{}.idx".format(name), tag_t, uint64_t)
    tags = util.FreshFunction("{}.tags".format(name), uint64_t, tag_t)
    data = util.FreshFunction("{}.data".format(name), uint64_t, uint64_t)
    return Label(has, idx, tags, data, check=check)
