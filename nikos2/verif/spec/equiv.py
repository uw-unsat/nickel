import sys
import z3

import libirpy.util as util

import datatypes as dt
import invariants


def proc_field_equiv(pid, ctx, kernelstate, fieldname):
    return z3.ForAll([pid], z3.Implies(
        dt.is_proc_valid(pid),
        getattr(kernelstate.procs[pid], fieldname) ==
        util.global_field_element(ctx, '@procs', fieldname, pid)))


def procs_equiv(conj, ctx, kernelstate):
    pid = util.FreshBitVec('pid', dt.pid_t)

    conj.append(proc_field_equiv(pid, ctx, kernelstate, 'state'))
    conj.append(proc_field_equiv(pid, ctx, kernelstate, 'nr_free_pages'))
    conj.append(proc_field_equiv(pid, ctx, kernelstate, 'nr_children'))
    conj.append(proc_field_equiv(pid, ctx, kernelstate, 'fileid'))


def pages_equiv(conj, ctx, kernelstate):
    pass


def files_equiv(conj, ctx, kernelstate):
    pass


def state_equiv(ctx, kernelstate):
    conj = []

    module = sys.modules[__name__]
    for k in kernelstate._meta.keys():
        if not k in kernelstate._structs:
            continue
        getattr(module, k + '_equiv')(conj, ctx, kernelstate)

    conj.append(kernelstate.current == kernelstate.sched_list(kernelstate.current_idx))

    conj.append(util.global_value(ctx, '@current_idx') == kernelstate.current_idx)
    conj.append(util.global_value(ctx, '@current_pid') == kernelstate.current)

    idx = util.FreshBitVec('idx', dt.size_t)
    conj.append(z3.ForAll([idx], z3.Implies(
        dt.is_sched_idx_valid(idx),
        kernelstate.sched_list(idx) ==
        util.global_to_uf_dict(ctx, '@sched_list')[()](util.i64(0), idx))))

    conj.append(invariants.impl_invariants(ctx))

    return z3.And(*conj)
