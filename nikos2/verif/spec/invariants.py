import z3

from libirpy import util

import datatypes as dt


def impl_invariants(ctx):
    conj = []

    conj.append(dt.is_proc_valid(util.global_value(ctx, '@current_pid')))
    conj.append(dt.is_sched_idx_valid(util.global_value(ctx, '@current_idx')))


    idx = util.FreshBitVec('idx', dt.size_t)
    conj.append(z3.ForAll([idx], z3.Implies(
        dt.is_sched_idx_valid(idx),
        dt.is_proc_valid(util.global_to_uf_dict(ctx, '@sched_list')[()](util.i64(0), idx)))))

    return z3.And(*conj)
