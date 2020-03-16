import z3

from libirpy import util

import datatypes as dt


def impl_invariants(ctx):
    conj = []

    conj.append(dt.is_proc_valid(util.global_value(ctx, '@current_pid')))

    return z3.And(*conj)
