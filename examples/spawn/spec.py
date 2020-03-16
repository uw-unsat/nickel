import z3
import errno

import libirpy.util as util
import datatypes as dt

def sys_broken_spawn(old):
    child_pid = old.nr_procs + 1

    cond = util.Cases(
        (z3.UGE(child_pid, dt.NR_PROCS), -errno.ENOMEM),
        default=child_pid,
    )

    new = old.copy()

    new.nr_procs += 1

    return cond, util.If(cond.cond(), old, new)


def sys_spawn(old):
    child_pid = old.current * dt.NR_CHILDREN + old.procs[old.current].nr_children + 1

    cond = util.Cases(
        (z3.UGE(old.procs[old.current].nr_children, dt.NR_CHILDREN), -errno.ENOMEM),
        (z3.UGE(child_pid, dt.NR_PROCS), -errno.ENOMEM),
        default=child_pid,
    )

    new = old.copy()

    new.procs[old.current].nr_children += 1

    return cond, util.If(cond.cond(), old, new)
