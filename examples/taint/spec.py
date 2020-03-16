import z3
import errno

import libirpy.util as util
import datatypes as dt


def sys_get(old):
    cond = util.Cases(
        default=old.procs[old.current].value
    )

    return cond, old


def sys_get_level(old):
    cond = util.Cases(
        default=util.If(old.procs[old.current].level == dt.TAINTED, util.i64(1), util.i64(0))
    )

    return cond, old


def sys_send(old, dst, value):
    src = old.current

    cond = util.Cases(
        # a real system should validate dst
        # removing this check will break NI
        (z3.And(old.procs[src].level == dt.TAINTED,
                old.procs[dst].level == dt.UNTAINTED), -errno.EINVAL),
        default=util.i64(0),
    )

    new = old.copy()

    new.procs[dst].value = value

    return cond, util.If(cond.cond(), old, new)


def sys_send_floating(old, dst, value):
    src = old.current

    cond = util.Cases(
        default=util.i64(0),
    )

    new = old.copy()

    new.procs[dst].value = value
    # bump dst level to tainted from untainted if current is tainted
    new.procs[dst].level = util.If(
        z3.And(
            old.procs[src].level == dt.TAINTED,
            old.procs[dst].level == dt.UNTAINTED
        ),
        dt.TAINTED,
        old.procs[dst].level
    )

    return cond, util.If(cond.cond(), old, new)


def sys_raise(old):
    cond = util.Cases(
        default=util.i64(0)
    )

    new = old.copy()

    # change to dt.UNTAINTED will break NI
    new.procs[new.current].level = dt.TAINTED

    return cond, new
