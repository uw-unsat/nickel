import z3
import errno

import libirpy.util as util
import datatypes as dt


def sys_get_quota(old):
    return util.Cases(default=old.procs[old.current].nr_free_pages), old


def sys_spawn(old, fileid, quota):
    pid = old.current * dt.NR_CHILDREN + old.procs[old.current].nr_children + 1

    cond = util.Cases(
            (z3.UGE(fileid, dt.NR_ELF_FILES), -errno.EINVAL),
            (z3.ULT(old.procs[old.current].nr_free_pages, quota), -errno.EINVAL),
            (z3.UGE(old.procs[old.current].nr_children, dt.NR_CHILDREN), -errno.ENOMEM),
            (z3.UGE(pid, dt.NR_PROCS), -errno.ENOMEM),
            default=pid,
    )

    new = old.copy()

    new.procs[old.current].nr_free_pages -= quota
    new.procs[old.current].nr_children += 1

    new.procs[pid].state = dt.PROC_STATE_RUN
    new.procs[pid].fileid = fileid
    new.procs[pid].nr_free_pages = quota
    new.procs[pid].nr_children = 0
    new.procs[pid].pgtable = util.i64(0)
    new.procs[pid].prev = old.current
    new.procs[pid].next = old.procs[old.current].next
    new.procs[pid].outidx = 0

    new.procs[old.current].next = pid

    return cond, util.If(cond.cond(negate=True), new, old)


def handle_page_fault(old, idx):
    pid = old.current

    val = old.procs[pid].pgtable(idx)

    cond = util.Cases(
            (z3.Not(dt.is_idx_valid(idx)), -errno.EINVAL),
            (val == 0, -errno.EINVAL),
            default=util.i64(0))

    new = old.copy()

    newpg = new.alloc_page()

    new.procs[pid].pgtable[idx] = newpg

    new.pages[newpg].owner = pid
    new.pages[newpg].free = False
    new.pages[newpg].inv = idx

    # elf loading
    elf = new.files[new.procs[pid].fileid].data
    new.pages[newpg].data = lambda pn, off, oldfn: util.If(pn == newpg,
        util.If(idx == dt.ELF_VA_SLOT, elf(off), util.i64(0)), oldfn(pn, off))

    return cond, util.If(cond.cond(negate=True), new, old)


def sys_write(old, idx1, idx2, value):
    cond = util.Cases(
        (z3.Not(dt.is_idx_valid(idx1)), -errno.EINVAL),
        (z3.Not(dt.is_off_valid(idx2)), -errno.EINVAL),
        (z3.Not(dt.is_page_valid(old.procs[old.current].pgtable(idx1))), -errno.EINVAL),
        default=util.i64(0))

    new = old.copy()

    pg = old.procs[old.current].pgtable(idx1)
    new.pages[pg].data[idx2] = value

    return cond, util.If(cond.cond(negate=True), new, old)


def sys_read(old, idx1, idx2):
    data = old.pages[old.procs[old.current].pgtable(idx1)].data(idx2)

    cond = util.Cases(
        (z3.Not(dt.is_idx_valid(idx1)), -errno.EINVAL),
        (z3.Not(dt.is_off_valid(idx2)), -errno.EINVAL),
        (z3.Not(dt.is_page_valid(old.procs[old.current].pgtable(idx1))), -errno.EINVAL),
        default=data)

    return cond, old


def sys_yield(old):
    next = old.procs[old.current].next
    cond = util.Cases(
        (z3.Not(dt.is_proc_valid(next)), -errno.EINVAL),
        (next == 0, -errno.EINVAL),
        (old.procs[next].state != dt.PROC_STATE_RUN, -errno.EINVAL),
        default=util.i64(0)
    )
    new = old.copy()
    new.current = next
    return cond, util.If(cond.cond(negate=True), new, old)


def sys_putchar(old, c):
    cond = util.Cases(
        default=util.i64(0)
    )

    new = old.copy()
    idx = old.procs[old.current].outidx
    old.procs[old.current].outidx += 1
    new.procs[old.current].outbuffer[idx] = c

    return cond, new
