import z3

import libirpy.util as util

import datatypes as dt


class ProcDomain(object):
    def __init__(self, pid):
        self.pid = pid

    def interferes(self, other):
        return z3.Or(self.pid == other.pid,
                     self.pid == 0,
                     other.pid == 0)

    def __eq__(self, other):
        return self.pid == other.pid


def obs_equivalence_sched(s1, s2):
    pid = util.FreshBitVec('pid', dt.pid_t)
    return z3.ForAll([pid],
            util.Implies(dt.is_proc_valid(pid),
                z3.And(
                    s1.procs[pid].state == s2.procs[pid].state,
                    s1.procs[pid].next == s2.procs[pid].next,
                    s1.procs[pid].prev == s2.procs[pid].prev)))


def obs_equivalence(s1, s2, dom):
    conj = []

    pid = dom.pid

    conj.append(s1.procs[pid].state == s2.procs[pid].state)
    conj.append(s1.procs[pid].nr_free_pages == s2.procs[pid].nr_free_pages)
    conj.append(s1.procs[pid].nr_children == s2.procs[pid].nr_children)
    conj.append(s1.procs[pid].outidx == s2.procs[pid].outidx)

    idx1 = util.FreshBitVec('idx1', dt.uint64_t)
    idx2 = util.FreshBitVec('idx2', dt.uint64_t)

    conj.append(z3.ForAll([idx1, idx2], z3.Implies(
        z3.And(
            dt.is_idx_valid(idx1),
            dt.is_off_valid(idx2),
        ),
        z3.And(
            # The page table structure has to be the same in both states
            dt.is_page_valid(s1.procs[pid].pgtable(idx1)) == dt.is_page_valid(s2.procs[pid].pgtable(idx1)),
            z3.Implies(
                dt.is_page_valid(s1.procs[pid].pgtable(idx1)),
                s1.pages[s1.procs[pid].pgtable(idx1)].data(idx2) ==
                s2.pages[s2.procs[pid].pgtable(idx1)].data(idx2))

        ))))

    fileid = util.FreshBitVec('fileid', dt.uint64_t)
    off = util.FreshBitVec('off', dt.uint64_t)
    conj.append(z3.ForAll([fileid], s1.files[fileid].entry == s2.files[fileid].entry))
    conj.append(z3.ForAll([fileid, off], z3.Implies(
        dt.is_off_valid(off),
        s1.files[fileid].data(off) == s2.files[fileid].data(off)
    )))

    conj.append(s1.procs[pid].fileid == s2.procs[pid].fileid)

    return z3.And(
            s1.current == s2.current,
            z3.Implies(dom.pid == 0, obs_equivalence_sched(s1, s2)),
            z3.Or(
                s1.procs[pid].state == dt.PROC_STATE_FREE,
                s2.procs[pid].state == dt.PROC_STATE_FREE,
                z3.Implies(dt.is_proc_valid(dom.pid), z3.And(*conj)),
            ))
