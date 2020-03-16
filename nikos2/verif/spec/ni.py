import z3

import libirpy.util as util

import datatypes as dt


class ProcDomain(object):
    def __init__(self, pid):
        self.pid = pid

    def valid(self):
        return z3.ULT(self.pid, dt.NR_PROCS)

    def interferes(self, other, state=None):
        return z3.Or(self.pid == other.pid,
                     self.pid == 0,
                     dt.descendant(other.pid, self.pid))

    def __eq__(self, other):
        return self.pid == other.pid


def obs_equivalence_sched(s1, s2):
    return s1.current_idx == s2.current_idx


def obs_eqv_sched_list(s1, s2, dom):
    conj = []

    pid = dom.pid

    child = util.FreshBitVec('chld', dt.pid_t)
    conj.append(z3.ForAll([child],
        util.Implies(
            dt.is_proc_valid(child),
            z3.Or(
                s1.sched_list(child) == pid,
                s2.sched_list(child) == pid),
            s1.sched_list(child) == s2.sched_list(child))))

    conj.append(s1.sched_list(pid) == s2.sched_list(pid))
    conj.append(s1.sched_list(dt.parent(pid)) == s2.sched_list(dt.parent(pid)))
    conj.append(s1.sched_list(dt.parent(dt.parent(pid))) ==
            s2.sched_list(dt.parent(dt.parent(pid))))
    conj.append(s1.sched_list(dt.parent(dt.parent(dt.parent(pid)))) ==
            s2.sched_list(dt.parent(dt.parent(dt.parent(pid)))))

    conj.append(s1.procs[dt.parent(pid)].nr_children ==
                s2.procs[dt.parent(pid)].nr_children)
    conj.append(s1.procs[dt.parent(dt.parent(pid))].nr_children ==
                s2.procs[dt.parent(dt.parent(pid))].nr_children)
    conj.append(s1.procs[dt.parent(dt.parent(dt.parent(pid)))].nr_children ==
                s2.procs[dt.parent(dt.parent(dt.parent(pid)))].nr_children)


    return z3.And(*conj)

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
            s1.procs[pid].state == s2.procs[pid].state,
            s1.current_idx == s2.current_idx,
            obs_eqv_sched_list(s1, s2, dom),

            z3.Or(
                s1.procs[pid].state == dt.PROC_STATE_FREE,
                s2.procs[pid].state == dt.PROC_STATE_FREE,
                z3.Implies(dt.is_proc_valid(dom.pid), z3.And(*conj)),
            ))
