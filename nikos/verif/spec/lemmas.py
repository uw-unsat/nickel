import z3

import libirpy.util as util

import datatypes as dt


def current_is_valid(s):
    return z3.And(
            dt.is_proc_valid(s.current),
            s.current != 0,
            s.procs[s.current].state == dt.PROC_STATE_RUN)


def proc_state_free_or_run(s):
    pid = util.FreshBitVec('pid', dt.pid_t)
    return z3.ForAll([pid], z3.Implies(
            dt.is_proc_valid(pid),
            z3.Or(
                s.procs[pid].state == dt.PROC_STATE_RUN,
                s.procs[pid].state == dt.PROC_STATE_FREE)))

def pgwalk_ok(s):
    pid = util.FreshBitVec('pid', dt.pid_t)
    idx = util.FreshBitVec('idx', dt.uint64_t)
    return z3.ForAll([pid, idx], z3.Implies(
        z3.And(
            dt.is_proc_valid(pid),
            s.procs[pid].state == dt.PROC_STATE_RUN,
        ),
        z3.And(
            z3.Implies(
                s.procs[pid].pgtable(idx) != 0,
                z3.And(
                    dt.is_page_valid(s.procs[pid].pgtable(idx)),
                    s.pages[s.procs[pid].pgtable(idx)].inv == idx,
                    z3.Not(s.pages[s.procs[pid].pgtable(idx)].free),
                    s.pages[s.procs[pid].pgtable(idx)].owner == pid))
        )))


def parent_valid(s):
    pid = util.FreshBitVec('pid', dt.pid_t)
    return z3.ForAll([pid],
            z3.Implies(s.procs[pid].state == dt.PROC_STATE_RUN,
                       s.procs[dt.parent(pid)].state == dt.PROC_STATE_RUN))


def child_free(s):
    pid = util.FreshBitVec('pid', dt.pid_t)
    child = util.FreshBitVec('child', dt.pid_t)
    return z3.ForAll([pid, child],
            util.Implies(
                dt.is_proc_valid(pid),
                dt.is_proc_valid(child),
                util.Implies(
                    s.procs[pid].state == dt.PROC_STATE_RUN,
                    dt.is_free_child(s, pid, child),
                    s.procs[child].state == dt.PROC_STATE_FREE)))


def nr_children_valid(s):
    pid = util.FreshBitVec('pid', dt.pid_t)
    return z3.ForAll([pid],
            util.Implies(
                dt.is_proc_valid(pid),
                z3.ULE(s.procs[pid].nr_children, dt.NR_CHILDREN)))


def spec_to_lemma(name):
    return [
        current_is_valid,
        parent_valid,
        pgwalk_ok,
        nr_children_valid,
        proc_state_free_or_run,
        child_free
    ]
