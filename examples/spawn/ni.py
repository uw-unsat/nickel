import z3
import libirpy.util as util

import datatypes as dt


def domains():
    return [
        Domain(util.FreshBitVec('dom_pid', dt.pid_t)),
    ]


class Domain(object):
    def __init__(self, pid):
        self.pid = pid

    def can_flow_to(self, other):
        return self.pid == other.pid

    interferes = can_flow_to

    def __eq__(self, other):
        return self.pid == other.pid


def obs_equivalence(s1, s2, dom):
    pid = dom.pid

    return z3.And(
        s1.current == s2.current,
        s1.nr_procs == s2.nr_procs,
        s1.procs[pid].nr_children == s2.procs[pid].nr_children,
    )
