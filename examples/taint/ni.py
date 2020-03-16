import z3
import libirpy.util as util
import datatypes as dt


def domains():
    return [
        ("untainted", Domain(dt.UNTAINTED)),
        ("tainted", Domain(dt.TAINTED)),
    ]


class Domain(object):
    def __init__(self, level):
        self.level = level

    def interferes(self, other):
        return z3.Or(
            self.level == other.level,
            z3.And(self.level == dt.UNTAINTED, other.level == dt.TAINTED),
        )

    def __eq__(self, other):
        return self.level == other.level


def obs_equivalence(s1, s2, dom):
    pid = util.FreshBitVec('pid', dt.pid_t)

    return z3.And(
        s1.current == s2.current,

        z3.ForAll([pid], z3.Implies(
            z3.Or(
                s1.procs[pid].level == dt.UNTAINTED,
                s2.procs[pid].level == dt.UNTAINTED,
                dom.level == dt.TAINTED,
            ),
            z3.And(
                s1.procs[pid].level == s2.procs[pid].level,
                s1.procs[pid].value == s2.procs[pid].value,
            )
        ))
    )
