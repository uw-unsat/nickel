import z3

import libirpy.util as util
from libirpy.state import BaseStruct, Struct, Map

import spec.label as l
import datatypes as dt


class ImplLabel(BaseStruct):
    label = Map(dt.page_id_t, dt.tag_t, dt.bool_t)

    def add(self, a, tag):
        self.label[a][tag] = z3.BoolVal(True)

    def has(self, a, tag):
        return self.label(a, tag)

    def is_empty(self, a):
        return l.is_empty(self.label[a])

    def is_subset(self, a, b):
        return l.is_subset(self.label[a], self.label[b])

    def is_subsetx(self, a, b, x):
        return l.is_subsetx(self.label[a], self.label[b], self.label[x])


class Label(Struct):
    label = Map(dt.page_id_t, dt.tag_t, dt.bool_t)
    idx = Map(dt.page_id_t, dt.tag_t, dt.uint64_t)
    data = Map(dt.page_id_t, dt.uint64_t, dt.tag_t)

    def add(self, a, tag):
        self.label[a][tag] = z3.BoolVal(True)

    def has(self, a, tag):
        return self.label(a, tag)

    def is_empty(self, a):
        return l.is_empty(self.label[a])

    def is_subset(self, a, b):
        return l.is_subset(self.label[a], self.label[b])

    def is_subsetx(self, a, b, x):
        return l.is_subsetx(self.label[a], self.label[b], self.label[x])


def get_id(O):
    if isinstance(O, tuple) or isinstance(O, list):
        return O[0]
    return O


class Pages(Struct):
    generation = Map(dt.page_id_t, dt.gen_t)
    type = Map(dt.page_id_t, dt.uint64_t)

    secrecy = Map(dt.page_id_t, dt.page_id_t)
    integrity = Map(dt.page_id_t, dt.page_id_t)

    name = Map(dt.page_id_t, dt.uint64_t, dt.uint64_t)
    metadata = Map(dt.page_id_t, dt.uint64_t, dt.uint64_t)

    parent      = Map(dt.page_id_t, dt.page_id_t)
    parent_slot = Map(dt.page_id_t, dt.size_t)

    tag_counter = Map(dt.page_id_t, dt.uint64_t)

    next  = Map(dt.page_id_t, dt.page_id_t)
    unext = Map(dt.page_id_t, dt.upage_id_t)

    # per container page freelist
    list = Map(dt.page_id_t, dt.size_t, dt.page_id_t)
    list_inv = Map(dt.page_id_t, dt.page_id_t, dt.size_t)

    # per container page2m freelist
    ulist = Map(dt.page_id_t, dt.size_t, dt.upage_id_t)
    ulist_inv = Map(dt.page_id_t, dt.upage_id_t, dt.size_t)

    quota  = Map(dt.page_id_t, dt.uint64_t)
    uquota = Map(dt.page_id_t, dt.uint64_t)
    qquota = Map(dt.page_id_t, dt.uint64_t)

    # the owner of a label page
    label_owner = Map(dt.page_id_t, dt.page_id_t)
    label_type  = Map(dt.page_id_t, dt.size_t)

    # owner of a tls block
    is_tls    = Map(dt.page_id_t, dt.bool_t)
    tls_owner = Map(dt.page_id_t, dt.page_id_t)

    # This goes away eventually..
    data = Map(dt.page_id_t, dt.uint64_t, dt.uint64_t)

    # Data union types
    label = Label()

    def freelist_pop(self, id):
        popped = self[id].next
        self[id].next = self[popped].next
        self[id].quota -= 1

        self.list = lambda cid, idx, oldfn: \
                util.If(cid == id,
                        util.If(z3.And(cid == id, idx+1 == dt.NR_PAGES),
                            popped,
                            oldfn(cid, idx+1)),
                        util.If(z3.And(cid == id, idx == dt.NR_PAGES),
                            popped,
                            oldfn(cid, idx)))

        self.list_inv = lambda cid, pn, oldfn: \
                util.If(cid == id,
                        util.If(z3.And(cid == id, pn == popped),
                            dt.i64(dt.NR_PAGES),
                            oldfn(cid, pn))-1,
                        util.If(z3.And(cid == id, pn == popped),
                            dt.i64(dt.NR_PAGES),
                            oldfn(cid, pn)))
        return popped

    def freelist_push(self, id, pid):
        self[id].quota += 1

        pos = self[id].list_inv(pid)
        last = self[id].list(dt.NR_PAGES-1)

        self.list = lambda cid, idx, oldfn: \
                util.If(z3.And(cid == id, idx == 0),
                        pid,
                        util.If(cid == id,
                                util.If(idx-1 == pos,
                                        last,
                                        oldfn(cid, idx-1)),
                                oldfn(cid, idx)))

        self.list_inv = lambda cid, pn, oldfn: \
                util.If(z3.And(cid == id, pn == pid),
                        dt.i64(0),
                        util.If(cid == id,
                            util.If(pn == last,
                                    pos,
                                    oldfn(cid, pn))+1,
                            oldfn(cid, pn)))

        # Set `pid` as head of the list
        self[pid].parent = id
        self[pid].next = self[id].next
        self[id].next = pid

    def is_type(self, O, type):
        conj = []
        if isinstance(O, tuple) or isinstance(O, list):
            conj.append(self.generation(O[0]) == O[1])
            id = O[0]
        else:
            id = O

        conj.append(dt.page_is_valid(id))
        conj.append(self.type(id) == type)

        return z3.And(*conj)

    def is_valid(self, O):
        conj = []
        if isinstance(O, tuple) or isinstance(O, list):
            conj.append(self.generation(O[0]) == O[1])
            id = O[0]
        else:
            id = O

        conj.append(dt.page_is_valid(id))

        return z3.And(*conj)

    def ownership(self, T):
        return self.data(T, util.i64(0))

    def gate_guard(self, T):
        return self.data(T, util.i64(1))

    def secrecy_label(self, T):
        return self.label[self.secrecy(T)].label

    def integrity_label(self, T):
        return self.label[self.integrity(T)].label

    def ownership_label(self, T):
        return self.label[self.ownership(T)].label

    def can_read_write(self, T, O):
        O = get_id(O)
        T = get_id(T)
        return z3.And(self.can_read(T, O), self.can_write(T, O))

    def can_write(self, T, O):
        O = get_id(O)
        T = get_id(T)
        r1 = self.label.is_subsetx(self.secrecy(T), self.secrecy(O), self.ownership(T))
        r2 = self.label.is_subsetx(self.integrity(O), self.integrity(T), self.ownership(T))
        return z3.And(r1, r2)

    def can_read(self, T, O):
        O = get_id(O)
        T = get_id(T)
        r1 = self.label.is_subsetx(self.secrecy(O), self.secrecy(T), self.ownership(T))
        r2 = self.label.is_subsetx(self.integrity(T), self.integrity(O), self.ownership(T))
        return z3.And(r1, r2)


class UPages(Struct):
    available = Map(dt.upage_id_t, dt.bool_t)
    parent = Map(dt.upage_id_t, dt.page_id_t)
    next = Map(dt.upage_id_t, dt.upage_id_t)
    data = Map(dt.upage_id_t, dt.uint64_t, dt.uint64_t)


class Time(Struct):
    container = Map(dt.quantum_id_t, dt.page_id_t)
    thread    = Map(dt.quantum_id_t, dt.page_id_t)


class NistarState(BaseStruct):
    root_container_id = Map(dt.page_id_t)
    current_slot = Map(dt.uint64_t)
    idle = Map(dt.page_id_t)

    @property
    def current(self):
        t = self.time[self.current_slot].thread

        cond = z3.And(
            self.pages.is_type(t, dt.PAGE_TYPE_THREAD),
            self.pages[t].data(2) == dt.THREAD_STATE_RUNNABLE,
            self.pages.can_read(t, self.time[self.current_slot].container),
        )

        return util.If(cond, t, self.idle)

    _tls = Map(dt.page_id_t, dt.uint64_t, dt.uint64_t)
    @property
    def tls(self):
        return self._tls[self.current]

    pages = Pages()
    upages = UPages()
    time = Time()
