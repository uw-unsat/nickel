import z3
import libirpy.util as util
from libirpy.state import BaseStruct, Struct, Map

import datatypes as dt


class Procs(Struct):
    state = Map(dt.pid_t, dt.uint64_t)

    nr_free_pages = Map(dt.pid_t, dt.uint64_t)
    nr_children = Map(dt.pid_t, dt.uint64_t)

    pgtable = Map(dt.pid_t, dt.uint64_t, dt.page_id_t)
    fileid = Map(dt.pid_t, dt.uint64_t)

    next = Map(dt.pid_t, dt.pid_t)
    prev = Map(dt.pid_t, dt.pid_t)

    outidx = Map(dt.pid_t, z3.IntSort())
    outbuffer = Map(dt.pid_t, z3.IntSort(), dt.uint8_t)


class Pages(Struct):
    free = Map(dt.page_id_t, dt.bool_t)
    owner = Map(dt.page_id_t, dt.pid_t)
    data = Map(dt.page_id_t, dt.uint64_t, dt.uint64_t)
    inv = Map(dt.page_id_t, dt.uint64_t)


class Files(Struct):
    entry = Map(dt.uint64_t, dt.uint64_t)
    data = Map(dt.uint64_t, dt.uint64_t, dt.uint64_t)


class MCertiKOSState(BaseStruct):
    procs = Procs()
    pages = Pages()
    files = Files()

    current = Map(dt.pid_t)

    alloc_assumptions = []

    def alloc_page(self):
        pg = util.FreshBitVec('alloc', dt.page_id_t)
        self.alloc_assumptions.append(z3.And(dt.is_page_valid(pg), self.pages[pg].free))
        return pg


def to_py(x):
    if z3.is_bv(x):
        if hasattr(x, 'as_long'):
            return x.as_long()
        else:
            return str(x)
    if z3.is_bool(x):
        if z3.is_true(x):
            return True
        if z3.is_false(x):
            return False
        return str(x)
    raise RuntimeError("type not supported")


def to_json_data(s, model):
    out = {}
    for i in range(512):
        v = model.eval(s(i))
        if v == 0:
            continue
        else:
            out[i] = v
    return out


def to_json_proc(s, model, i):
    return {
        'state': model.eval(s.procs[i].state),
        'nr_free_pages': model.eval(s.procs[i].nr_free_pages),
        'nr_children': model.eval(s.procs[i].nr_children),
        'pgtable': to_json_data(s.procs[i].pgtable, model),
        'fileid': model.eval(s.procs[i].fileid),
        'next': model.eval(s.procs[i].next),
        'prev': model.eval(s.procs[i].prev),
    }


def to_json_page(s, model, i):
    return {
        'free': model.eval(s.pages[i].free),
        'owner': model.eval(s.pages[i].owner),
        'data': to_json_data(s.pages[i].data, model),
        'inv': model.eval(s.pages[i].inv),
    }


def to_json_file(s, model, i):
    return {
        'entry': model.eval(s.files[i].entry),
        'data': {} # to_json_data(s.files[i].data, model),
    }


def to_json_procs(s, model):
    return { i: to_json_proc(s, model, i) for i in range(dt.NR_PROCS) }


def to_json_pages(s, model):
    return { i: to_json_page(s, model, i) for i in range(dt.NR_PAGES) }


def to_json_files(s, model):
    return { i: to_json_file(s, model, i) for i in range(dt.NR_ELF_FILES) }


def to_json(s, model):
    m = type('model', (), {'model': model, 'eval': lambda self, *args:
        to_py(self.model.eval(*args, model_completion=True))})()

    return {
        'procs': to_json_procs(s, m),
        'pages': to_json_pages(s, m),
        'files': to_json_files(s, m),
        'current': m.eval(s.current),

    }
