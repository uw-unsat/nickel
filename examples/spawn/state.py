from libirpy.state import BaseStruct, Struct, Map
import datatypes as dt


class Procs(Struct):
    nr_children = Map(dt.pid_t, dt.uint64_t)


class SimpleState(BaseStruct):
    procs = Procs()
    current = Map(dt.pid_t)
    nr_procs = Map(dt.uint64_t)
