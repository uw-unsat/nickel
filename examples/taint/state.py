from libirpy.state import BaseStruct, Struct, Map
import datatypes as dt


class Procs(Struct):
    value = Map(dt.pid_t, dt.uint64_t)
    level = Map(dt.pid_t, dt.bool_t)


class SimpleState(BaseStruct):
    procs = Procs()
    current = Map(dt.pid_t)
