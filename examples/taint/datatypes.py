import libirpy.typedefs as td
import z3


bool_t       = td.bool_t
pid_t        = td.uint64_t
uint64_t     = td.uint64_t

UNTAINTED    = z3.BoolVal(False)
TAINTED      = z3.BoolVal(True)
