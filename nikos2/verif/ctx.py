import libirpy
import libirpy.cstdlib as cstdlib

import nikos2.impl as impl


def newctx():
    ctx = libirpy.newctx(prune_depth=1000)
    # If we don't need the values of any constants we don't have to
    # initialize them, slightly faster execution time.
    ctx.eval.declare_global_constant = ctx.eval.declare_global_variable
    libirpy.initctx(ctx, impl)

    ctx.globals['@pdb'] = cstdlib.pdb
    ctx.globals['@memcpy'] = cstdlib.memcpy
    ctx.globals['@memset64'] = cstdlib.memset64
    ctx.globals['@memset'] = cstdlib.memset
    ctx.globals['@panic'] = cstdlib.panic

    ctx.globals['@elf_get_entry'] = cstdlib.nop
    ctx.globals['@get_current_pt_regs'] = cstdlib.nop
    ctx.globals['@get_cpu_pt_regs'] = cstdlib.nop

    return ctx
