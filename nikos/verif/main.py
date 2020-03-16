import z3

import libirpy
import libirpy.unittest
import libirpy.util as util
import nickel.unwindings as ni
from nickel.prototype import Prototype

import json
import datatypes as dt
import prototypes as p
import spec
import state
import ctx


TestCase = libirpy.unittest.IrpyTestCase


def json_join(j1, j2, margin=16):
    just = max(map(len, j1.splitlines()))

    out = []
    for a, b in zip(j1.splitlines(), j2.splitlines()):
        out.append(a.ljust(just + margin) + b)
    return '\n'.join(out)


def spec_args(args):
    spec_args = []
    for arg in args:
        if z3.is_expr(arg) and arg.sexpr().startswith('(concat'):
            spec_args.append(arg.children()[::-1])
        else:
            spec_args.append(arg)
    return spec_args


def flatten(lst):
    out = []
    for i in lst:
        if isinstance(i, tuple):
            out.extend(i)
        else:
            out.append(i)
    return tuple(out)


class MCertiKOSRefinement(ni.ProofBase):
    prototypes = p.syscalls

    def setUp(self):
        super(MCertiKOSRefinement, self).setUp()
        self.ctx = ctx.newctx()
        self.kernelstate = state.MCertiKOSState()
        self._pre = spec.state_equiv(self.ctx, self.kernelstate)
        self.solver.add(self._pre)
        self.ctx.add_assumption(spec.impl_invariants(self.ctx))

    def _test_handler(self, name):
        args = getattr(Prototype(self.prototypes), name)()
        sargs = spec_args(args)

        kret, ks = getattr(spec, name)(self.kernelstate, *sargs)
        iret = self.ctx.call("@{}".format(name), *flatten(args))

        m = self._prove(z3.And(kret.to_ite() == iret,
                               spec.state_equiv(self.ctx, ks)),
                        pre=z3.And(z3.BoolVal(True), self._pre),
                        return_model=self.INTERACTIVE)

        if m:
            print m
            ctx = self.ctx
            from ipdb import set_trace; set_trace()

    def _syscall_generic(self, name):
        self._test(name)


class MCertiKOSNI(ni.ProofBase):
    def setUp(self):
        super(MCertiKOSNI, self).setUp()
        self.s = state.MCertiKOSState()
        self.t = state.MCertiKOSState()
        self.dom = spec.ni.ProcDomain(util.FreshBitVec('dom_pid', dt.pid_t))

    def _domain(self, s, name, args):
        if name == 'sys_yield':
            return spec.ni.ProcDomain(util.i64(0))
        else:
            return spec.ni.ProcDomain(s.current)

    def obs_equivalence(self, *args, **kwargs):
        return spec.ni.obs_equivalence(*args, **kwargs)

    def _test_handler(self, name):
        specfn = getattr(spec, name)
        args = self._get_args(name)
        dom = lambda s: self._domain(s, name, args)
        lemmas = spec.lemmas.spec_to_lemma(name)
        self._test(specfn=specfn, specargs=args, dom=dom, syscall_name=name, lemmas=lemmas)

    def _get_args(self, name):
        return spec_args(getattr(Prototype(self.prototypes), name)())

    def _apply_lemmas(self, state, lemmas):
        for lemma in lemmas:
            print "Applying lemma {}".format(lemma.__name__)
            self.solver.add(lemma(state))

    def assumptions(self, s, s1):
        self.solver.add(z3.And(*s1.alloc_assumptions))

    def ce(self, m, s, s1, specargs, locals):
        print(m)
        print(json_join(json.dumps(state.to_json(self.s, m), indent=2),
                        json.dumps(state.to_json(s1, m), indent=2)))
        from ipdb import set_trace; set_trace()


class OutputConsistency(ni.OutputConsistency, MCertiKOSNI):
    prototypes = p.all_ops


class LocalRespect(ni.LocalRespect, MCertiKOSNI):
    prototypes = p.all_ops


class WeakStepConsistency(ni.WeakStepConsistency, MCertiKOSNI):
    prototypes = p.all_ops


class DomainConsistency(ni.DomainConsistency, MCertiKOSNI):
    prototypes = p.all_ops


class DomainRespect(ni.DomainRespect, MCertiKOSNI):
    prototypes = p.all_ops


class MCertiKOSSpecLemma(ni.ProofBase):
    prototypes = p.all_ops
    props = spec.lemmas.spec_to_lemma('all')

    def setUp(self):
        self.state = state.MCertiKOSState()
        super(MCertiKOSSpecLemma, self).setUp()

    def _test_lemma_sat(self, lemma):
        pre = lemma(self.state)
        self._solve(pre)

    def _test_lemmas_sat(self):
        pre = [l(self.state) for l in self.props]
        self._solve(pre)

    def _test_handler(self, syscall, lemma):
        args = spec_args(getattr(Prototype(self.prototypes), syscall)())
        pre = z3.And(*[l(self.state) for l in self.props])
        self.solver.add(pre)

        _, state = getattr(spec, syscall)(self.state, *args)

        self.solver.add(z3.And(*self.state.alloc_assumptions))
        post = lemma(state)
        self._prove(post, pre=pre)


if __name__ == "__main__":
    libirpy.unittest.main()
