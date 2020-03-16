# -*- encoding: UTF-8
import unittest
import z3

import libirpy
import libirpy.unittest
import libirpy.solver as solver
import libirpy.util as util
import nickel.unwindings as ni

import datatypes as dt
import spec
import spec.label as l
import state
import ctx
from prototypes import proto


TestCase = libirpy.unittest.IrpyTestCase


def flatten(lst):
    out = []
    for i in lst:
        if isinstance(i, tuple):
            out.extend(i)
        else:
            out.append(i)
    return tuple(out)


def spec_args(args):
    spec_args = []
    for arg in args:
        if z3.is_expr(arg) and arg.sexpr().startswith('(concat'):
            spec_args.append(arg.children()[::-1])
        else:
            spec_args.append(arg)
    return spec_args


class NistarMeta(type):
    def __new__(cls, name, parents, dct):
        cls._add_syscalls(name, parents, dct)
        return super(NistarMeta, cls).__new__(cls, name, parents, dct)

    @classmethod
    def _add_syscalls(cls, name, parents, dct):
        for syscall in proto.keys():
            cls._add_syscall(dct, syscall)

    @classmethod
    def _add_syscall(cls, dct, syscall):
        if 'test_{}'.format(syscall) in dct:
            return
        dct['test_{}'.format(syscall)] = lambda self, syscall=syscall: \
            self._syscall_generic(syscall)


class Nistar(TestCase):
    __metaclass__ = NistarMeta

    def setUp(self):
        self.ctx = ctx.newctx()
        self.kernelstate = state.NistarState()

        self.solver = self.Solver()
        self.solver.set(AUTO_CONFIG=False)
        self._set_name()

        self._pre = spec.state_equiv(self.ctx, self.kernelstate)
        self.solver.add(self._pre)

        self.ctx.add_assumption(spec.impl_invariants(self.ctx))

    def tearDown(self):
        if isinstance(self.solver, solver.Solver):
            del self.solver

    def _test(self, name):
        args = getattr(proto, name)()

        inv = []
        sargs = spec_args(args)

        for arg in args:
            if hasattr(arg, 'packing_invariants'):
                inv.append(arg.packing_invariants())

        kret, ks = getattr(spec, name)(self.kernelstate, *sargs)
        iret = self.ctx.call("@{}".format(name), *flatten(args))
        if iret is None:
            iret = 0

        if self.ctx.assumptions:
            print "WARN: Adding {} assumptions".format(len(self.ctx.assumptions))
            for i in self.ctx.assumptions:
                print i
            self.solver.add(z3.And(*self.ctx.assumptions))

        if name != 'sched_next':
            # We are not idling.
            self.solver.add(self.kernelstate.current != self.kernelstate.idle)

        self.solver.add(z3.And(inv))

        if isinstance(kret, util.Cases):
            m = self._prove(z3.And(iret == kret.to_ite(),
                                   spec.state_equiv(self.ctx, ks)),
                            pre=z3.And(z3.BoolVal(True), self._pre),
                            return_model=self.INTERACTIVE)
        else:
            m = self._prove(z3.And((iret == 0) == kret,
                                   spec.state_equiv(self.ctx, ks)),
                            pre=z3.And(z3.BoolVal(True), self._pre),
                            return_model=self.INTERACTIVE)
        if m:
            print m
            ctx = self.ctx
            from ipdb import set_trace; set_trace()

    def _syscall_generic(self, name):
        self._test(name)


class NistarAssumptions(TestCase):
    __metaclass__ = NistarMeta

    def setUp(self):
        self.ctx = ctx.newctx()
        self.kernelstate = state.NistarState()

        self.solver = self.Solver()
        self.solver.set(AUTO_CONFIG=False)
        self._set_name()

        self._pre = spec.state_equiv(self.ctx, self.kernelstate)
        self.solver.add(self._pre)

        self.ctx.add_assumption(spec.impl_invariants(self.ctx))

    def tearDown(self):
        if isinstance(self.solver, solver.Solver):
            del self.solver

    def _test(self, name):
        inv = ['ok', 'current_thread_valid', 'freelist_ok',
                  'ufreelist_ok', 'label_unique_ok', 'tls_unique_ok']
        for i in inv:
            self.solver.add(getattr(spec.lemmas, i)(self.kernelstate))

        if name != 'sched_next':
            self.solver.add(self.kernelstate.current != self.kernelstate.idle)

        args = getattr(proto, name)()
        self.ctx.call("@{}".format(name), *flatten(args))

        conds = self.ctx.assumptions

        self._prove(z3.And(*conds))

    def _syscall_generic(self, name):
        self._test(name)


class NistarFlowTests(TestCase):
    def setUp(self):
        self.s1 = state.NistarState()
        self.s2 = state.NistarState()

        self.L = (util.FreshFunction('secrecy', dt.tag_t, dt.bool_t),
                  util.FreshFunction('integrity', dt.tag_t, dt.bool_t))

        self.solver = self.Solver()
        self.solver.set(AUTO_CONFIG=False)
        self.solver.set(MODEL=self.MODEL_HI)
        self._set_name()

    def tearDown(self):
        if isinstance(self.solver, solver.Solver):
            del self.solver

    def test_flow_w(self):
        T = (util.FreshFunction('secrecy', dt.tag_t, dt.bool_t),
             util.FreshFunction('integrity', dt.tag_t, dt.bool_t),
             util.FreshFunction('ownership', dt.tag_t, dt.bool_t))

        L = (util.FreshFunction('secrecy', dt.tag_t, dt.bool_t),
             util.FreshFunction('integrity', dt.tag_t, dt.bool_t))

        K = (util.FreshFunction('secrecy', dt.tag_t, dt.bool_t),
             util.FreshFunction('integrity', dt.tag_t, dt.bool_t))

        # T ⋢⁺ L /\ K ⊑ L => T ⋢⁺ K
        self._prove(z3.Implies(
                z3.And(z3.Not(l.can_write(T, L, T[2])),
                       l.flow(K, L)),
                z3.Not(l.can_write(T, K, T[2]))))

    def test_flow_r(self):
        T = (util.FreshFunction('secrecy', dt.tag_t, dt.bool_t),
             util.FreshFunction('integrity', dt.tag_t, dt.bool_t),
             util.FreshFunction('ownership', dt.tag_t, dt.bool_t))

        L = (util.FreshFunction('secrecy', dt.tag_t, dt.bool_t),
             util.FreshFunction('integrity', dt.tag_t, dt.bool_t))

        K = (util.FreshFunction('secrecy', dt.tag_t, dt.bool_t),
             util.FreshFunction('integrity', dt.tag_t, dt.bool_t))

        # L ⋢⁺ T /\ L ⊑ K => K ⋢⁺ T
        self._prove(z3.Implies(
                z3.And(z3.Not(l.can_read(T, L, T[2])),
                       l.flow(L, K)),
                z3.Not(l.can_read(T, K, T[2]))))

    def test_flow_w2(self):
        T = (util.FreshFunction('secrecy', dt.tag_t, dt.bool_t),
             util.FreshFunction('integrity', dt.tag_t, dt.bool_t),
             util.FreshFunction('ownership', dt.tag_t, dt.bool_t))

        L = (util.FreshFunction('secrecy', dt.tag_t, dt.bool_t),
             util.FreshFunction('integrity', dt.tag_t, dt.bool_t))

        tag = util.FreshBitVec('tag', dt.tag_t)

        # If a thread can not write to L is the same as saying
        # there exists a tag in L's integrity label but not in T's integrity label,
        # or there exists a tag in T's secrecy label but not in L's secrecy label.

        # T ⋢⁺ L <=> ∃ t. (Lintegrity(t) /\ ¬ Townership(t) /\ ¬ Tintegrity(t)) \/
        #                 (¬ Lsecrecy(t)  /\ ¬ Townership(t) /\ Tsecrecy(t))
        self._prove(
            z3.Not(l.can_write(T, L, T[2])) ==
            z3.Exists([tag],
                z3.Or(
                    z3.And(
                        L[1](tag),             # Lintegrity(t)
                        z3.Not(T[2](tag)),     # ¬ Townership(t)
                        z3.Not(T[1](tag))),    # ¬ Tintegrity(t)
                    z3.And(
                        z3.Not(L[0](tag)),     # ¬ Lsecrecy(t)
                        z3.Not(T[2](tag)),     # ¬ Townership(t)
                        T[0](tag)),            # Tsecrecy(t)
                    )))


class NistarInvariantTests(TestCase):
    def setUp(self):
        self.ctx = ctx.newctx()
        self.state = state.NistarState()

        self.solver = self.Solver()
        self.solver.set(AUTO_CONFIG=False)
        self.solver.set(MODEL=self.MODEL_HI)
        self._set_name()

    def test_impl_invariant(self):
        I = spec.impl_invariants(self.ctx)
        self._solve(I)

    def test_spec_invariants(self):
        self._solve(spec.spec_invariants(self.state.initial()))

    def test_equiv_inv(self):
        old = dt.NR_PAGES
        dt.NR_PAGES = 10
        self.state = self.state.initial()
        I = spec.impl_invariants(self.ctx)
        S = spec.spec_invariants(self.state)
        e = spec.state_equiv(self.ctx, self.state)
        self._solve(z3.And(I, S, e))
        dt.NR_PAGES = old


class NistarSpecLemmaMeta(NistarMeta):
    @classmethod
    def _add_syscall(cls, dct, syscall):
        for lemma in dct['lemmas']:
            if not 'test_{}_{}'.format(syscall, lemma) in dct:
                dct['test_{}_{}'.format(syscall, lemma)] = lambda self, syscall=syscall, lemma=lemma: self._test_lemma(syscall, lemma)


class NistarSpecLemma(TestCase):
    __metaclass__ = NistarSpecLemmaMeta

    def setUp(self):
        self.state = state.NistarState()
        self.solver = self.Solver()
        self.solver.set(AUTO_CONFIG=False)
        self.solver.set(MODEL=self.MODEL_HI)
        self._set_name()

    def test_sat(self):
        old = (dt.NR_PAGES, dt.NR_PAGES2M)
        dt.NR_PAGES, dt.NR_PAGES2M = 10, 2
        conj = []
        for i in self.lemmas:
            conj.append(getattr(spec.lemmas, i)(self.state))
        self._solve(z3.And(*conj))
        dt.NR_PAGES, dt.NR_PAGES2M = old

    def _test_lemma(self, syscall, lemma_name):
        args = spec_args(getattr(proto, syscall)())
        lemma = getattr(spec.lemmas, lemma_name)

        for i in self.lemmas:
            cond = getattr(spec.lemmas, i)(self.state)
            if i == lemma_name:
                pre = cond
            self.solver.add(cond)

        _, state = getattr(spec, syscall)(self.state, *args)

        for i in self.lemmas:
            if i == lemma_name:
                continue
            print "Assuming lemma", i
            cond = getattr(spec.lemmas, i)(self.state)
            self.solver.add(cond)

        post = lemma(state)

        self._prove(post, pre=pre)

    lemmas = [
        'ok',
        'current_thread_valid',
        'freelist_ok',
        'ufreelist_ok',
        'label_unique_ok',
        'tls_unique_ok',
        # Should be true, but its not used by anyone.
        # 'tags_unused_ok',
    ]


class NistarNI(TestCase):
    __metaclass__ = NistarMeta

    def setUp(self):
        self.s = state.NistarState()
        self.t = state.NistarState()

        # Domain
        self.L = dt.Domain(
                util.FreshFunction('secrecy', dt.tag_t, dt.bool_t),
                util.FreshFunction('integrity', dt.tag_t, dt.bool_t),
                util.FreshFunction('ownership', dt.tag_t, dt.bool_t))

        self.solver = self.Solver()
        self.solver.set(AUTO_CONFIG=False)
        self.solver.set(MODEL=self.MODEL_HI)
        self._set_name()

    def _domain(self, s, name, args, widle=False):
        secrecy = s.pages.label[s.pages[s.current].secrecy].label
        integrity = s.pages.label[s.pages[s.current].integrity].label
        ownership = s.pages.label[s.pages.ownership(s.current)].label

        if name == 'sys_alloc_tag':
            tag_lo = s.current
            tag_hi = s.pages[s.current].tag_counter
            tag = z3.Concat(tag_hi, tag_lo)
            ownership = lambda t, ownership=ownership: \
                    z3.If(t == tag, z3.BoolVal(True), ownership(t))
        elif name == 'sched_next':
            secrecy = l.empty()
            integrity = l.universal()
            ownership = l.empty()
        elif name == 'do_gate_enter':
            ownership = l.union(ownership, args[2].has)

        if widle and name != 'sched_next':
            secrecy = lambda tag, old=secrecy: util.If(s.current == s.idle, z3.BoolVal(True), old(tag))
            integrity = lambda tag, old=integrity: util.If(s.current == s.idle, z3.BoolVal(False), old(tag))
            ownership = lambda tag, old=ownership: util.If(s.current == s.idle, z3.BoolVal(False), old(tag))

        return dt.Domain(secrecy, integrity, ownership)

    def _syscall_generic(self, name):
        specfn = getattr(spec, name)
        args = self._get_args(name)

        dom = lambda s: self._domain(s, name, args)

        lemmas = spec.lemmas.spec_to_lemma(name)

        self._test(specfn=specfn, specargs=args, dom=dom, syscall_name=name, lemmas=lemmas)

    def _get_args(self, name):
        return spec_args(getattr(proto, name)())

    def _apply_lemmas(self, state, lemmas):
        for lemma in lemmas:
            print "Applying lemma {}".format(lemma.__name__)
            self.solver.add(lemma(state))


class OutputConsistency(NistarNI):
    def _test(self, specfn=None, specargs=None, syscall_name=None, dom=None, lemmas=None):
        # s and t are `safe` states.
        self._apply_lemmas(self.s, lemmas)
        self._apply_lemmas(self.t, lemmas)

        # s ~dom(a, s) t
        self.solver.add(
                spec.ni.obs_equivalence(self.s, self.t, dom(self.s)))

        if syscall_name != 'sched_next':
            self.solver.add(self.s.current != self.s.idle)
            self.solver.add(self.t.current != self.t.idle)

        # output(s, a)
        sout, _ = specfn(self.s, *specargs)
        tout, _ = specfn(self.t, *specargs)

        if isinstance(sout, util.Cases) or isinstance(tout, util.Cases):
            sout = sout.to_ite()
            tout = tout.to_ite()

        m = self._prove(sout == tout, return_model=self.INTERACTIVE)
        if m:
            print m
            from ipdb import set_trace; set_trace()


class LocalRespect(NistarNI):
    def _test(self, specfn=None, specargs=None, syscall_name=None, dom=None, lemmas=None):
        if spec.lemmas.label_unique_ok not in lemmas:
            lemmas.append(spec.lemmas.label_unique_ok)

        # dom(a, s) ⋢ L
        self.solver.add(z3.Not(
            l.interference(dom(self.s), self.L)))

        if syscall_name != 'sched_next':
            self.solver.add(self.s.current != self.s.idle)

        # s is a `safe` state.
        self._apply_lemmas(self.s, lemmas)

        # step(s, a)
        _, s1 = specfn(self.s, *specargs)

        # Show that s ~L step(s, a)
        m = self._prove(spec.ni.obs_equivalence(self.s, s1, self.L), return_model=self.INTERACTIVE)
        if m:
            print m
            from ipdb import set_trace; set_trace()


class StepConsistency(NistarNI):
    def _test_current_equal(self, name):
        # Show that observational equivalence implies that
        # s.current == t.current for all operations (except 'sched_next')

        args = self._get_args(name)

        dom = lambda s: self._domain(s, name, args, widle=True)

        self._apply_lemmas(self.s, [spec.lemmas.ok, spec.lemmas.current_thread_valid])
        self._apply_lemmas(self.t, [spec.lemmas.ok, spec.lemmas.current_thread_valid])

        # s ~L t
        self.solver.add(
                spec.ni.obs_equivalence(self.s, self.t, self.L))

        # s ~dom(a, s) t
        self.solver.add(
                spec.ni.obs_equivalence(self.s, self.t, dom(self.s)))

        self._prove(self.s.current == self.t.current)

    def test_current_equal_normal(self):
        # Any operation that doesn't have a "special" domain.
        self._test_current_equal('sys_container_get_root')

    def test_current_equal_sys_alloc_tag(self):
        self._test_current_equal('sys_alloc_tag')

    def test_current_equal_do_gate_enter(self):
        self._test_current_equal('do_gate_enter')

    def _test(self, specfn=None, specargs=None, syscall_name=None, dom=None, lemmas=None):
        # s and t are `safe` states.
        self._apply_lemmas(self.s, lemmas)
        self._apply_lemmas(self.t, lemmas)

        # s ~L t
        self.solver.add(
                spec.ni.obs_equivalence(self.s, self.t, self.L))

        # s ~dom(a, s) t
        self.solver.add(
                spec.ni.obs_equivalence(self.s, self.t, dom(self.s)))

        # Only operation enabled for idle thread is sched_next
        if syscall_name != 'sched_next':
            self.solver.add(self.s.current != self.s.idle)
            self.solver.add(self.t.current != self.t.idle)

        # step(s, a)
        _, s1 = specfn(self.s, *specargs)
        _, t1 = specfn(self.t, *specargs)

        # step(s, a) and step(t, a) are safe. Speeds up these two proofs significantly.
        if syscall_name in ['sys_container_move_uquota']:
            self._apply_lemmas(s1, lemmas)
            self._apply_lemmas(t1, lemmas)

        # show that s ~L t
        m = self._prove(spec.ni.obs_equivalence(s1, t1, self.L), return_model=self.INTERACTIVE)
        if m:
            print m
            from ipdb import set_trace; set_trace()


class DomainConsistency(NistarNI):
    def _test(self, specfn=None, specargs=None, syscall_name=None, dom=None, lemmas=None):
        # s and t are `safe` states.
        self._apply_lemmas(self.s, lemmas)
        self._apply_lemmas(self.t, lemmas)

        self.solver.add(self.s.current != self.s.idle)
        self.solver.add(self.t.current != self.t.idle)

        # s ~dom(a, s) t
        self.solver.add(
                spec.ni.obs_equivalence(self.s, self.t, dom(self.s)))

        # show that dom(a, s) = dom(a, t)
        m = self._prove(l.equal(dom(self.s), dom(self.t)))
        if m:
            print m
            from ipdb import set_trace; set_trace()


class EqvTest(ni.EquivalenceProp):
    doms = [('label', dt.Domain(
            util.FreshFunction('secrecy', dt.tag_t, dt.bool_t),
            util.FreshFunction('integrity', dt.tag_t, dt.bool_t),
            util.FreshFunction('ownership', dt.tag_t, dt.bool_t)))]
    state = state.NistarState
    lemmas = [spec.lemmas.ok, spec.lemmas.freelist_ok]

    def obs_equivalence(self, s, t, L):
        return spec.ni.obs_equivalence(s, t, L)


if __name__ == "__main__":
    libirpy.unittest.main()
