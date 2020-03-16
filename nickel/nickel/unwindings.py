import z3
import libirpy.unittest
import libirpy.util as util

from six import with_metaclass


def name(p):
    if callable(p):
        return p.__name__
    return str(p)


class UnwindingMeta(type):
    def __new__(cls, name, parents, dct):
        if not dct.get('__abstract__', False):
            merge = ['prototypes', 'props', 'doms']

            for parent in parents:
                for m in merge:
                    if m not in dct and hasattr(parent, m):
                        dct.setdefault(m, getattr(parent, m))

            cls._pre_process(name, parents, dct)
            cls._add_event_handlers(name, parents, dct)
        return super(UnwindingMeta, cls).__new__(cls, name, parents, dct)

    @classmethod
    def _pre_process(cls, name, parents, dct):
        pass

    @classmethod
    def _add_event_handlers(cls, name, parents, dct):
        if not 'prototypes' in dct:
            RuntimeError("Class {} has no prototypes".format(name))
        if 'prototypes' in dct:
            for handler in dct['prototypes'].keys():
                cls._add_event_handler(dct, handler)

    @classmethod
    def _add_event_handler(cls, dct, handler):
        _basename = 'test_{}'.format(name(handler))

        doms = [('', None)]
        if 'doms' in dct and dct['doms']:
            doms = dct['doms']

        many = len(doms) > 1

        for dom in doms:
            if isinstance(dom, tuple):
                dname, dom = dom
            else:
                dname = dom.__class__.__name__.lower()

            if not many:
                dname = None

            if dname:
                basename = "{}_{}".format(_basename, dname)
            else:
                basename = _basename

            if 'props' in dct:
                for prop in dct['props']:
                    hname = '{}_{}'.format(basename, name(prop))
                    if hname in dct:
                        return

                    if dom:
                        fun = lambda self, handler=handler, prop=prop, dom=dom: \
                                self._test_handler(handler, prop, dom=dom)
                    else:
                        fun = lambda self, handler=handler, prop=prop: \
                                self._test_handler(handler, prop)

                    dct[hname] = fun
            else:
                if basename in dct:
                    return
                if dom:
                    fun = lambda self, handler=handler, dom=dom: \
                            self._test_handler(handler, dom=dom)
                else:
                    fun = lambda self, handler=handler: self._test_handler(handler)

                dct[basename] = fun


class ProofBase(with_metaclass(UnwindingMeta, libirpy.unittest.IrpyTestCase)):
    def setUp(self):
        self.create_solver()
        super(ProofBase, self).setUp()

    def create_solver(self):
        self.solver = self.Solver()
        self.solver.set(AUTO_CONFIG=False)
        self.solver.set(MODEL=self.MODEL_HI)
        self._set_name()

    def _apply_lemmas(self, state, lemmas):
        for lemma in lemmas:
            self.solver.add(lemma(state))


class OutputConsistency(ProofBase):
    def setUp(self):
        if hasattr(self, 'state'):
            self.s = self.state()
            self.t = self.state()
        super(OutputConsistency, self).setUp()

    def _test(self, specfn=None, specargs=None, syscall_name=None, dom=None, lemmas=None):
        # s and t are `safe` states.
        self._apply_lemmas(self.s, lemmas)
        self._apply_lemmas(self.t, lemmas)

        # s ~dom(a, s) t
        self.solver.add(
                self.obs_equivalence(self.s, self.t, dom(self.s)))

        # output(s, a)
        sout, _ = specfn(self.s, *specargs)
        tout, _ = specfn(self.t, *specargs)

        if isinstance(sout, tuple):
            scond = sout[0]
            sout = sout[1]
        else:
            scond = sout

        if isinstance(tout, tuple):
            tcond = tout[0]
            tout = tout[1]
        else:
            tcond = tout

        # TODO: sout and tout

        m = self._prove(scond.to_ite() == tcond.to_ite(), return_model=self.INTERACTIVE)
        if m:
            print(m)
            from ipdb import set_trace; set_trace()


class LocalRespect(ProofBase):
    def setUp(self):
        if hasattr(self, 'state'):
            self.s = self.state()
        super(LocalRespect, self).setUp()

    def _test(self, specfn=None, specargs=None, syscall_name=None, dom=None, lemmas=None):
        # dom(a, s) ~/> L
        self.solver.add(z3.Not(dom(self.s).interferes(self.dom)))

        if hasattr(self.dom, 'valid'):
            self.solver.add(self.dom.valid())

        # s is a `safe` state.
        self._apply_lemmas(self.s, lemmas)

        # step(s, a)
        _, s1 = specfn(self.s, *specargs)

        if hasattr(self, 'assumptions'):
            self.assumptions(self.s, s1)

        # Show that s ~L step(s, a)
        m = self._prove(self.obs_equivalence(self.s, s1, self.dom), return_model=self.INTERACTIVE)
        if m:
            if hasattr(self, 'ce'):
                self.ce(m, self.s, s1, specargs, locals())
            else:
                print(m)
                from ipdb import set_trace; set_trace()


class WeakStepConsistency(ProofBase):
    def setUp(self):
        if hasattr(self, 'state'):
            self.s = self.state()
            self.t = self.state()
        super(WeakStepConsistency, self).setUp()

    def _test(self, specfn=None, specargs=None, syscall_name=None, dom=None, lemmas=None):
        # s and t are `safe` states.
        self._apply_lemmas(self.s, lemmas)
        self._apply_lemmas(self.t, lemmas)

        # s ~L t
        self.solver.add(
                self.obs_equivalence(self.s, self.t, self.dom))

        # s ~dom(a, s) t
        self.solver.add(
                self.obs_equivalence(self.s, self.t, dom(self.s)))

        # step(s, a)
        _, s1 = specfn(self.s, *specargs)
        _, t1 = specfn(self.t, *specargs)

        if hasattr(self, 'assumptions'):
            self.assumptions(self.s, s1)
            self.assumptions(self.t, t1)

        # show that s ~L t
        m = self._prove(self.obs_equivalence(s1, t1, self.dom), return_model=self.INTERACTIVE)
        if m:
            if hasattr(self, 'ce'):
                self.ce(m, self.s, s1, specargs, locals())
            else:
                print(m)
                from ipdb import set_trace; set_trace()


class DomainConsistency(ProofBase):
    def setUp(self):
        if hasattr(self, 'state'):
            self.s = self.state()
            self.t = self.state()
        super(DomainConsistency, self).setUp()

    def _test(self, specfn=None, specargs=None, syscall_name=None, dom=None, lemmas=None):
        # s and t are `safe` states.
        self._apply_lemmas(self.s, lemmas)
        self._apply_lemmas(self.t, lemmas)

        # s ~dom(a, s) t => dom(a, s) = dom(a, t)
        self.solver.add(
                self.obs_equivalence(self.s, self.t, dom(self.s)))

        self._prove(dom(self.s) == dom(self.t))


class DomainRespect(ProofBase):
    def setUp(self):
        if hasattr(self, 'state'):
            self.s = self.state()
            self.t = self.state()
        super(DomainRespect, self).setUp()

    def _test(self, specfn=None, specargs=None, syscall_name=None, dom=None, lemmas=None):
        # s and t are `safe` states.
        self._apply_lemmas(self.s, lemmas)
        self._apply_lemmas(self.t, lemmas)

        if hasattr(self.dom, 'valid'):
            self.solver.add(self.dom.valid())

        # s ~u t => (dom(a, s) ~> u <=> dom(a, t) ~> u)
        self.solver.add(
                self.obs_equivalence(self.s, self.t, self.dom))

        self.solver.add(dom(self.s).interferes(self.dom))
        self._prove(dom(self.t).interferes(self.dom))


class DomainValid(ProofBase):
    def _test(self, specfn=None, specargs=None, syscall_name=None, dom=None, lemmas=None):
        self._apply_lemmas(self.s, lemmas)
        self._prove(dom(self.s).valid())


class EquivalenceProp(ProofBase):
    def setUp(self):
        if hasattr(self, 'state'):
            self.x = self.state()
            self.y = self.state()
            self.z = self.state()
        super(EquivalenceProp, self).setUp()

    def _get_dom(self, dom):
        if isinstance(dom, tuple):
            return dom[1]
        return dom

    def test_eqv_refl(self):
        self._apply_lemmas(self.x, getattr(self, 'lemmas', []))
        for dom in self.doms:
            self.dom = self._get_dom(dom)
            self._prove(self.obs_equivalence(self.x, self.x, self.dom))

    def test_eqv_sym(self):
        self._apply_lemmas(self.x, getattr(self, 'lemmas', []))
        self._apply_lemmas(self.y, getattr(self, 'lemmas', []))
        for dom in self.doms:
            self.dom = self._get_dom(dom)
            self._prove(
                    util.Implies(
                        self.obs_equivalence(self.x, self.y, self.dom),
                        self.obs_equivalence(self.y, self.x, self.dom)))

    def test_eqv_trans(self):
        self._apply_lemmas(self.x, getattr(self, 'lemmas', []))
        self._apply_lemmas(self.y, getattr(self, 'lemmas', []))
        self._apply_lemmas(self.z, getattr(self, 'lemmas', []))
        for dom in self.doms:
            self.dom = self._get_dom(dom)
            self._prove(
                    util.Implies(
                        self.obs_equivalence(self.x, self.y, self.dom),
                        self.obs_equivalence(self.y, self.z, self.dom),
                        self.obs_equivalence(self.x, self.z, self.dom)))
