import libirpy
import libirpy.unittest
import nickel.unwindings as unwinding
from nickel.prototype import Prototype

import spec
import ni
import state


ops =  {
   'sys_spawn': [],
   # 'sys_broken_spawn': [],
}


class SimpleNI(unwinding.ProofBase):
    __abstract__ = True
    prototypes = ops
    doms = ni.domains()
    state = state.SimpleState

    def _domain(self, s, name, args):
        return ni.Domain(s.current)

    def obs_equivalence(self, *args, **kwargs):
        return ni.obs_equivalence(*args, **kwargs)

    def _test_handler(self, name, dom):
        self.dom = dom
        specfn = getattr(spec, name)
        args = self._get_args(name)
        dom = lambda s: self._domain(s, name, args)
        self._test(specfn=specfn, specargs=args, dom=dom, syscall_name=name, lemmas=[])

    def _get_args(self, name):
        return getattr(Prototype(self.prototypes), name)()


class OutputConsistency(unwinding.OutputConsistency, SimpleNI):
    pass


class LocalRespect(unwinding.LocalRespect, SimpleNI):
    pass


class WeakStepConsistency(unwinding.WeakStepConsistency, SimpleNI):
    pass


class DomainConsistency(unwinding.DomainConsistency, SimpleNI):
    pass


class DomainRespect(unwinding.DomainRespect, SimpleNI):
    pass


class EqvTest(SimpleNI, unwinding.EquivalenceProp):
    prototypes = {}


if __name__ == '__main__':
    libirpy.unittest.main()
