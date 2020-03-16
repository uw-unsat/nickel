import z3

import libirpy
import libirpy.unittest
import libirpy.util as util
import nickel.unwindings as ni

import datatypes as dt
from prototypes import proto, prototypes
import spec
import state


TestCase = libirpy.unittest.IrpyTestCase


class SKNI(ni.ProofBase):
    def setUp(self):
        self.s = state.SKState()
        self.t = state.SKState()
        self.config = state.SKConfiguration()
        self.dom = spec.ni.Partition(util.FreshBitVec('dom', dt.partition_t))
        super(SKNI, self).setUp()

    def _domain(self, s, name, args):
        if name == 'sys_schedule':
            return spec.ni.Scheduler()
        if name == 'sys_transfer_sampling_message':
            return spec.ni.Transmitter(self.config)
        if name == 'sys_transfer_queueing_message':
            return spec.ni.Transmitter(self.config)

        # Every other event runs as the current partition
        return spec.ni.Partition(s.current_partition)

    def obs_equivalence(self, *args, **kwargs):
        return spec.ni.obs_equivalence(self.config, *args, **kwargs)

    def _test_handler(self, name):
        specfn = getattr(spec, name)
        args = self._get_args(name)
        dom = lambda s: self._domain(s, name, args)
        lemmas = spec.lemmas.spec_to_lemma(name)
        nspecfn = lambda *args, **kwargs: specfn(self.config, *args, **kwargs)
        self._test(specfn=nspecfn, specargs=args, dom=dom, syscall_name=name, lemmas=lemmas)

    def _get_args(self, name):
        return getattr(proto, name)()

    def _apply_lemmas(self, state, lemmas):
        for lemma in lemmas:
            print("Applying lemma {}".format(lemma.__name__))
            self.solver.add(lemma(self.config, state))


class SKSpecLemma(ni.ProofBase):
    prototypes = prototypes
    props = spec.lemmas.spec_to_lemma('all')

    def setUp(self):
        self.state = state.SKState()
        self.config = state.SKConfiguration()
        super(SKSpecLemma, self).setUp()

    def _test_handler(self, syscall, lemma):
        args = getattr(proto, syscall)()

        pre = [l(self.config, self.state) for l in self.props]
        self.solver.add(pre)

        _, state = getattr(spec, syscall)(self.config, self.state, *args)

        post = lemma(self.config, state)

        m = self._prove(post, pre=z3.And(*pre), return_model=self.INTERACTIVE)

        if m:
            print(m)
            from ipdb import set_trace; set_trace()


class OutputConsistency(ni.OutputConsistency, SKNI):
    prototypes = prototypes


class LocalRespect(ni.LocalRespect, SKNI):
    prototypes = prototypes


class WeakStepConsistency(ni.WeakStepConsistency, SKNI):
    prototypes = prototypes


class DomainConsistency(ni.DomainConsistency, SKNI):
    prototypes = prototypes


class DomainRespect(ni.DomainRespect, SKNI):
    prototypes = prototypes


class DomainTest(TestCase):
    def _new_config(self):
            return spec.ni.PolicyConfiguration(
                flows_to=util.FreshFunction('flows_to', dt.partition_t, dt.bool_t),
                flows_from=util.FreshFunction('flows_from', dt.partition_t, dt.bool_t))

    def test_interferes_scheduler(self):
        s = spec.ni.Scheduler()
        for i in spec.ni.domains(self._new_config()):
            assert s.interferes(i)

    def test_no_interferes_scheduler(self):
        s = spec.ni.Scheduler()
        for i in spec.ni.domains(self._new_config()):
            if isinstance(i, spec.ni.Scheduler):
                continue
            assert not i.interferes(s)

    def test_no_interferes_partition(self):
        u = spec.ni.Partition(util.FreshBitVec('id', dt.partition_t))
        v = spec.ni.Partition(util.FreshBitVec('id', dt.partition_t))
        assert not u.interferes(v)

    def test_partition_interferes_transmitter(self):
        config = self._new_config()
        u = spec.ni.Partition(util.FreshBitVec('id', dt.partition_t))
        v = spec.ni.Transmitter(config)
        self._prove(u.interferes(v) == config.flows_to(u.id))

    def test_transmitter_interferes_partition(self):
        config = self._new_config()
        u = spec.ni.Transmitter(config)
        v = spec.ni.Partition(util.FreshBitVec('id', dt.partition_t))
        self._prove(u.interferes(v) == config.flows_from(v.id))


class EqvTest(ni.ProofBase):
    def setUp(self):
        self.x = state.SKState()
        self.y = state.SKState()
        self.z = state.SKState()
        self.config = state.SKConfiguration()
        self.dom = spec.ni.Partition(util.FreshBitVec('dom', dt.partition_t))
        super(EqvTest, self).setUp()

    def obs_equivalence(self, *args, **kwargs):
        return spec.ni.obs_equivalence(self.config, *args, **kwargs)

    def test_eqv_refl(self):
        self._prove(self.obs_equivalence(self.x, self.x, self.dom))

    def test_eqv_sym(self):
        self._prove(
                util.Implies(
                    self.obs_equivalence(self.x, self.y, self.dom),
                    self.obs_equivalence(self.y, self.x, self.dom)))

    def test_eqv_trans(self):
        self._prove(
                util.Implies(
                    self.obs_equivalence(self.x, self.y, self.dom),
                    self.obs_equivalence(self.y, self.z, self.dom),
                    self.obs_equivalence(self.x, self.z, self.dom)))



if __name__ == "__main__":
    libirpy.unittest.main()
