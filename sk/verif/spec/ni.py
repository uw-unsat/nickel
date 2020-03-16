import z3
import libirpy.util as util
import datatypes as dt
from collections import namedtuple


PolicyConfiguration = namedtuple('PolicyConfiguration', ['flows_to', 'flows_from'])


def domains(config):
    return [
        Transmitter(config=config),
        Scheduler(),
        Partition(util.FreshBitVec('partition_id', dt.partition_t))
    ]


class Domain(object):
    def interferes(self, other):
        raise NotImplementedError()


class Transmitter(Domain):
    def __init__(self, config=None):
        self.flows_to = config.flows_to
        self.flows_from = config.flows_from

    def interferes(self, other):
        """Transmitter can only interfere with partitions, according to a
        configuration"""
        if not isinstance(other, Partition):
            return False
        return self.flows_from(other.id)


class Scheduler(Domain):
    def interferes(self, other):
        """Scheduler can interfere with any domain"""
        return True


class Partition(Domain):
    def __init__(self, id):
        self.id = id

    def __eq__(self, other):
        if hasattr(other, 'id'):
            return self.id == other.id
        else:
            return False

    def interferes(self, other):
        """partitions can only interfere with transmitter, according to
        transmitter configuration"""
        if not isinstance(other, Transmitter):
            return self == other

        return other.flows_to(self.id)


def partition_eqv(conj, sc, s1, s2, dom):
    conj.append(s1.partition[dom.id].num_ports ==
                s2.partition[dom.id].num_ports)



def port_eqv(conj, sc, s1, s2, port):
    if not conj:
        conj = []

    conj.append(s1.port[port].allocated == s2.port[port].allocated)
    conj.append(s1.port[port].partition == s2.port[port].partition)
    conj.append(s1.port[port].port_type == s2.port[port].port_type)
    conj.append(s1.port[port].port_direction == s2.port[port].port_direction)
    conj.append(s1.port[port].port_name == s2.port[port].port_name)
    conj.append(s1.port[port].max_message_size == s2.port[port].max_message_size)

    # Sampling ports
    conj.append(util.Implies(
        s1.is_port_sampling(port),
        s1.port[port].sampling_message == s2.port[port].sampling_message))

    # Queueing ports
    idx = util.FreshConst("idx", z3.IntSort())
    conj.append(util.Implies(
        z3.Or(
            s1.is_port_queueing(port),
            s2.is_port_queueing(port),
        ),
        z3.And(
            s1.port[port].queueing_max_nb_message ==
            s2.port[port].queueing_max_nb_message,

            # Write / read idx are the same
            s1.port.queue_q[port].write_idx == s2.port.queue_q[port].write_idx,
            s1.port.queue_q[port].read_idx == s2.port.queue_q[port].read_idx,

            # Every written value is the same
            z3.ForAll([idx], util.Implies(
                0 <= idx,
                idx < s1.port.queue_q[port].write_idx,
                s1.port.queue_q[port].q(idx) == s2.port.queue_q[port].q(idx))))))

    return z3.And(*conj)


def ports_eqv(conj, sc, s1, s2, dom):
    port = util.FreshBitVec('port', dt.port_id_t)

    portname = util.FreshConst('portname', dt.port_name_t)
    conj.append(z3.ForAll([portname], util.Implies(
        sc.port_config[portname].partition == dom.id,
        z3.And(
            s1.port.is_port_allocated(portname) == s2.port.is_port_allocated(portname),
            s1.port[portname].port_id == s2.port[portname].port_id,
            port_eqv(None, sc, s1, s2, s1.port[portname].port_id)
    ))))

    conj.append(z3.ForAll([port],
        util.Implies(
            z3.Or(s1.port[port].partition == dom.id,
                  s2.port[port].partition == dom.id),
            port_eqv(None, sc, s1, s2, port))))


def obs_equivalence_partition(sc, s1, s2, dom):
    conj = []

    conj.append(s1.current_partition == s2.current_partition)
    conj.append(s1.current_process == s2.current_process)
    partition_eqv(conj, sc, s1, s2, dom)
    ports_eqv(conj, sc, s1, s2, dom)

    return z3.And(*conj)


def trans_port_eqv(conj, sc, s1, s2):
    port = util.FreshBitVec('port', dt.port_id_t)
    idx = util.FreshConst('idx', dt.IntSort())

    conj.append(z3.ForAll([port],
        util.Implies(
            z3.Or(s1.port[port].allocated,
                  s2.port[port].allocated),
            z3.Or(
                s1.port[port].port_direction == dt.PORT_DIRECTION_SOURCE,
                s2.port[port].port_direction == dt.PORT_DIRECTION_SOURCE),

            z3.And(
                s1.port[port].allocated == s2.port[port].allocated,
                s1.port[port].port_direction == s2.port[port].port_direction,
                s1.port[port].max_message_size == s2.port[port].max_message_size,
                s1.port[port].port_type == s2.port[port].port_type,

                util.Implies(s1.port[port].port_type == dt.PORT_TYPE_QUEUEING,
                    s1.port[port].queue_q.read_idx == s2.port[port].queue_q.read_idx,
                    s1.port[port].queue_q.write_idx == s2.port[port].queue_q.write_idx,
                    z3.ForAll([idx],
                        util.Implies(idx < s1.port[port].queue_q.write_idx,
                            s1.port[port].qeueu_q.q(idx) == s2.port[port].queue_q.q(idx)))

                ),
                util.Implies(s1.port[port].port_type == dt.PORT_TYPE_SAMPLING,
                    s1.port[port].sampling_message == s2.port[port].sampling_message),
                ),
    )))


def obs_equivalence_transmitter(sc, s1, s2, dom):
    conj = []

    conj.append(s1.current_partition == s2.current_partition)
    conj.append(s1.current_process == s2.current_process)

    # Message buffer of every incoming port are equivalent
    trans_port_eqv(conj, sc, s1, s2)


def obs_equivalence(sc, s1, s2, dom):
    if isinstance(dom, Partition):
        return obs_equivalence_partition(sc, s1, s2, dom)
    elif isinstance(dom, Transmitter):
        return obs_equivalence_transmitter(sc, s1, s2, dom)
    else:
        assert False, "Obs not implemented for domain {}".format(dom)
