import z3

import datatypes as dt
import libirpy.util as util


def current_partition_valid(sc, state):
    return z3.And(
            dt.is_partition_valid(state.current_partition),
            z3.UGT(state.current_partition, 0))


def port_type_valid(sc, state):
    port = util.FreshBitVec('port_l', dt.port_id_t)
    return z3.ForAll([port], util.In(
        state.port[port].port_type,
        [dt.PORT_TYPE_SAMPLING,
         dt.PORT_TYPE_QUEUEING]))


def allocated_ports_consistent(sc, state):
    conj = []

    partition = util.FreshBitVec('partition_l', dt.partition_t)
    portidx = util.FreshBitVec('portidx_l', dt.uint32_t)
    portname = util.FreshConst('portname_l', dt.port_name_t)
    port = util.FreshBitVec('port_l', dt.port_id_t)

    conj.append(z3.Not(state.port[0].allocated))

    # Partition owns each of its ports
    conj.append(z3.ForAll([portname], util.Implies(
        state.port.is_port_allocated(portname),
        z3.And(
            state.port[state.port[portname].port_id].allocated,
            state.port[state.port[portname].port_id].partition == sc.port_config[portname].partition,
            dt.port_id_partition(state.port[portname].port_id) == sc.port_config[portname].partition))))

    # Partition owns each of its ports
    conj.append(z3.ForAll([partition, portidx], util.Implies(
        dt.is_partition_valid(partition),
        state.port[z3.Concat(partition, portidx)].partition == partition)))

    # Every portidx below "num_ports" has been allocated
    conj.append(z3.ForAll([partition, portidx],
            util.Implies(
                dt.is_partition_valid(partition),
                z3.ULT(portidx, state.partition[partition].num_ports),
                state.port[z3.Concat(partition, portidx)].allocated)))

    # No portidx above "num_ports" has been allocated
    conj.append(z3.ForAll([partition, portidx],
            util.Implies(
                dt.is_partition_valid(partition),
                z3.UGE(portidx, state.partition[partition].num_ports),
                z3.Not(state.port[z3.Concat(partition, portidx)].allocated))))

    # port name <-> port id bijection
    conj.append(
            z3.ForAll([port],
                util.Implies(
                    state.port[port].allocated,
                    state.port[state.port[port].port_name].port_id == port)))

    conj.append(
            z3.ForAll([portname],
                util.Implies(
                    state.port[state.port[portname].port_id].allocated,
                    z3.And(
                        state.port[state.port[portname].port_id].port_name == portname
                    ))))

    # Portid 0 is always Unallocated.
    # Every unallocated port name points to 0
    conj.append(
            z3.ForAll([portname],
                util.Implies(
                    z3.Not(state.port[state.port[portname].port_id].allocated),
                    state.port[portname].port_id == 0)))

    return z3.And(*conj)


def queue_consistent(sc, state):
    port = util.FreshBitVec('port_l', dt.port_id_t)

    return z3.ForAll([port],
        util.Implies(
            state.port[port].allocated,
            state.is_port_queueing(port),
            # state.port.queue_q.len(port) >= 0,
            state.port.queue_q[port].read_idx <= state.port.queue_q[port].write_idx,
            ))


def spec_to_lemma(name):
    return [
        current_partition_valid,
        port_type_valid,
        allocated_ports_consistent,
        queue_consistent,
    ]
