import z3

import libirpy.util as util
import datatypes as dt


def sys_create_sampling_port(sc, old, sampling_port_name, max_message_size,
                             port_direction, refresh_period):
    current = old.current_partition

    # Covert channel 3: Partition port identifier space according to partitions
    # Otherwise the allocation is a channel
    portid = z3.Concat(
            current,
            old.partition[current].num_ports)

    cond = util.Cases(
        # Number of sampling ports exceeds configuration
        (z3.UGE(old.partition[current].num_ports,
                sc.max_sampling_ports(current)),
            dt.INVALID_CONFIG),

        # Sampling port does not exist in configuration for partition
        (z3.Not(sc.is_port_sampling(sampling_port_name)),
            dt.INVALID_CONFIG),
        (sc.port_config[sampling_port_name].partition != current,
            dt.INVALID_CONFIG),

        # Port with this name has already been allocated
        (old.port.is_port_allocated(sampling_port_name),
            dt.NO_ACTION),

        # Max message size is non-zero and matches configuration
        (max_message_size == 0,
            dt.INVALID_CONFIG),
        (max_message_size != sc.port_config[sampling_port_name].max_message_size,
            dt.INVALID_CONFIG),

        # Direction does not match configuration
        (port_direction != sc.port_config[sampling_port_name].port_direction,
            dt.INVALID_CONFIG),

        # Refresh period is negative
        (refresh_period < 0, dt.INVALID_CONFIG),

        default=portid)

    new = old.copy()

    new.partition[current].num_ports += 1
    new.port[portid].port_type = dt.PORT_TYPE_SAMPLING

    new.port[portid].allocated = True
    new.port[portid].port_direction = port_direction
    new.port[portid].max_message_size = max_message_size
    new.port[portid].partition = current

    new.port[portid].port_name = sampling_port_name
    new.port[sampling_port_name].port_id = portid

    # Initialize sampling port
    new.port[portid].sampling_message = z3.StringVal("")

    return (cond, None), util.If(cond.cond(negate=True), new, old)


def sys_write_sampling_message(sc, old, sampling_port_id, message):
    length = z3.Length(message)

    cond = util.Cases(
        # Covert channel 2: Check if the sampling port belongs to the current partition,
        # no other partition should be able to write to this port
        (old.port[sampling_port_id].partition != old.current_partition,
            dt.INVALID_PARAM),

        # sampling_port_id does not identify an existing sampling port
        (z3.Not(old.is_port_sampling(sampling_port_id)),
            dt.INVALID_PARAM),
        (z3.Not(old.port[sampling_port_id].allocated),
            dt.INVALID_PARAM),

        # Length is greater than MAX_MESSAGE_SIZE for the port
        (sc.gte(length, old.port[sampling_port_id].max_message_size),
            dt.INVALID_CONFIG),

        # length is zero
        (length == 0, dt.INVALID_PARAM),

        # The specified port is not a source port
        (z3.Not(old.port.is_port_src(sampling_port_id)),
            dt.INVALID_MODE),

        default=dt.NO_ERROR)

    new = old.copy()

    new.port[sampling_port_id].sampling_message = message

    return (cond, old.port[sampling_port_id].max_message_size), util.If(cond.cond(negate=True), new, old)


def sys_read_sampling_message(_, old, sampling_port_id, message_addr=None):
    cond = util.Cases(
        # Covert channel 2: Check if the sampling port belongs to the current partition,
        # no other partition should be able to read this port
        (old.port[sampling_port_id].partition != old.current_partition,
            dt.INVALID_PARAM),

        # sampling_port_id does not identify an existing sampling port
        (z3.Not(old.is_port_sampling(sampling_port_id)),
            dt.INVALID_PARAM),
        (z3.Not(old.port[sampling_port_id].allocated),
            dt.INVALID_PARAM),

        # The specified port is not a destination port
        (z3.Not(old.port.is_port_src(sampling_port_id)),
            dt.INVALID_MODE),

        default=dt.NO_ERROR)

    # TODO: Check if the age of the message is within REFRESH_PERIOD

    new = old.copy()

    msg = new.port[sampling_port_id].sampling_message

    return (cond, msg), util.If(cond.cond(negate=True), new, old)


def sys_get_sampling_port_id(sc, old, sampling_port_name):
    portid = old.port[sampling_port_name].port_id

    cond = util.Cases(
        # sampling_port_id does not identify an existing sampling port
        (sc.port_config[sampling_port_name].partition != old.current_partition,
            dt.INVALID_CONFIG),
        (z3.Not(old.port.is_port_allocated(sampling_port_name)),
            dt.INVALID_CONFIG),
        (z3.Not(old.is_port_sampling(portid)),
            dt.INVALID_CONFIG),
        (old.port[portid].partition != old.current_partition,
            dt.INVALID_CONFIG),
        default=dt.NO_ERROR)

    return (cond, portid), old


def sys_get_sampling_port_status(_, old, sampling_port_id):
    cond = util.Cases(
        # sampling_port_id does not identify an existing sampling port
        (z3.Not(old.is_port_sampling(sampling_port_id)),
            dt.INVALID_CONFIG),
        (z3.Not(old.port[sampling_port_id].allocated),
            dt.INVALID_CONFIG),

        # Covert channel 2: Should check if port belongs to current partition
        (dt.port_id_partition(sampling_port_id) != old.current_partition,
            dt.INVALID_CONFIG),
        (old.port[sampling_port_id].partition != old.current_partition,
            dt.INVALID_CONFIG),

        default=dt.NO_ERROR)

    # TODO: Check refresh validity
    valid = z3.BoolVal(True)

    return (cond, valid), old


def sys_create_queueing_port(sc, old, queueing_port_name, max_message_size,
                            max_nb_message, port_direction):
    current = old.current_partition

    # Covert channel 3: Partition port identifier space according to partitions
    # Otherwise the allocation is a channel
    portid = z3.Concat(
            current,
            old.partition[current].num_ports)

    cond = util.Cases(
        # Number of queueing ports exceeds configuration
        (z3.UGE(old.partition[current].num_ports,
                sc.max_queueing_ports(current)),
            dt.INVALID_CONFIG),

        # Queueing port does not exist in configuration for partition
        (z3.Not(sc.is_port_queueing(queueing_port_name)),
            dt.INVALID_CONFIG),
        (sc.port_config[queueing_port_name].partition != current,
            dt.INVALID_CONFIG),

        # Port with this name has already been allocated
        (old.port.is_port_allocated(queueing_port_name),
            dt.NO_ACTION),

        # Max message size is non-zero and matches configuration
        (max_message_size == 0,
            dt.INVALID_CONFIG),
        (max_message_size != sc.port_config[queueing_port_name].max_message_size,
            dt.INVALID_CONFIG),

        # Max queue size is non-zero and matches configuration
        (max_nb_message == 0,
            dt.INVALID_CONFIG),
        (max_nb_message != sc.port_config[queueing_port_name].queueing_max_nb_message,
            dt.INVALID_CONFIG),

        # Direction does not match configuration
        (port_direction != sc.port_config[queueing_port_name].port_direction,
            dt.INVALID_CONFIG),

        default=portid)

    new = old.copy()

    new.partition[current].num_ports += 1
    new.port[portid].port_type = dt.PORT_TYPE_QUEUEING

    new.port[portid].allocated = True
    new.port[portid].port_direction = port_direction
    new.port[portid].max_message_size = max_message_size
    new.port[portid].partition = current

    new.port[portid].port_name = queueing_port_name
    new.port[queueing_port_name].port_id = portid

    # Initialize queue port
    new.port[portid].queueing_max_nb_message = max_nb_message
    new.port.queue_q[portid].read_idx = 0
    new.port.queue_q[portid].write_idx = 0

    return (cond, None), util.If(cond.cond(negate=True), new, old)


def sys_send_queueing_message(sc, old, queueing_port_id, message, time_out):
    length = z3.Length(message)

    cond = util.Cases(
        # Covert channel 2: Check if the sampling port belongs to the current partition,
        # no other partition should be able to write to this port
        (old.port[queueing_port_id].partition != old.current_partition,
            dt.INVALID_PARAM),

        # queueing port does not identify an existing queueing  port
        (z3.Not(old.is_port_queueing(queueing_port_id)),
            dt.INVALID_PARAM),
        (z3.Not(old.port[queueing_port_id].allocated),
            dt.INVALID_PARAM),

        # Length is greater than MAX_MESSAGE_SIZE for the port
        (sc.gte(length, old.port[queueing_port_id].max_message_size),
            dt.INVALID_CONFIG),

        # length is zero
        (length == 0, dt.INVALID_PARAM),

        # The specified port is not a source port
        (z3.Not(old.port.is_port_src(queueing_port_id)),
            dt.INVALID_MODE),

        # The queue's size is not full
        # (old.port.queue_q.len(queueing_port_id) ==
        #         z3.BV2Int(old.port[queueing_port_id].queueing_max_nb_message),
        #         dt.NOT_AVAILABLE),

        default=dt.NO_ERROR)

    new = old.copy()

    new.port.queue_q.enqueue(queueing_port_id, message)

    return cond, util.If(cond.cond(negate=True), new, old)


def sys_receive_queueing_message(_, old, queueing_port_id, time_out=None, message_addr=None):
    cond = util.Cases(
        # Covert channel 2: Check if the sampling port belongs to the current partition,
        # no other partition should be able to read this port
        (old.port[queueing_port_id].partition != old.current_partition,
            dt.INVALID_PARAM),

        # sampling_port_id does not identify an existing sampling port
        (z3.Not(old.is_port_queueing(queueing_port_id)),
            dt.INVALID_PARAM),
        (z3.Not(old.port[queueing_port_id].allocated),
            dt.INVALID_PARAM),

        # The specified port is not a destination port
        (z3.Not(old.port.is_port_src(queueing_port_id)),
            dt.INVALID_MODE),

        # Normal:
        (old.port.queue_q.is_empty(queueing_port_id),
            dt.NOT_AVAILABLE),

        default=dt.NO_ERROR)

    # TODO: timeout

    new = old.copy()

    msg = new.port.queue_q.dequeue(queueing_port_id)

    return (cond, msg), util.If(cond.cond(negate=True), new, old)


def sys_get_queueing_port_id(_, old, queueing_port_name):
    portid = old.port[queueing_port_name].port_id

    cond = util.Cases(
        # queueing_port_id does not identify an existing queueing port
        (z3.Not(old.is_port_queueing(portid)),
            dt.INVALID_CONFIG),
        (z3.Not(old.port.is_port_allocated(queueing_port_name)),
            dt.INVALID_CONFIG),
        (old.port[portid].partition != old.current_partition,
            dt.INVALID_CONFIG),
        default=dt.NO_ERROR)

    new = old.copy()

    return (cond, portid), util.If(cond.cond(negate=True), new, old)


def sys_get_queueing_port_status(sc, old, queueing_port_id):
    cond = util.Cases(
        default=dt.NO_ERROR)

    new = old.copy()

    return cond, util.If(cond.cond(negate=True), new, old)


def sys_clear_queueing_port(sc, old, queueing_port_id):
    cond = util.Cases(
        # Covert channel 2: Check if the sampling port belongs to the current partition,
        # no other partition should be able to read this port
        (old.port[queueing_port_id].partition != old.current_partition,
            dt.INVALID_PARAM),

        # sampling_port_id does not identify an existing sampling port
        (z3.Not(old.is_port_queueing(queueing_port_id)),
            dt.INVALID_PARAM),
        (z3.Not(old.port[queueing_port_id].allocated),
            dt.INVALID_PARAM),

        # The specified port is not a destination port
        (z3.Not(old.port.is_port_src(queueing_port_id)),
            dt.INVALID_MODE),

        default=dt.NO_ERROR)

    new = old.copy()

    new.port.queue_q.clear(queueing_port_id)

    return (cond, None), util.If(cond.cond(negate=True), new, old)


def sys_transfer_sampling_message(sc, old, sampling_port_id):
    cond = util.Cases(
        # sampling_port_id does not identify an existing sampling port
        (z3.Not(old.is_port_sampling(sampling_port_id)),
            dt.INVALID_CONFIG),
        (z3.Not(old.port[sampling_port_id].allocated),
            dt.INVALID_CONFIG),

        # Can only transfer from src ports
        (z3.Not(old.port.is_port_src(sampling_port_id)),
            dt.INVALID_PARAM),
        default=dt.NO_ERROR)

    new = old.copy()

    # Copy message from `sampling_port_id` to each destination
    # in channel
    new.port.sampling_message = lambda to, oldfn=None: \
        util.If(old.port[sampling_port_id].channel(to),
           old.port[sampling_port_id].sampling_message,
           oldfn(to))

    return (cond, None), util.If(cond.cond(negate=True), new, old)

def sys_transfer_queueing_message(sc, old, queueing_port_id):

    dest = old.port[queueing_port_id].queue_dest
    # dest_queue_full = old.port.queue_q.len(dest) < z3.BV2Int(old.port[dest].queueing_max_nb_message)

    cond = util.Cases(
        # queueing_port_id does not identify an existing queueing port
        (z3.Not(old.is_port_queueing(queueing_port_id)),
            dt.INVALID_CONFIG),
        (z3.Not(old.port[queueing_port_id].allocated),
            dt.INVALID_CONFIG),

        # Destination has been initialized and is valid
        (z3.Not(old.is_port_queueing(dest)), dt.INVALID_CONFIG),
        (z3.Not(old.port[dest].allocated), dt.INVALID_CONFIG),

        # Can only transfer from src ports
        (z3.Not(old.port.is_port_src(queueing_port_id)),
            dt.INVALID_PARAM),

        # Can only transfer to dst ports
        # Should this be an invariant?
        (z3.Not(old.port.is_port_dst(dest)),
            dt.INVALID_PARAM),

        ###

        (z3.Not(old.port.queue_q.len(queueing_port_id) > 0),
            dt.NO_ERROR),

        # Covert channel 1: If the dest queue is full,
        # silently drop the message.
        # (z3.Not(dest_queue_full),
        #     dt.NO_ERROR),

        default=dt.NO_ERROR)

    new = old.copy()

    # Pop from src and write to dest
    m = new.port.queue_q.dequeue(queueing_port_id)
    new.port.queue_q.enqueue(dest, m)

    return (cond, None), util.If(cond.cond(negate=True), new, old)


def sys_schedule(sc, old):

    cond = util.Cases(
        default=dt.NO_ERROR
    )

    new = old.copy()

    new.scheduler.current_slot += 1

    new.scheduler.current_slot = util.If(
            new.scheduler.current_slot == sc.scheduler_config.num_slots,
            0,
            new.scheduler.current_slot)

    return (cond, None), util.If(cond.cond(negate=True), new, old)

