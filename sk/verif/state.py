import z3
from libirpy.state import Struct, BaseStruct, Map
import datatypes as dt


class PortConfig(Struct):
    port_direction    = Map(dt.port_name_t, dt.port_direction_t)
    partition         = Map(dt.port_name_t, dt.partition_t)
    port_type         = Map(dt.port_name_t, dt.port_type_t)

    max_message_size  = Map(dt.port_name_t, dt.buffer_size_t)

    def is_port_dst(self, pname):
        return self[pname].port_direction == dt.PORT_DIRECTION_DESTINATION

    def is_port_src(self, pname):
        return self[pname].port_direction == dt.PORT_DIRECTION_SOURCE

    ## Fields specific to sampling ports

    # A channel is a single source port associated with a set of
    # destination ports
    sampling_channel = Map(dt.port_name_t, dt.port_name_t, dt.bool_t)
    sampling_refresh_period    = Map(dt.port_name_t, dt.time_t)

    ## Fields specific to queueing ports
    queueing_max_nb_message = Map(dt.port_name_t, dt.buffer_size_t)


class SchedulerConfig(Struct):
    num_slots = Map(dt.uint64_t)
    slots     = Map(dt.uint64_t, dt.partition_t)


class SKConfiguration(BaseStruct):
    max_sampling_ports = Map(dt.partition_t, dt.uint32_t)
    max_queueing_ports = Map(dt.partition_t, dt.uint32_t)

    port_config = PortConfig()

    scheduler_config = SchedulerConfig()

    gte = Map(z3.IntSort(), dt.buffer_size_t, dt.bool_t)

    def is_port_queueing(self, port_name):
        return self.port_config[port_name].port_type == dt.PORT_TYPE_QUEUEING

    def is_port_sampling(self, port_name):
        return self.port_config[port_name].port_type == dt.PORT_TYPE_SAMPLING


#########


class Queue(Struct):
    q = Map(dt.port_id_t, z3.IntSort(), dt.message_t)
    read_idx = Map(dt.port_id_t, z3.IntSort())
    write_idx = Map(dt.port_id_t, z3.IntSort())

    def is_empty(self, portid):
        return self[portid].write_idx == self[portid].read_idx

    def len(self, portid):
        return self[portid].write_idx - self[portid].read_idx

    def clear(self, portid):
        self[portid].read_idx = self[portid].write_idx

    def enqueue(self, portid, m):
        cur = self[portid].write_idx
        self[portid].write_idx += 1
        self[portid].q[cur] = m

    def dequeue(self, portid):
        cur = self[portid].read_idx
        self[portid].read_idx += 1
        return self[portid].q(cur)


class Partition(Struct):
    num_ports = Map(dt.partition_t, dt.uint32_t)


class Scheduler(Struct):
    current_slot = Map(dt.uint64_t)


class Port(Struct):
    # Sampling port with `id` has been allocated
    allocated = Map(dt.port_id_t, dt.bool_t)

    # Configured type of this port
    port_type = Map(dt.port_id_t, dt.port_type_t)

    # is a source / destination port
    port_direction   = Map(dt.port_id_t, dt.port_direction_t)

    port_name = Map(dt.port_id_t, dt.port_name_t)
    port_id   = Map(dt.port_name_t, dt.port_id_t)

    # Partition that owns `id`
    partition = Map(dt.port_id_t, dt.partition_t)

    # Max message size this port supports
    max_message_size = Map(dt.port_id_t, dt.buffer_size_t)

    # A channel is a single source port associated with a set of
    # destination ports.
    channel = Map(dt.port_id_t, dt.port_id_t, dt.bool_t)

    def is_port_dst(self, portid):
        return self[portid].port_direction == dt.PORT_DIRECTION_DESTINATION

    def is_port_src(self, portid):
        return self[portid].port_direction == dt.PORT_DIRECTION_SOURCE

    def is_port_allocated(self, portname):
        return self[portname].port_id != 0

    ### Fields specific to sampling ports

    # Current message for this port
    sampling_message = Map(dt.port_id_t, dt.message_t)

    # A channel is a single source port associated with a set of
    # destination ports.
    sampling_channel = Map(dt.port_id_t, dt.port_id_t, dt.bool_t)

    ## Fields specific to queuing ports
    queueing_max_nb_message = Map(dt.port_id_t, dt.buffer_size_t)

    # Current message queue
    queue_q = Queue()

    # Single source / single dest queue
    queue_dest = Map(dt.port_id_t, dt.port_id_t)


class Process(Struct):
    partition = Map(dt.pid_t, dt.partition_t)
    status = Map(dt.pid_t, dt.status_t)


class SKState(BaseStruct):
    partition = Partition()
    process = Process()

    port = Port()
    scheduler = Scheduler()

    current_partition = Map(dt.partition_t)
    current_process = Map(dt.pid_t)

    def is_port_queueing(self, port_id):
        return self.port[port_id].port_type == dt.PORT_TYPE_QUEUEING

    def is_port_sampling(self, port_id):
        return self.port[port_id].port_type == dt.PORT_TYPE_SAMPLING

    def get_next_portid(self, partition):
        return z3.Concat(partition,
                         self.partition[partition].next_port_id)
