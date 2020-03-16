
import datatypes as dt
import nickel.prototype as p



prototypes = {
    # Sampling ports
    'sys_create_sampling_port': [p.arg('port_name', dt.port_name_t),
                                 p.arg('message_size', dt.buffer_size_t),
                                 p.arg('port_direction', dt.port_direction_t),
                                 p.arg('refresh_period', dt.time_t)],
    'sys_write_sampling_message': [('port_id', dt.port_id_t),
                                   ('message', dt.message_t)],
    'sys_read_sampling_message': [('port_id', dt.port_id_t)],
    'sys_get_sampling_port_id': [('port_name', dt.port_name_t)],
    'sys_get_sampling_port_status': [('port_id', dt.port_id_t)],

    # Queueing port
    'sys_create_queueing_port': [('port_name', dt.port_name_t),
                                 p.i64('message_size'),
                                 p.i64('message_queue_size'),
                                 ('port_direction', dt.port_direction_t)],
    'sys_send_queueing_message': [('port_id', dt.port_id_t),
                                 ('message', dt.message_t),
                                 ('timeout', dt.time_t)],
    'sys_receive_queueing_message': [('port_id', dt.port_id_t)],
    'sys_get_queueing_port_id': [('port_name', dt.port_name_t)],
    'sys_get_queueing_port_status': [('port_id', dt.port_id_t)],
    'sys_clear_queueing_port': [('port_id', dt.port_id_t)],

    # Scheduler
    # 'sys_schedule': [],

    # Transmitter
    # 'sys_transfer_sampling_message': [('port_id', dt.port_id_t)],
    # 'sys_transfer_queueing_message': [('port_id', dt.port_id_t)],
}




proto = p.Prototype(prototypes)
