from nickel.prototype import i64


syscalls = {
    'sys_spawn': [i64('fileid'), i64('quota')],
    'sys_get_quota': [],
}


psuedo_ops = {
    'sys_yield': [],
    'handle_page_fault': [i64('idx')],

    'sys_read': [i64('idx'), i64('idx')],
    'sys_write': [i64('idx'), i64('idx'), i64('value')],
}


all_ops = dict(syscalls.items() + psuedo_ops.items())
