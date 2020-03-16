import unittest

import itypes as it


class TestReference(unittest.TestCase):
    def test_type_parsing(self):
        ctx = {}
        ctx.types = {}

        it.declare_struct_type(ctx, 'struct.trap_regs', 'i64', 'i64', 'i64', 'i64', 'i64',
                               'i64', 'i64', 'i64', 'i64', 'i64', 'i64', 'i64', 'i64', 'i64', 'i64', '[8 x i8]',)
        it.declare_struct_type(ctx, 'struct.proc', 'i32', 'i64', 'i64',
                               '[16 x i64]', 'i64', '%struct.trap_regs = type { i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, [8 x i8] }', 'i64', '[8 x i8]',)

        self.assertEqual(it.parse_type(ctx, 'i64***'),
                         it.PointerType(it.PointerType(it.PointerType(it.IntType(64)))))
        it.parse_type(ctx, 'i64***')
        it.parse_type(ctx, '[0 x i8]')
        it.parse_type(ctx, '[0 x i8]*')
        it.parse_type(ctx, '[3 x [4 x i32]]')
        it.parse_type(ctx, '[3 x [4 x i32]]')
        it.parse_type(ctx, '[3 x [4 x i32]]')
        it.parse_type(ctx, '%mytype = type { %struct.trap_regs*, i32 }')
