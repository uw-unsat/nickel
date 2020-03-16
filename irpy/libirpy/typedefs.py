import z3


bool_t = z3.BoolSort()

uint128_t = z3.BitVecSort(128)
uint64_t = z3.BitVecSort(64)
uint32_t = z3.BitVecSort(32)
uint16_t = z3.BitVecSort(16)
uint8_t = z3.BitVecSort(8)

int128_t = z3.BitVecSort(128)
int64_t = z3.BitVecSort(64)
int32_t = z3.BitVecSort(32)
int16_t = z3.BitVecSort(16)
int8_t = z3.BitVecSort(8)

MAX_INT128 = z3.BitVecVal(2 ** 128 - 1, 128)
MAX_INT64  = z3.BitVecVal(2 ** 64 - 1, 64)
MAX_INT32  = z3.BitVecVal(2 ** 32 - 1, 32)


def i128(val):
    return z3.BitVecVal(val, 128)


def i64(val):
    return z3.BitVecVal(val, 64)


def i32(val):
    return z3.BitVecVal(val, 32)


def i16(val):
    return z3.BitVecVal(val, 16)


def i8(val):
    return z3.BitVecVal(val, 8)


def i1(val):
    return z3.BitVecVal(val, 1)
