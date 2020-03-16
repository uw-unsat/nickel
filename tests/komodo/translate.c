#include <sys/bitfield.h>
#include "translate.h"

uint8_t x86_insns[SZ_4K / X86_INSN_LEN][X86_INSN_LEN] __aligned(SZ_4K);

uint32_t arm_insns[] = {
#       include "test_enclave.inc"
};

static uint8_t *emit_code(uint8_t *ptr, uint32_t bytes, size_t len)
{
        if (len == 1) {
                *ptr = bytes;
        } else if (len == 2) {
                *(uint16_t *)ptr = bytes;
        } else {
                *(uint32_t *)ptr = bytes;
                barrier();
        }
        return ptr + len;
}

#define EMIT(bytes, len) \
        do { prog = emit_code(prog, bytes, len); } while (0)

#define EMIT1(b1)               EMIT(b1, 1)
#define EMIT2(b1, b2)           EMIT((b1) + ((b2) << 8), 2)
#define EMIT3(b1, b2, b3)       EMIT((b1) + ((b2) << 8) + ((b3) << 16), 3)
#define EMIT4(b1, b2, b3, b4)   EMIT((b1) + ((b2) << 8) + ((b3) << 16) + ((b4) << 24), 4)
#define EMIT1_off32(b1, off) \
        do { EMIT1(b1); EMIT(off, 4); } while (0)
#define EMIT2_off32(b1, b2, off) \
        do { EMIT2(b1, b2); EMIT(off, 4); } while (0)
#define EMIT3_off32(b1, b2, b3, off) \
        do { EMIT3(b1, b2, b3); EMIT(off, 4); } while (0)
#define EMIT4_off32(b1, b2, b3, b4, off) \
        do { EMIT4(b1, b2, b3, b4); EMIT(off, 4); } while (0)

#define EMIT_NOP1()             EMIT1(0x90)
#define EMIT_NOP2()             do { EMIT1(0x66); EMIT_NOP1(); } while (0)
#define EMIT_NOP3()             do { EMIT2(0x0F, 0x1F); EMIT1(0x00); } while (0)
#define EMIT_NOP4()             EMIT4(0x0F, 0x1F, 0x40, 0x00)
#define EMIT_NOP5()             do { EMIT4(0x0F, 0x1F, 0x44, 0x00); EMIT1(0x00); } while (0)
#define EMIT_NOP6()             do { EMIT1(0x66); EMIT_NOP5(); } while (0)
#define EMIT_NOP7()             do { EMIT3(0x0F, 0x1F, 0x80); EMIT4(0x00, 0x00, 0x00, 0x00); } while (0)
#define EMIT_NOP8()             do { EMIT4(0x0F, 0x1F, 0x84, 0x00); EMIT4(0x00, 0x00, 0x00, 0x00); } while (0)
#define EMIT_NOP9()             do { EMIT1(0x66); EMIT_NOP8(); } while (0)

#define EMIT_RDTSC()            EMIT2(0x0F, 0x31)

/* lahf; seto %al */
#define EMIT_SAVE_FLAGS()       do { EMIT1(0x9F); EMIT3(0x0F, 0x90, 0xC0); } while (0)
/* add $0x7f, %al; sahf */
#define EMIT_RESTORE_FLAGS()    do { EMIT3(0x80, 0xC0, 0x7F); EMIT1(0x9E); } while (0)

/* mov dst, src */
#define EMIT_MOV(DST, SRC)                                      \
        do {                                                    \
                if (is_ereg(DST) || is_ereg(SRC))               \
                        EMIT1(add_2mod(0x40, DST, SRC));        \
                EMIT2(0x89, add_2reg(0xC0, DST, SRC));          \
        } while (0)

/* list of x86 cond jumps opcodes (. + s8)
 * Add 0x10 (and an extra 0x0f) to generate far jumps (. + s32)
 */
#define X86_JB                  0x72
#define X86_JAE                 0x73
#define X86_JE                  0x74
#define X86_JNE                 0x75
#define X86_JBE                 0x76
#define X86_JA                  0x77
#define X86_JL                  0x7C
#define X86_JGE                 0x7D
#define X86_JLE                 0x7E
#define X86_JG                  0x7F

/*
 * Since test_enclave uses r0-3, r9-11, map these registers to
 * ones that have simpler encoding.
 *
 * %rax and %rdx are clobbered and not used.
 */
static const int reg2hex[] = {
        [0] = 7,                /* rdi */
        [1] = 6,                /* rsi */
        [2] = 5,                /* rbp */
        [3] = 1,                /* rcx */
        [4] = 0,                /* r8 */
        [5] = 1,                /* r9 */
        [6] = 2,                /* r10 */
        [7] = 3,                /* r11 */
        [8] = 4,                /* r12 */
        [9] = 5,                /* r13 */
        [10] = 6,               /* r14 */
        [11] = 7,               /* r15 */
};

/*
 * is_ereg() == true if 'reg' maps to r8..r15
 * which need extra byte of encoding;
 * rax, rcx, ..., rbp have simpler encoding.
 */
static bool is_ereg(uint32_t reg)
{
        return reg >= 4;
}

/* add modifiers if 'reg' maps to x64 registers r8..r15 */
static uint8_t add_1mod(uint8_t byte, uint32_t reg)
{
        if (is_ereg(reg))
                byte |= 1;
        return byte;
}

static uint8_t add_2mod(uint8_t byte, uint32_t r1, uint32_t r2)
{
        if (is_ereg(r1))
                byte |= 1;
        if (is_ereg(r2))
                byte |= 4;
        return byte;
}

/* encode 'dst_reg' register into x64 opcode 'byte' */
static uint8_t add_1reg(uint8_t byte, uint32_t dst_reg)
{
        return byte + reg2hex[dst_reg];
}

/* encode 'dst_reg' and 'src_reg' registers into x64 opcode 'byte' */
static uint8_t add_2reg(uint8_t byte, uint32_t dst_reg, uint32_t src_reg)
{
        return byte + reg2hex[dst_reg] + (reg2hex[src_reg] << 3);
}

static bool is_imm8(int value)
{
        return value <= 127 && value >= -128;
}

static uint8_t *translate_branch(uint8_t *prog, uint32_t insn)
{
        uint32_t cond;
        uint8_t jmp_cond;
        int32_t jmp_offset, offset24;

        /* ignore bl for now */
        if (insn & BIT_32(24))
                return NULL;

        cond = FIELD_GET(GENMASK_32(31, 28), insn);
        /*
         * The offset needs to be left-shifted by two bits.  Also it's
         * 2 words ahead the current instruction.
         */
        offset24 = insn & GENMASK_32(23, 0);
        jmp_offset = (((offset24 << 8) >> 8) + 2) * X86_INSN_LEN;

        switch (cond) {
        default:
                return NULL;
        case 0x0:
                jmp_cond = X86_JE;
                break;
        case 0x1:
                jmp_cond = X86_JNE;
                break;
        case 0x2:
                /* unsigned >= */
                jmp_cond = X86_JAE;
                break;
        case 0x3:
                /* unsigned < */
                jmp_cond = X86_JB;
                break;
        case 0x8:
                /* unsigned > */
                jmp_cond = X86_JA;
                break;
        case 0x9:
                /* unsigned <= */
                jmp_cond = X86_JBE;
                break;
        case 0xa:
                /* signed >= */
                jmp_cond = X86_JGE;
                break;
        case 0xb:
                /* signed < */
                jmp_cond = X86_JL;
                break;
        case 0xc:
                /* signed > */
                jmp_cond = X86_JG;
                break;
        case 0xd:
                /* signed <= */
                jmp_cond = X86_JLE;
                break;
        case 0xe:
                /* unconditional jmp */
                if (is_imm8(jmp_offset - 2)) {
                        EMIT2(0xEB, jmp_offset - 2);
                } else {
                        EMIT1_off32(0xE9, jmp_offset - 6);
                }
                return prog;
        }

        if (is_imm8(jmp_offset - 2)) {
                EMIT2(jmp_cond, jmp_offset - 2);
        } else {
                EMIT2_off32(0x0F, jmp_cond + 0x10, jmp_offset - 6);
        }
        return prog;
}

static uint8_t *translate_mrc(uint8_t *prog, uint32_t insn)
{
        uint8_t dst_reg = FIELD_GET(GENMASK_32(15, 12), insn);
        /*
         * The format is: mrc coproc, opcode1, Rd, CRn, CRm{, opcode2}
         * such as:       mrc p15, 0, Rd, c9, c13, 0
         */
        /* handle only p15 for now */
        if (FIELD_GET(GENMASK_32(11, 8), insn) != 15)
                return NULL;

        EMIT_RDTSC();
        /* mov %eax into dst_reg */
        EMIT_MOV(dst_reg, 0);
        return prog;
}

static uint8_t *translate_data_proc(uint8_t *prog, uint32_t insn, uint8_t b2, uint8_t b3)
{
        uint32_t dst_reg, op1_reg;
        bool cond = (insn & BIT_32(20));

        dst_reg = FIELD_GET(GENMASK_32(15, 12), insn);
        op1_reg = FIELD_GET(GENMASK_32(19, 16), insn);

        if (insn & BIT_32(25)) {
                /* imm */
                uint32_t imm32;

                /* don't handle rotate for now */
                if (FIELD_GET(GENMASK_32(11, 8), insn))
                        return NULL;
                imm32 = FIELD_GET(GENMASK_32(7, 0), insn);
                if (!cond)
                        EMIT_SAVE_FLAGS();

                /* mov op1 to dst */
                EMIT_MOV(dst_reg, op1_reg);

                /* op dst, imm */
                if (is_imm8(imm32))
                        EMIT3(0x83, add_1reg(b3, dst_reg), imm32);
                else
                        EMIT2_off32(0x81, add_1reg(b3, dst_reg), imm32);

                if (!cond)
                        EMIT_RESTORE_FLAGS();
        } else {
                /* reg */
                uint32_t src_reg;

                /* don't handle shift for now */
                if (FIELD_GET(GENMASK_32(11, 4), insn))
                        return NULL;
                src_reg = FIELD_GET(GENMASK_32(3, 0), insn);

                if (!cond)
                        EMIT_SAVE_FLAGS();

                /* mov op1 to dst */
                EMIT_MOV(dst_reg, op1_reg);

                /* op dst, src */
                if (is_ereg(dst_reg) || is_ereg(src_reg))
                        EMIT1(add_2mod(0x40, dst_reg, src_reg));
                EMIT2(b2, add_2reg(0xC0, dst_reg, src_reg));

                if (!cond)
                        EMIT_RESTORE_FLAGS();
        }

        return prog;
}

static uint8_t *translate_add(uint8_t *prog, uint32_t insn)
{
        return translate_data_proc(prog, insn, 0x01, 0xC0);
}

static uint8_t *translate_sub(uint8_t *prog, uint32_t insn)
{
        return translate_data_proc(prog, insn, 0x29, 0xE8);
}

static uint8_t *translate_cmp(uint8_t *prog, uint32_t insn)
{
        uint32_t dst_reg, imm32;

        /* must set condition code */
        if (!(insn & BIT_32(20)))
                return NULL;

        dst_reg = FIELD_GET(GENMASK_32(15, 12), insn);

        /* ignore reg cmp */
        if (!(insn & BIT_32(25)))
                return NULL;
        /* don't handle rotate for now */
        if (FIELD_GET(GENMASK_32(11, 8), insn))
                return NULL;
        imm32 = FIELD_GET(GENMASK_32(7, 0), insn);

        /* cmp dst_reg, imm8 */
        EMIT1(add_1mod(0x48, dst_reg));
        if (is_imm8(imm32))
                EMIT3(0x83, add_1reg(0xF8, dst_reg), imm32);
        else
                EMIT2_off32(0x81, add_1reg(0xF8, dst_reg), imm32);
        return prog;
}

static uint8_t *translate_mov(uint8_t *prog, uint32_t insn)
{
        uint32_t dst_reg;

        /* must not set condition code */
        if (insn & BIT_32(20))
                return NULL;

        dst_reg = FIELD_GET(GENMASK_32(15, 12), insn);

        if (insn & BIT_32(25)) {
                /* mov dst, imm */
                uint32_t imm32;

                /* don't handle rotate for now */
                if (FIELD_GET(GENMASK_32(11, 8), insn))
                        return NULL;
                imm32 = FIELD_GET(GENMASK_32(7, 0), insn);
                if (is_ereg(dst_reg))
                        EMIT1(add_1mod(0x40, dst_reg));
                EMIT1_off32(add_1reg(0xB8, dst_reg), imm32);
        } else {
                /* mov dst, src */
                uint32_t src_reg;

                /* don't handle shift for now */
                if (FIELD_GET(GENMASK_32(11, 4), insn))
                        return NULL;
                src_reg = FIELD_GET(GENMASK_32(3, 0), insn);
                EMIT_MOV(dst_reg, src_reg);
        }

        return prog;
}

static uint8_t *translate_movw(uint8_t *prog, uint32_t insn)
{
        uint32_t dst_reg, imm4, imm12;

        /* must not set condition code */
        if (insn & BIT_32(20))
                return NULL;

        dst_reg = FIELD_GET(GENMASK_32(15, 12), insn);
        imm4 = FIELD_GET(GENMASK_32(19, 16), insn);
        imm12 = FIELD_GET(GENMASK_32(19, 16), insn);

        if (is_ereg(dst_reg))
                EMIT1(add_1mod(0x40, dst_reg));
        EMIT1_off32(add_1reg(0xB8, dst_reg), (imm4 << 12) | imm12);
        return prog;
}

static uint8_t *translate_svc(uint8_t *prog, uint32_t insn)
{
        /* svc => int $0x80 */
        EMIT2(0xcd, 0x80);
        return prog;
}

static uint8_t *translate_one(uint8_t *prog, uint32_t insn)
{
        if (FIELD_GET(GENMASK_32(27, 25), insn) == 0x5) {
                return translate_branch(prog, insn);
        } else {
                /* only b/bl use cond */
                if (FIELD_GET(GENMASK_32(31, 28), insn) != 0xe)
                        return NULL;
        }

        if ((FIELD_GET(GENMASK_32(27, 24), insn) == 0xe) && (insn & BIT_32(20)) && (insn & BIT_32(4)))
                return translate_mrc(prog, insn);

        if ((FIELD_GET(GENMASK_32(27, 26), insn) == 0x0) && (FIELD_GET(GENMASK_32(24, 21), insn) == 0x4))
                return translate_add(prog, insn);

        if ((FIELD_GET(GENMASK_32(27, 26), insn) == 0x0) && (FIELD_GET(GENMASK_32(24, 21), insn) == 0x2))
                return translate_sub(prog, insn);

        if ((FIELD_GET(GENMASK_32(27, 26), insn) == 0x0) && (FIELD_GET(GENMASK_32(24, 21), insn) == 0xa))
                return translate_cmp(prog, insn);

        if ((FIELD_GET(GENMASK_32(27, 26), insn) == 0x0) && (FIELD_GET(GENMASK_32(24, 21), insn) == 0xd))
                return translate_mov(prog, insn);

        /* movw variant */
        if ((FIELD_GET(GENMASK_32(27, 24), insn) == 0x3) && (FIELD_GET(GENMASK_32(23, 20), insn) == 0x0))
                return translate_movw(prog, insn);

        if (FIELD_GET(GENMASK_32(27, 24), insn) == 0xf)
                return translate_svc(prog, insn);

        return NULL;
}

static uint8_t *fill_nops(uint8_t *prog, size_t n)
{
#if 1
        for (; n; --n)
                EMIT_NOP1();
#endif

        switch (n) {
        case 0:
                break;
        case 1:
                EMIT_NOP1();
                break;
        case 2:
                EMIT_NOP2();
                break;
        case 3:
                EMIT_NOP3();
                break;
        case 4:
                EMIT_NOP4();
                break;
        case 5:
                EMIT_NOP5();
                break;
        case 6:
                EMIT_NOP6();
                break;
        case 7:
                EMIT_NOP7();
                break;
        case 8:
                EMIT_NOP8();
                break;
        default:
                EMIT_NOP9();
                prog = fill_nops(prog, n - 9);
                break;
        }
        return prog;
}

static uint8_t *fill_hole(uint8_t *prog, size_t n)
{
        for (; n; --n)
                EMIT1(0xCC);
        return prog;
}

static size_t translate(void *dst, const uint32_t *src, size_t n)
{
        size_t i;

        for (i = 0; i < n; ++i) {
                uint8_t *prog0, *prog;

                prog0 = dst + i * X86_INSN_LEN;
                prog = translate_one(prog0, src[i]);
                /* failed */
                if (!prog)
                        prog = fill_hole(prog0, X86_INSN_LEN);
                /* too many bytes; increase X86_INSN_LEN */
                if (prog0 + X86_INSN_LEN < prog)
                        return 0;
                prog = fill_nops(prog, prog0 + X86_INSN_LEN - prog);
        }

        return n;
}

size_t translate_test_enclave(void)
{
        return translate(x86_insns, arm_insns, ARRAY_SIZE(arm_insns));
}
