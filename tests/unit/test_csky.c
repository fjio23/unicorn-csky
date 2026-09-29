#include "unicorn_test.h"

static const uint64_t base = 0x1000;
/* movi16 r0, 7; addi16 r0, 3; movi32 r17, 0x1234 */
static const uint8_t mixed[] = {0x07, 0x30, 0x02, 0x20, 0x11, 0xea, 0x34, 0x12};

static uc_engine *open_csky(int model)
{
    uc_engine *uc = NULL;
    OK(uc_open(UC_ARCH_CSKY, UC_MODE_CSKY_V2, &uc));
    OK(uc_ctl_set_cpu_model(uc, model));
    OK(uc_mem_map(uc, base, 0x2000, UC_PROT_ALL));
    OK(uc_mem_write(uc, base, mixed, sizeof(mixed)));
    return uc;
}

static uint32_t read32(uc_engine *uc, int reg)
{
    uint32_t value = 0;
    OK(uc_reg_read(uc, reg, &value));
    return value;
}

static void test_csky_models(void)
{
    int model;
    TEST_CHECK(uc_arch_supported(UC_ARCH_CSKY));
    for (model = UC_CPU_CSKY_CK803; model < UC_CPU_CSKY_ENDING; model++) {
        uc_engine *uc = open_csky(model);
        OK(uc_emu_start(uc, base, base + sizeof(mixed), 0, 0));
        TEST_CHECK(read32(uc, UC_CSKY_REG_R0) == 10);
        TEST_CHECK(read32(uc, UC_CSKY_REG_R17) == 0x1234);
        TEST_CHECK(read32(uc, UC_CSKY_REG_PC) == base + sizeof(mixed));
        OK(uc_close(uc));
    }
}

static void test_csky_context(void)
{
    uc_engine *uc = open_csky(UC_CPU_CSKY_CK803);
    uc_context *ctx;
    uint32_t value = 0xabcdef00;
    OK(uc_emu_start(uc, base, base + sizeof(mixed), 0, 1));
    OK(uc_context_alloc(uc, &ctx));
    OK(uc_context_save(uc, ctx));
    OK(uc_emu_start(uc, base + 2, base + sizeof(mixed), 0, 0));
    OK(uc_context_reg_write(ctx, UC_CSKY_REG_SP, &value));
    OK(uc_context_restore(uc, ctx));
    TEST_CHECK(read32(uc, UC_CSKY_REG_R0) == 7);
    TEST_CHECK(read32(uc, UC_CSKY_REG_PC) == base + 2);
    TEST_CHECK(read32(uc, UC_CSKY_REG_R14) == value);
    OK(uc_context_free(ctx));
    OK(uc_close(uc));
}

static void test_csky_register_sizes(void)
{
    uc_engine *uc = open_csky(UC_CPU_CSKY_CK810);
    uint64_t value = UINT64_C(0x4004000000000000), actual = 0;
    uint16_t small = 0;
    size_t size = sizeof(small);
    uc_assert_err(UC_ERR_OVERFLOW, uc_reg_read2(uc, UC_CSKY_REG_R0, &small, &size));
    TEST_CHECK(small == 0); /* Overflow must not write to the buffer. */
    OK(uc_reg_write(uc, UC_CSKY_REG_F15, &value));
    OK(uc_reg_read(uc, UC_CSKY_REG_F15, &actual));
    TEST_CHECK(actual == value);
    size = sizeof(value);
    uc_assert_err(UC_ERR_ARG, uc_reg_read2(uc, UC_CSKY_REG_ENDING, &value, &size));
    OK(uc_close(uc));
}

static void test_csky_invalid_modes(void)
{
    uc_engine *uc = NULL;
    uc_assert_err(UC_ERR_MODE, uc_open(UC_ARCH_CSKY, UC_MODE_BIG_ENDIAN | UC_MODE_CSKY_V2, &uc));
    uc_assert_err(UC_ERR_MODE, uc_open(UC_ARCH_CSKY, UC_MODE_64, &uc));
    OK(uc_open(UC_ARCH_CSKY, UC_MODE_CSKY_V2, &uc));
    uc_assert_err(UC_ERR_ARG, uc_ctl_set_cpu_model(uc, UC_CPU_CSKY_ENDING));
    OK(uc_close(uc));
}

static void test_csky_memory_fault(void)
{
    /* ld.w16 r2, (r1, 0) */
    const uint8_t code[] = {0x40, 0x91};
    uint32_t address = 0x9000;
    uc_engine *uc = open_csky(UC_CPU_CSKY_CK803);
    OK(uc_mem_write(uc, base, code, sizeof(code)));
    OK(uc_reg_write(uc, UC_CSKY_REG_R1, &address));
    uc_assert_err(UC_ERR_READ_UNMAPPED, uc_emu_start(uc, base, base + 2, 0, 0));
    TEST_CHECK(read32(uc, UC_CSKY_REG_PC) == base);
    OK(uc_close(uc));
}

TEST_LIST = {
    {"csky_models", test_csky_models},
    {"csky_context", test_csky_context},
    {"csky_register_sizes", test_csky_register_sizes},
    {"csky_invalid_modes", test_csky_invalid_modes},
    {"csky_memory_fault", test_csky_memory_fault},
    {NULL, NULL}
};
