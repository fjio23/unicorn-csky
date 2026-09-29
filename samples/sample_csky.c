/* C-SKY V2: execute mixed 16-bit and 32-bit instructions. */
#include <stdio.h>
#include <unicorn/unicorn.h>

int main(void)
{
    uc_engine *uc;
    uc_err err;
    uint32_t r0 = 0, r17 = 0;
    const uint64_t address = 0x1000;
    /* movi16 r0, 7; addi16 r0, 3; movi32 r17, 0x1234 */
    const unsigned char code[] = {0x07, 0x30, 0x02, 0x20, 0x11, 0xea, 0x34, 0x12};

    err = uc_open(UC_ARCH_CSKY, UC_MODE_CSKY_V2, &uc);
    if (err != UC_ERR_OK) {
        fprintf(stderr, "%s\n", uc_strerror(err));
        return 1;
    }
#define CHECK(call) do { err = (call); if (err != UC_ERR_OK) goto out; } while (0)
    CHECK(uc_ctl_set_cpu_model(uc, UC_CPU_CSKY_CK803));
    CHECK(uc_mem_map(uc, address, 0x1000, UC_PROT_ALL));
    CHECK(uc_mem_write(uc, address, code, sizeof(code)));
    CHECK(uc_emu_start(uc, address, address + sizeof(code), 0, 0));
    CHECK(uc_reg_read(uc, UC_CSKY_REG_R0, &r0));
    CHECK(uc_reg_read(uc, UC_CSKY_REG_R17, &r17));
    printf("r0 = %u, r17 = 0x%x\n", r0, r17);
out:
    uc_close(uc);
    if (err != UC_ERR_OK) {
        fprintf(stderr, "%s\n", uc_strerror(err));
        return 1;
    }
    return r0 == 10 && r17 == 0x1234 ? 0 : 1;
}
