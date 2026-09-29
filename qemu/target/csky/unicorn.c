/* Unicorn Engine C-SKY backend. SPDX-License-Identifier: LGPL-2.1-or-later */
#include "qemu/osdep.h"
#include "cpu.h"
#include "translate.h"
#include "exec/helper-proto.h"
#include "unicorn_common.h"
#include "uc_priv.h"

static void csky_set_pc(struct uc_struct *uc, uint64_t address)
{
    ((CPUCSKYState *)uc->cpu->env_ptr)->pc = address;
}

static uint64_t csky_get_pc(struct uc_struct *uc)
{
    return ((CPUCSKYState *)uc->cpu->env_ptr)->pc;
}

static void csky_release(void *ctx)
{
    TCGContext *tcg_ctx = ctx;
    CSKYCPU *cpu = CSKY_CPU(tcg_ctx->uc->cpu);
    int i;
    release_common(ctx);
    for (i = 0; i < NB_MMU_MODES; i++) {
        g_free(cpu->neg.tlb.d[i].iotlb);
        g_free(cpu->neg.tlb.f[i].table);
    }
}

static uint32_t *csky_reg(CPUCSKYState *env, unsigned regid)
{
    if (regid >= UC_CSKY_REG_R0 && regid <= UC_CSKY_REG_R31) {
        return &env->regs[regid - UC_CSKY_REG_R0];
    }
    switch (regid) {
    case UC_CSKY_REG_PC: return &env->pc;
    case UC_CSKY_REG_PSR: return &env->cp0.psr;
    case UC_CSKY_REG_HI: return &env->hi;
    case UC_CSKY_REG_LO: return &env->lo;
    case UC_CSKY_REG_FCR: return &env->vfp.fcr;
    case UC_CSKY_REG_FESR: return &env->vfp.fesr;
    default: return NULL;
    }
}

DEFAULT_VISIBILITY
uc_err reg_read(void *_env, int mode, unsigned int regid, void *value, size_t *size)
{
    CPUCSKYState *env = _env;
    uint32_t *reg = csky_reg(env, regid);
    uc_err ret = UC_ERR_ARG;
    if (regid >= UC_CSKY_REG_F0 && regid <= UC_CSKY_REG_F15) {
        CHECK_REG_TYPE(uint64_t);
        *(uint64_t *)value = env->vfp.reg[regid - UC_CSKY_REG_F0].fpu[0];
    } else if (reg) {
        CHECK_REG_TYPE(uint32_t);
        if (regid == UC_CSKY_REG_PSR) {
            helper_update_psr(env);
        }
        *(uint32_t *)value = *reg;
    }
    return ret;
}

DEFAULT_VISIBILITY
uc_err reg_write(void *_env, int mode, unsigned int regid, const void *value,
                 size_t *size, int *setpc)
{
    CPUCSKYState *env = _env;
    uint32_t *reg = csky_reg(env, regid);
    uc_err ret = UC_ERR_ARG;
    if (regid >= UC_CSKY_REG_F0 && regid <= UC_CSKY_REG_F15) {
        CHECK_REG_TYPE(uint64_t);
        env->vfp.reg[regid - UC_CSKY_REG_F0].fpu[0] = *(const uint64_t *)value;
    } else if (reg) {
        CHECK_REG_TYPE(uint32_t);
        *reg = *(const uint32_t *)value;
        if (regid == UC_CSKY_REG_PSR) {
            helper_record_psr_bits(env);
        } else if (regid == UC_CSKY_REG_FCR) {
            helper_vfp_update_fcr(env);
        } else if (regid == UC_CSKY_REG_PC) {
            *setpc = 1;
        }
    }
    return ret;
}

static bool csky_stop_interrupt(struct uc_struct *uc, int intno)
{
    return intno == EXCP_CSKY_UDEF;
}

static int csky_cpus_init(struct uc_struct *uc, const char *model)
{
    return cpu_csky_init(uc) ? 0 : -1;
}

DEFAULT_VISIBILITY
void uc_init(struct uc_struct *uc)
{
    uc->release = csky_release;
    uc->reg_read = reg_read;
    uc->reg_write = reg_write;
    uc->set_pc = csky_set_pc;
    uc->get_pc = csky_get_pc;
    uc->cpus_init = csky_cpus_init;
    uc->stop_interrupt = csky_stop_interrupt;
    uc->cpu_context_size = offsetof(CPUCSKYState, end_reset_fields);
    uc_common_init(uc);
}
