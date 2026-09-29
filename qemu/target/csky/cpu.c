/* Unicorn Engine C-SKY CPU integration. SPDX-License-Identifier: LGPL-2.1-or-later */
#include "qemu/osdep.h"
#include "cpu.h"
#include "exec/exec-all.h"
#include "exec/helper-proto.h"
#include "uc_priv.h"

static void csky_set_pc(CPUState *cs, vaddr pc)
{
    CSKY_CPU(cs)->env.pc = pc;
}

static void csky_sync_pc(CPUState *cs, TranslationBlock *tb)
{
    CSKY_CPU(cs)->env.pc = tb->pc;
}

static bool csky_has_work(CPUState *cs)
{
    return true;
}

static void csky_reset(CPUState *cs)
{
    CSKYCPU *cpu = CSKY_CPU(cs);
    CPUCSKYState *env = &cpu->env;
    cpu->cc.parent_reset(cs);
    memset(env, 0, offsetof(CPUCSKYState, end_reset_fields));
    env->sce_condexec_bits = env->sce_condexec_bits_bk = 1;
    env->cp0.cpidr[0] = env->cpuid;
    env->cp0.ccr = 2; /* CK803 extended literal loads. */
    set_float_rounding_mode(float_round_nearest_even, &env->vfp.fp_status);
}

hwaddr csky_cpu_get_phys_page_debug(CPUState *cs, vaddr addr)
{
    return addr;
}

bool csky_cpu_tlb_fill(CPUState *cs, vaddr address, int size,
                      MMUAccessType access_type, int mmu_idx,
                      bool probe, uintptr_t retaddr)
{
    tlb_set_page(cs, address & TARGET_PAGE_MASK, address & TARGET_PAGE_MASK,
                 PAGE_READ | PAGE_WRITE | PAGE_EXEC, mmu_idx, TARGET_PAGE_SIZE);
    return true;
}

void csky_cpu_do_unaligned_access(CPUState *cs, vaddr address,
                                 MMUAccessType access_type, int mmu_idx,
                                 uintptr_t retaddr)
{
    cs->exception_index = EXCP_CSKY_ALIGN;
    cpu_loop_exit_restore(cs, retaddr);
}

void helper_uc_csky_exit(CPUCSKYState *env)
{
    CPUState *cs = env_cpu(env);
    cs->exception_index = EXCP_HLT;
    cs->halted = 1;
    cpu_loop_exit(cs);
}

CSKYCPU *cpu_csky_init(struct uc_struct *uc)
{
    CSKYCPU *cpu;
    CPUState *cs;
    CPUClass *cc;
    if (uc->cpu_model == INT_MAX) {
        uc->cpu_model = UC_CPU_CSKY_CK803;
    }
    if (uc->cpu_model < 0 || uc->cpu_model >= UC_CPU_CSKY_ENDING) {
        return NULL;
    }
    cpu = qemu_memalign(8, sizeof(*cpu));
    if (!cpu) {
        return NULL;
    }
    memset(cpu, 0, sizeof(*cpu));
    cs = CPU(cpu);
    cc = &cpu->cc.parent_class;
    cs->cc = cc;
    cs->uc = uc;
    uc->cpu = cs;
    cpu_class_init(uc, cc);
    cpu->cc.parent_reset = cc->reset;
    cc->reset = csky_reset;
    cc->has_work = csky_has_work;
    cc->set_pc = csky_set_pc;
    cc->synchronize_from_tb = csky_sync_pc;
    cc->get_phys_page_debug = csky_cpu_get_phys_page_debug;
    cc->tlb_fill_cpu = csky_cpu_tlb_fill;
    cc->do_unaligned_access = csky_cpu_do_unaligned_access;
    cc->tcg_initialize = csky_translate_init;
    cpu_common_initfn(uc, cs);
    cpu->env.uc = uc;
    cpu_set_cpustate_pointers(cpu);
    if (uc->cpu_model == UC_CPU_CSKY_CK803) {
        cpu->env.features = CPU_ABIV2 | CPU_E803 | ABIV2_ELRW;
        cpu->env.cpuid = CSKY_CPUID_E804;
    } else {
        cpu->env.features = CPU_ABIV2 | CPU_C810 | ABIV2_FPU;
        cpu->env.cpuid = CSKY_CPUID_C810;
    }
    cpu_exec_realizefn(cs);
    cpu_reset(cs);
    cpu_address_space_init(cs, 0, cs->memory);
    qemu_init_vcpu(cs);
    return cpu;
}
