/* Unicorn Engine: C-SKY V2 API. */
#ifndef UNICORN_CSKY_H
#define UNICORN_CSKY_H
#ifdef __cplusplus
extern "C" {
#endif

typedef enum uc_cpu_csky {
    UC_CPU_CSKY_CK803 = 0,
    UC_CPU_CSKY_CK810,
    UC_CPU_CSKY_ENDING
} uc_cpu_csky;

/* Integer/control registers are uint32_t. F0-F15 are uint64_t raw bits. */
typedef enum uc_csky_reg {
    UC_CSKY_REG_INVALID = 0,
    UC_CSKY_REG_R0,
    UC_CSKY_REG_R1,
    UC_CSKY_REG_R2,
    UC_CSKY_REG_R3,
    UC_CSKY_REG_R4,
    UC_CSKY_REG_R5,
    UC_CSKY_REG_R6,
    UC_CSKY_REG_R7,
    UC_CSKY_REG_R8,
    UC_CSKY_REG_R9,
    UC_CSKY_REG_R10,
    UC_CSKY_REG_R11,
    UC_CSKY_REG_R12,
    UC_CSKY_REG_R13,
    UC_CSKY_REG_R14,
    UC_CSKY_REG_R15,
    UC_CSKY_REG_R16,
    UC_CSKY_REG_R17,
    UC_CSKY_REG_R18,
    UC_CSKY_REG_R19,
    UC_CSKY_REG_R20,
    UC_CSKY_REG_R21,
    UC_CSKY_REG_R22,
    UC_CSKY_REG_R23,
    UC_CSKY_REG_R24,
    UC_CSKY_REG_R25,
    UC_CSKY_REG_R26,
    UC_CSKY_REG_R27,
    UC_CSKY_REG_R28,
    UC_CSKY_REG_R29,
    UC_CSKY_REG_R30,
    UC_CSKY_REG_R31,
    UC_CSKY_REG_PC,
    UC_CSKY_REG_PSR,
    UC_CSKY_REG_HI,
    UC_CSKY_REG_LO,
    UC_CSKY_REG_F0,
    UC_CSKY_REG_F1,
    UC_CSKY_REG_F2,
    UC_CSKY_REG_F3,
    UC_CSKY_REG_F4,
    UC_CSKY_REG_F5,
    UC_CSKY_REG_F6,
    UC_CSKY_REG_F7,
    UC_CSKY_REG_F8,
    UC_CSKY_REG_F9,
    UC_CSKY_REG_F10,
    UC_CSKY_REG_F11,
    UC_CSKY_REG_F12,
    UC_CSKY_REG_F13,
    UC_CSKY_REG_F14,
    UC_CSKY_REG_F15,
    UC_CSKY_REG_FCR,
    UC_CSKY_REG_FESR,
    UC_CSKY_REG_ENDING,
    UC_CSKY_REG_SP = UC_CSKY_REG_R14,
    UC_CSKY_REG_LR = UC_CSKY_REG_R15
} uc_csky_reg;
#ifdef __cplusplus
}
#endif
#endif
