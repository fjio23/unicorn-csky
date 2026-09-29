/* Unicorn Emulator Engine */
/* By Nguyen Anh Quynh <aquynh@gmail.com>, 2015 */

#ifndef UC_QEMU_TARGET_CSKY_H
#define UC_QEMU_TARGET_CSKY_H

// functions to read & write registers
uc_err reg_read_csky(void *env, int mode, unsigned int regid, void *value,
                     size_t *size);
uc_err reg_write_csky(void *env, int mode, unsigned int regid,
                      const void *value, size_t *size, int *setpc);

void uc_init_csky(struct uc_struct *uc);
#endif
