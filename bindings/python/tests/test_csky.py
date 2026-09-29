"""C-SKY V2 integration tests (no cross assembler required)."""
import unittest
from concurrent.futures import ThreadPoolExecutor

from unicorn import Uc, UcError, UC_ARCH_CSKY, UC_MODE_CSKY_V2, UC_MODE_BIG_ENDIAN
from unicorn import UC_HOOK_CODE, UC_HOOK_BLOCK, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE
from unicorn import UC_HOOK_INSN_INVALID, UC_HOOK_INTR
from unicorn import UC_ERR_MODE, UC_ERR_INSN_INVALID, UC_ERR_READ_UNMAPPED
from unicorn import UC_ERR_WRITE_PROT, UC_ERR_FETCH_UNMAPPED, UC_PROT_READ
from unicorn.csky_const import *

BASE = 0x1000
# movi16 r0, 7; addi16 r0, 3; movi32 r17, 0x1234
MIXED = bytes.fromhex('0730 0220 11ea 3412')


def engine(code=MIXED, model=UC_CPU_CSKY_CK803, address=BASE):
    uc = Uc(UC_ARCH_CSKY, UC_MODE_CSKY_V2)
    uc.ctl_set_cpu_model(model)
    uc.mem_map(BASE, 0x3000)
    uc.mem_write(address, code)
    return uc


class TestCsky(unittest.TestCase):
    def test_models_and_mixed_width(self):
        for model in (UC_CPU_CSKY_CK803, UC_CPU_CSKY_CK810):
            with self.subTest(model=model):
                uc = engine(model=model)
                uc.emu_start(BASE, BASE + len(MIXED))
                self.assertEqual(uc.reg_read(UC_CSKY_REG_R0), 10)
                self.assertEqual(uc.reg_read(UC_CSKY_REG_R17), 0x1234)
                self.assertEqual(uc.reg_read(UC_CSKY_REG_PC), BASE + len(MIXED))

    def test_fpu_ck810(self):
        import struct
        # faddd vr2, vr0, vr1 (0xf4200802)
        uc = engine(bytes.fromhex('20f4 0208'), model=UC_CPU_CSKY_CK810)
        bits = lambda x: struct.unpack('<Q', struct.pack('<d', x))[0]
        uc.reg_write(UC_CSKY_REG_F0, bits(1.5))
        uc.reg_write(UC_CSKY_REG_F1, bits(2.25))
        uc.emu_start(BASE, BASE + 4)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_F2), bits(3.75))
        context = uc.context_save()
        uc.reg_write(UC_CSKY_REG_F2, 0)
        uc.context_restore(context)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_F2), bits(3.75))
        uc = engine(bytes.fromhex('20f4 0208'))
        with self.assertRaises(UcError) as caught:
            uc.emu_start(BASE, BASE + 4)
        self.assertEqual(caught.exception.errno, UC_ERR_INSN_INVALID)

    def test_count_and_resume(self):
        uc = engine()
        uc.emu_start(BASE, BASE + len(MIXED), count=1)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_R0), 7)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_PC), BASE + 2)
        uc.emu_start(BASE + 2, BASE + len(MIXED))
        self.assertEqual(uc.reg_read(UC_CSKY_REG_R0), 10)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_R17), 0x1234)

    def test_code_and_block_hooks(self):
        uc = engine()
        instructions, blocks = [], []
        uc.hook_add(UC_HOOK_CODE, lambda u, a, s, _: instructions.append((a, s, u.reg_read(UC_CSKY_REG_PC))))
        uc.hook_add(UC_HOOK_BLOCK, lambda u, a, s, _: blocks.append(a))
        uc.emu_start(BASE, BASE + len(MIXED))
        self.assertEqual(instructions, [(BASE, 2, BASE), (BASE + 2, 2, BASE + 2), (BASE + 4, 4, BASE + 4)])
        self.assertEqual(blocks[0], BASE)

    def test_stop_from_hook(self):
        uc = engine()
        uc.hook_add(UC_HOOK_CODE, lambda u, a, s, _: u.emu_stop(), begin=BASE + 2, end=BASE + 2)
        uc.emu_start(BASE, BASE + len(MIXED))
        self.assertEqual(uc.reg_read(UC_CSKY_REG_R0), 7)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_PC), BASE + 2)

    def test_pc_write_from_hook(self):
        uc = engine()
        uc.hook_add(UC_HOOK_CODE, lambda u, a, s, _: u.reg_write(UC_CSKY_REG_PC, BASE + 4), begin=BASE, end=BASE)
        uc.emu_start(BASE, BASE + len(MIXED))
        self.assertEqual(uc.reg_read(UC_CSKY_REG_R0), 0)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_R17), 0x1234)

    def test_memory_and_hooks(self):
        # st.w16 r0, (r1, 0); ld.w16 r2, (r1, 0)
        uc = engine(bytes.fromhex('00b1 4091'))
        uc.reg_write(UC_CSKY_REG_R0, 0x12345678)
        uc.reg_write(UC_CSKY_REG_R1, 0x3000)
        accesses = []
        uc.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE,
                    lambda u, t, a, s, v, _: accesses.append((a, s)))
        uc.emu_start(BASE, BASE + 4)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_R2), 0x12345678)
        self.assertEqual(uc.mem_read(0x3000, 4), bytes.fromhex('78563412'))
        self.assertEqual(accesses, [(0x3000, 4), (0x3000, 4)])

    def test_memory_errors(self):
        uc = engine(bytes.fromhex('4091'))
        uc.reg_write(UC_CSKY_REG_R1, 0x9000)
        with self.assertRaises(UcError) as caught:
            uc.emu_start(BASE, BASE + 2)
        self.assertEqual(caught.exception.errno, UC_ERR_READ_UNMAPPED)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_PC), BASE)
        uc = engine(bytes.fromhex('00b1'))
        uc.reg_write(UC_CSKY_REG_R1, 0x3000)
        uc.mem_protect(0x3000, 0x1000, UC_PROT_READ)
        with self.assertRaises(UcError) as caught:
            uc.emu_start(BASE, BASE + 2)
        self.assertEqual(caught.exception.errno, UC_ERR_WRITE_PROT)

    def test_branch(self):
        # br16 .+4; movi16 r0, 7; movi16 r0, 9
        uc = engine(bytes.fromhex('0204 0730 0930'))
        uc.emu_start(BASE, BASE + 6)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_R0), 9)

    def test_psr_condition(self):
        # bt16 .+4; movi16 r0, 7; movi16 r1, 9
        for carry in (0, 1):
            uc = engine(bytes.fromhex('0208 0730 0931'))
            uc.reg_write(UC_CSKY_REG_PSR, carry)
            uc.emu_start(BASE, BASE + 6)
            self.assertEqual(uc.reg_read(UC_CSKY_REG_R0), 0 if carry else 7)
            self.assertEqual(uc.reg_read(UC_CSKY_REG_PSR) & 1, carry)

    def test_context_and_aliases(self):
        uc = engine()
        uc.reg_write(UC_CSKY_REG_SP, 0x3000)
        uc.reg_write(UC_CSKY_REG_LR, 0x1234)
        uc.reg_write(UC_CSKY_REG_PSR, 1)
        uc.emu_start(BASE, BASE + 2)
        context = uc.context_save()
        uc.emu_start(BASE + 2, BASE + len(MIXED))
        uc.context_restore(context)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_R0), 7)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_PC), BASE + 2)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_R14), 0x3000)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_R15), 0x1234)
        self.assertEqual(context.reg_read(UC_CSKY_REG_PSR), 1)
        context.reg_write(UC_CSKY_REG_R31, 42)
        uc.context_restore(context)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_R31), 42)

    def test_invalid_and_recovery(self):
        uc = engine(bytes.fromhex('ffff ffff 0730'))
        with self.assertRaises(UcError) as caught:
            uc.emu_start(BASE, BASE + 6)
        self.assertEqual(caught.exception.errno, UC_ERR_INSN_INVALID)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_PC), BASE)
        def invalid(u, _):
            u.reg_write(UC_CSKY_REG_PC, BASE + 4)
            return True
        uc.hook_add(UC_HOOK_INSN_INVALID, invalid)
        uc.emu_start(BASE, BASE + 6)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_R0), 7)

    def test_breakpoint_interrupt(self):
        uc = engine(bytes.fromhex('0000 0730'))
        interrupts = []
        def intr(u, n, _):
            interrupts.append(n)
            u.reg_write(UC_CSKY_REG_PC, BASE + 2)
        uc.hook_add(UC_HOOK_INTR, intr)
        uc.emu_start(BASE, BASE + 4)
        self.assertEqual(interrupts, [7])
        self.assertEqual(uc.reg_read(UC_CSKY_REG_R0), 7)

    def test_cross_page_instruction(self):
        uc = engine(MIXED[4:], address=0x1ffe)
        uc.emu_start(0x1ffe, 0x2002)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_R17), 0x1234)
        uc = engine(bytes.fromhex('0730'), address=0x3ffe)
        uc.emu_start(0x3ffe, 0x4000)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_R0), 7)
        with self.assertRaises(UcError) as caught:
            uc.emu_start(0x4000, 0x4002)
        self.assertEqual(caught.exception.errno, UC_ERR_FETCH_UNMAPPED)

    def test_timeout(self):
        uc = engine(bytes.fromhex('0004'))  # br16 .
        uc.emu_start(BASE, BASE + 2, timeout=10000)
        self.assertEqual(uc.reg_read(UC_CSKY_REG_PC), BASE)

    def test_instances(self):
        def run(value):
            uc = engine(bytes((value, 0x30, 0x02, 0x20)))
            uc.emu_start(BASE, BASE + 4)
            return uc.reg_read(UC_CSKY_REG_R0)
        with ThreadPoolExecutor(max_workers=4) as pool:
            self.assertEqual(list(pool.map(run, range(16))), list(range(3, 19)))

    def test_reject_big_endian(self):
        with self.assertRaises(UcError) as caught:
            Uc(UC_ARCH_CSKY, UC_MODE_CSKY_V2 | UC_MODE_BIG_ENDIAN)
        self.assertEqual(caught.exception.errno, UC_ERR_MODE)


if __name__ == '__main__':
    unittest.main()
