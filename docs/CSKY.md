# C-SKY V2

The C-SKY backend provides little-endian, 32-bit CPU emulation through the C API
and Python bindings. Select `UC_ARCH_CSKY` with `UC_MODE_CSKY_V2`.

## Models and registers

- `UC_CPU_CSKY_CK803` is the default model.
- `UC_CPU_CSKY_CK810` additionally enables the upstream VFP instruction set.
- Select the model with `uc_ctl_set_cpu_model` / `ctl_set_cpu_model` before
  initializing the engine (for example, before mapping memory).
- `UC_CSKY_REG_R0` through `R31`, `PC`, `PSR`, `HI`, `LO`, `FCR`, and `FESR`
  use `uint32_t` in C. `SP` aliases `R14`; `LR` aliases `R15`.
- `UC_CSKY_REG_F0` through `F15` expose the low 64 bits of each VFP register as
  a `uint64_t` bit pattern. Single precision uses its low 32 bits. Floating-point
  instructions remain unavailable on CK803 even though the register API permits
  inspecting the saved state.
- Reset starts in user mode (`PSR = 0`), with zeroed integer registers and the
  conditional execution state disabled. Initialize SP and any required state
  before running application code.

Both 16-bit and 32-bit instructions are decoded. A 32-bit instruction is stored
as its high halfword followed by its low halfword, each little endian. Do not
encode it by writing a single little-endian `uint32_t`.

## Build and test

From the repository root, using CMake, a C compiler, Make or Ninja, pkg-config,
and Python 3:

```sh
cmake -S . -B build -DUNICORN_ARCH=csky -DUNICORN_BUILD_TESTS=ON
cmake --build build -j4
ctest --test-dir build -R '^test_csky$' --output-on-failure
./build/sample_csky
PYTHONPATH=bindings/python LIBUNICORN_PATH=build \
  python3 bindings/python/tests/test_csky.py -v
```

No C-SKY cross compiler is required for these tests. The common `test_mem` and
`test_ctl` executables assume x86 is enabled; run them using a default, full
architecture build instead of a C-SKY-only build.

The default architecture list includes C-SKY. Tests cover the two CPU models,
mixed instruction widths, integer and CK810 floating-point arithmetic, branches,
PSR carry, load/store byte order, memory faults and permissions, code/block/memory
hooks, PC changes and stopping from a hook, count limits, timeouts, contexts,
invalid-instruction recovery, breakpoints, page boundaries, and concurrent
independent engines. This is integration coverage, not exhaustive ISA validation.

## Python example

```python
from unicorn import Uc, UC_ARCH_CSKY, UC_MODE_CSKY_V2
from unicorn.csky_const import UC_CSKY_REG_R0, UC_CSKY_REG_R17

uc = Uc(UC_ARCH_CSKY, UC_MODE_CSKY_V2)
uc.mem_map(0x1000, 0x1000)
# movi16 r0, 7; addi16 r0, 3; movi32 r17, 0x1234
code = bytes.fromhex('07 30 02 20 11 ea 34 12')
uc.mem_write(0x1000, code)
uc.emu_start(0x1000, 0x1000 + len(code))
assert uc.reg_read(UC_CSKY_REG_R0) == 10
assert uc.reg_read(UC_CSKY_REG_R17) == 0x1234
```

See `samples/sample_csky.c` for the equivalent C program.

## Scope

This backend runs CPU code in Unicorn's mapped address space. Guest addresses
map directly to Unicorn memory; the hardware MMU/MPU, board devices, multicore
release, timers, NVIC, semihosting, and operating-system services are not
implemented. Board-dependent helpers report a guest exception instead of invoking
host or QEMU board services. It is not a bootable full-system C-SKY machine.

V1, big endian, CK860, TEE, VDSP, and FPUv3 model variants are not exposed.
Their upstream decoding/helper code is retained where shared with the V2
translator, but no public CPU model enables those extensions. Only C and Python
API integration has been added and tested; other language bindings need their
own architecture integration before use. Validation was performed on Linux
x86-64; other host platforms have not been tested.

Undefined instructions return `UC_ERR_INSN_INVALID` and support
`UC_HOOK_INSN_INVALID`. Guest traps and breakpoints use `UC_HOOK_INTR` (for
example, breakpoint exception number 7). The PC identifies the faulting
instruction. A handler that resumes execution must update PC or otherwise
resolve the exception, or it will encounter the same instruction again.

## Source provenance

The instruction translator and helpers are adapted from
[XUANTIE-RV/qemu](https://github.com/XUANTIE-RV/qemu), branch
`xuantie-qemu-6.1.0`, commit
`03813c9fe82063d1a03be61b3a82377a0e8bbaa3`. Its TCG interfaces are closer to
Unicorn's than the QEMU 9 default branch. Original copyright and license notices
are preserved in the imported files.

The Unicorn base is commit `7c5db94191defc1e04a4f66f4eb1220903cba837`.
The port replaces global TCG register handles with per-engine state, namespaces
helpers for coexistence with other targets, adds Unicorn execution hooks and
register/context APIs, and removes vendor trace and board dependencies.
