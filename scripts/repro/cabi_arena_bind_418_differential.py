#!/usr/bin/env python3
"""#418 — self-contained binding of `env::__cabi_arena_realloc` (the meld
dissolve gap): EXECUTION differential vs wasmtime.

The wit-bindgen `cabi-realloc-extern` shape imports the canonical-ABI arena
allocator from the embedder. The `--relocatable` seam is locked (#420: an
UNDEFINED `__cabi_arena_realloc` symbol the TCB link satisfies) — but a
SELF-CONTAINED dissolve (default compile, no host linker) previously degraded
to an ET_REL "link me with the Kiln bridge" object: the arena import was the
one unresolved seam blocking a fully self-contained image.

This gate asserts the bound behavior end to end:
  1. the default self-contained compile of the fixture produces ET_EXEC (an
     executable image, not a link-me object) — RED before the #418 binding;
  2. every export EXECUTES under unicorn (image's own startup runs first:
     R9/R10/R11 init, globals table, #758 data copy) and matches wasmtime
     ground truth, where the import is satisfied by a HOST arena allocator
     implementing the #418 contract (old_len==0 && new_len==0 -> align;
     bump allocation; realloc preserves min(old,new) bytes; bounded, traps
     on exhaustion — never memory.grow);
  3. the host arena deliberately uses a DIFFERENT base than synth's, so only
     pointer-INDEPENDENT semantics can pass (no base-coincidence green);
  4. the exhaustion case must TRAP on BOTH sides.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/cabi_arena_bind_418_differential.py
Exits nonzero on any mismatch.
"""

import os
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("cabi_arena_bind.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")

# (export, args, traps) — every observable is pointer-independent.
CASES = [
    ("case_zero", (8,), False),
    ("case_zero", (1,), False),
    ("grow_preserves", (), False),
    ("disjoint", (), False),
    ("align_ok", (16,), False),
    ("exhaust", (), True),
]

SENTINELS = (0xDEADBEEF, 0xCAFEF00D, 0x5A5A5A5A, 0xA0A0A0A0)

FLASH_BASE = 0x0000_0000
FLASH_SIZE = 0x40000
RET_STUB = 0x3F000  # inside the flash map, far above the image
RAM_BASE = 0x2000_0000
RAM_SIZE = 0x20_0000

# Host arena base — deliberately NOT synth's derived base (6144), so equal
# results can only come from contract-conformant semantics, never from both
# sides picking the same addresses.
HOST_ARENA_BASE = 0x8000


def compile_self_contained(out):
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
         "--target", "cortex-m3", "--all-exports"],
        capture_output=True, text=True,
    )
    if r.returncode != 0:
        sys.exit(f"compile failed: {r.stderr}")
    return r.stderr


def load_image(elf_path):
    f = ELFFile(open(elf_path, "rb"))
    if f.header.e_type != "ET_EXEC":
        sys.exit(
            f"RED (#418): expected a self-contained ET_EXEC image, got "
            f"{f.header.e_type} — the arena import still degrades the "
            f"dissolve to a link-me object"
        )
    blobs = []  # (addr, bytes)
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"]
        if s.header.sh_flags & 0x2 and s.header.sh_type == "SHT_PROGBITS":
            blobs.append((s["sh_addr"], s.data()))
    if not blobs:
        sys.exit("no allocatable PROGBITS sections found")
    return blobs, syms


# ---------------------------------------------------------------- wasmtime
def host_arena_instance():
    """Instantiate the ORIGINAL module with a host arena implementing the
    #418 contract over the instance's own linear memory."""
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    store = wasmtime.Store(eng)
    state = {"cur": HOST_ARENA_BASE}

    def realloc(caller, old_ptr, old_len, align, new_len):
        mem = caller.get("memory")
        # contract: old_len == 0 && new_len == 0 -> return align
        if old_len == 0 and new_len == 0:
            return align
        if align <= 0 or (align & (align - 1)):
            raise wasmtime.Trap("bad align")
        size = mem.data_len(caller)
        aligned = (state["cur"] + align - 1) & ~(align - 1)
        end = aligned + new_len
        if end > size:
            # bounded arena: trap on exhaustion, never memory.grow
            raise wasmtime.Trap("arena exhausted")
        state["cur"] = end
        n = min(old_len, new_len)
        if n:
            mem.write(caller, bytes(mem.read(caller, old_ptr, old_ptr + n)),
                      aligned)
        return aligned

    ty = wasmtime.FuncType([wasmtime.ValType.i32()] * 4,
                           [wasmtime.ValType.i32()])
    func = wasmtime.Func(store, ty, realloc, access_caller=True)
    inst = wasmtime.Instance(store, mod, [func])
    return store, inst


def wasm_result(func, args):
    store, inst = host_arena_instance()  # fresh arena per case
    f = inst.exports(store)[func]
    try:
        return f(store, *args) & 0xFFFFFFFF, False
    except (wasmtime.WasmtimeError, wasmtime.Trap):
        return None, True


# ----------------------------------------------------------------- unicorn
def fresh_machine(blobs, syms):
    """Map the image and run its OWN startup (reset vector -> stop at the
    first laid-out function): R10/R11/R9 init, R9 globals-table
    materialization (the arena cursor global!), #758 data ROM->RAM copy."""
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(FLASH_BASE, FLASH_SIZE)
    mu.mem_map(RAM_BASE, RAM_SIZE)
    for addr, data in blobs:
        mu.mem_write(addr, bytes(data))
    mu.mem_write(RET_STUB, b"\x00\xbf\x00\xbf")  # nop; nop
    image = blobs[0][1]
    sp_init = int.from_bytes(image[0:4], "little")
    reset = int.from_bytes(image[4:8], "little")
    # First COMPILED function (the startup's final jump target) — exclude the
    # image-infrastructure symbols, or `min` lands on Reset_Handler and the
    # startup never executes (a vacuous machine: R9/R10/R11 all zero).
    infra = {"Reset_Handler", "Default_Handler", "Trap_Handler",
             "__linear_memory_base"}
    first_func = min(v for k, v in syms.items() if k not in infra) & ~1
    mu.reg_write(UC_ARM_REG_SP, sp_init)
    mu.emu_start(reset, first_func, timeout=5_000_000)
    if mu.reg_read(UC_ARM_REG_PC) & ~1 != first_func:
        sys.exit(
            f"startup did not reach the first function "
            f"(pc={mu.reg_read(UC_ARM_REG_PC):#x}, want {first_func:#x})"
        )
    # Anti-vacuity: the startup must have established the linmem base in R11.
    r11 = mu.reg_read(UC_ARM_REG_R11)
    if r11 != syms["__linear_memory_base"]:
        sys.exit(f"startup left R11={r11:#x}, want __linear_memory_base")
    return mu, sp_init


def arm_result(blobs, syms, func, args):
    mu, sp_init = fresh_machine(blobs, syms)  # fresh arena per case
    regs = (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)
    for reg, sent in zip(regs, SENTINELS):
        mu.reg_write(reg, sent)  # anti-vacuity: caller residue
    for reg, val in zip(regs, args):
        mu.reg_write(reg, val)
    mu.reg_write(UC_ARM_REG_SP, sp_init)
    mu.reg_write(UC_ARM_REG_LR, RET_STUB | 1)
    try:
        mu.emu_start((syms[func] & ~1) | 1, RET_STUB, timeout=5_000_000)
    except UcError:
        return None, True  # UDF -> invalid-instruction exception = trap
    if mu.reg_read(UC_ARM_REG_PC) & ~1 != RET_STUB:
        return None, True  # stopped elsewhere (fault-shaped)
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF, False


def main():
    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")
    elf = "/tmp/cabi_arena_bind_418.elf"
    compile_self_contained(elf)
    blobs, syms = load_image(elf)

    fails = 0
    for func, args, want_trap in CASES:
        gt, gt_trap = wasm_result(func, args)
        got, got_trap = arm_result(blobs, syms, func, args)
        if want_trap:
            ok = gt_trap and got_trap
            show = f"trap(wasmtime)={gt_trap} trap(arm)={got_trap}"
        else:
            ok = (not gt_trap) and (not got_trap) and got == gt
            show = (
                f"= {got if got is None else hex(got)}  "
                f"(wasmtime: {gt if gt is None else hex(gt)})"
            )
        if not ok:
            fails += 1
        print(f"{'OK  ' if ok else 'FAIL'} {func}{args} {show}")

    print("ORACLE:", "PASS" if fails == 0 else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
