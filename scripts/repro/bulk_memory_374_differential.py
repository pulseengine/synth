#!/usr/bin/env python3
"""#374 — memory.copy / memory.fill (bulk-memory) numeric differential.

synth had no bulk-memory lowering: `memory.copy`/`memory.fill` fell through the
decoder `_ => None` and (since v0.11.46/GI-FPU-001) loud-skipped the whole
function — 19 falcon sites. This adds the WasmOp variants + decoder arms + stack
effect (pop 3, push 0) + a bounds-checked byte-loop lowering in
`select_with_stack` (memmove-direction copy, low-byte fill, end-exclusive OOB
trap matching wasmtime).

This harness is the value-level gate (no silicon needed, like #372): **wasmtime
is ground truth**; **unicorn** runs synth's Thumb-2 output. Compiled with
`--safety-bounds software` so the OOB vectors exercise the inline trap. For each
vector both engines start from the SAME deterministic memory pattern; we compare
the FULL 64 KiB image AND the trap/no-trap outcome.

The vectors are chosen to DISCRIMINATE the likely lowering bugs (not just "a copy
happened"):
  - copy non-overlap dst<src, distinct values   -> catches a pop-order swap
  - copy overlap dst>src                          -> forces backward copy
  - copy overlap dst<src                          -> forward correct
  - copy dst==src                                 -> self copy (no-op)
  - len==0 at dst==size                           -> no-op, must NOT trap
  - dst+len==size / src+len==size (boundary)      -> must NOT trap (end-exclusive)
  - dst+len>size / src+len>size                   -> must TRAP
  - fill val with high bits set                   -> only low byte written (STRB)

Run:
  synth compile scripts/repro/bulk_memory_374_diff.wat -o /tmp/bmd.elf \
        --target cortex-m7dp --all-exports --safety-bounds software
  /tmp/n374venv/bin/python scripts/repro/bulk_memory_374_differential.py /tmp/bmd.elf
Exits nonzero on any mismatch.
"""
import subprocess
import os
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import (
    UC_ARCH_ARM,
    UC_ERR_INSN_INVALID,
    UC_HOOK_CODE,
    UC_MODE_THUMB,
    Uc,
    UcError,
)
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WASM = "scripts/repro/bulk_memory_374_diff.wat"
ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/bmd.elf"
SYNTH = os.environ.get("SYNTH", "./target/release/synth")

MEM_BYTES = 0x10000  # 1 page = 64 KiB (matches the wat `(memory 1)`)
CODE, LIN, STK, RET = 0x200000, 0x400000, 0x90000, 0x300000


def pattern():
    return bytes((i * 31 + 7) & 0xFF for i in range(MEM_BYTES))


# (fn, dst, b/src, len, expect_trap)
VECTORS = [
    # ---- memory.copy ----
    ("cpy", 100, 200, 16, False),     # non-overlap dst<src (asymmetric distinct)
    ("cpy", 1000, 1004, 16, False),   # overlap dst<src -> forward
    ("cpy", 2004, 2000, 16, False),   # overlap dst>src -> backward (the landmine)
    ("cpy", 4000, 4000, 32, False),   # dst==src self copy
    ("cpy", 500, 800, 0, False),      # len 0 no-op
    ("cpy", MEM_BYTES, 0, 0, False),  # len 0 at dst==size, must NOT trap
    ("cpy", MEM_BYTES - 16, 0, 16, False),  # dst+len==size boundary, no trap
    ("cpy", 0, MEM_BYTES - 16, 16, False),  # src+len==size boundary, no trap
    ("cpy", MEM_BYTES - 10, 0, 16, True),   # dst+len>size -> trap
    ("cpy", 0, MEM_BYTES - 10, 16, True),   # src+len>size -> trap
    # ---- memory.fill ----
    ("fil", 300, 0xAB, 20, False),         # normal
    ("fil", 5000, 0x12345678, 10, False),  # high bits set -> only low byte 0x78
    ("fil", 700, 0x00, 0, False),          # len 0 no-op
    ("fil", MEM_BYTES, 0xAB, 0, False),    # len 0 at dst==size, must NOT trap
    ("fil", MEM_BYTES - 16, 0xFF, 16, False),  # boundary, no trap
    ("fil", MEM_BYTES - 10, 0xFF, 16, True),   # OOB -> trap
]


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(_wasm_bytes_path(), "rb").read())

    def wasmtime_run(fn, a, b, c):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        mem = inst.exports(store)["memory"]
        mem.write(store, pattern(), 0)
        try:
            inst.exports(store)[fn](store, a, b, c)
            trapped = False
        except wasmtime.Trap:
            trapped = True
        img = bytes(mem.read(store, 0, MEM_BYTES))
        return trapped, img

    # Read symbol offsets from the ELF SYMBOL TABLE (host-independent), NOT by
    # parsing `synth disasm` TEXT — disasm formatting is host-dependent and the
    # regex matched nothing on the Linux CI runner (#850). synth emits the symtab
    # as an UNNAMED SHT_SYMTAB section (get_section_by_name(".symtab") is None), so
    # iterate by TYPE. ARM Thumb symbols carry the Thumb bit (bit 0); mask `& ~1`
    # so the map equals the clean disasm addresses. This is load-bearing for
    # trap_addr too: the hook compares the EVEN executing PC, so an unmasked
    # (odd) trap_addr would never match and silently defeat trap detection.
    ef = ELFFile(open(ELF, "rb"))
    text_idx = ef.get_section_index(".text")
    syms = {s.name: s["st_value"] & ~1 for sec in ef.iter_sections()
            if sec.header.sh_type == "SHT_SYMTAB"
            for s in sec.iter_symbols()
            if s.name and s["st_shndx"] == text_idx}
    trap_sym = syms["Trap_Handler"]
    text = ef.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    trap_addr = CODE + trap_sym - base

    def unicorn_run(fn, a, b, c):
        fa = syms[fn]
        mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        mu.mem_map(CODE, 0x10000)
        mu.mem_map(LIN, MEM_BYTES)        # exactly 1 page: any OOB write faults
        mu.mem_map(STK - 0x8000, 0x10000)
        mu.mem_map(RET, 0x1000)
        mu.mem_write(CODE, code)
        mu.mem_write(LIN, pattern())
        mu.reg_write(UC_ARM_REG_SP, STK)
        mu.reg_write(UC_ARM_REG_R11, LIN)        # linear-memory base
        mu.reg_write(UC_ARM_REG_R10, MEM_BYTES)  # memory size (bytes) for bounds
        mu.reg_write(UC_ARM_REG_R0, a & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_R1, b & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_R2, c & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_LR, RET | 1)
        trapped = [False]

        def hook(uc, address, size, ud):
            if address == trap_addr:
                trapped[0] = True
                uc.emu_stop()
        mu.hook_add(UC_HOOK_CODE, hook)
        try:
            mu.emu_start((CODE + fa - base) | 1, RET, count=200000)
        except UcError as e:
            # The inline bounds trap is a `UDF` -> UC_ERR_INSN_INVALID: that IS
            # the wasm trap (on silicon UsageFault/HardFault routes to
            # Trap_Handler). Any OTHER fault (e.g. READ/WRITE_UNMAPPED) means a
            # bounds bug let an out-of-bounds access through — report as ERR so it
            # never silently counts as a match.
            if e.errno == UC_ERR_INSN_INVALID:
                return True, bytes(mu.mem_read(LIN, MEM_BYTES))
            return f"ERR:{e}", b""
        img = bytes(mu.mem_read(LIN, MEM_BYTES))
        return trapped[0], img

    fails = 0
    for (fn, a, b, c, exp_trap) in VECTORS:
        gt_trap, gt_img = wasmtime_run(fn, a, b, c)
        sy_trap, sy_img = unicorn_run(fn, a, b, c)
        assert gt_trap == exp_trap, f"vector expectation wrong for {fn}({a},{b},{c})"
        if isinstance(sy_trap, str):  # ERR
            ok = False
            detail = sy_trap
        elif gt_trap:
            # Both must trap; on trap wasm leaves memory unchanged (bounds checked
            # up front), and so does synth (bounds before the loop).
            ok = sy_trap and sy_img == gt_img
            detail = f"trap synth={sy_trap} wasmtime={gt_trap}"
        else:
            ok = (not sy_trap) and sy_img == gt_img
            if sy_img != gt_img:
                diff = next((i for i in range(MEM_BYTES) if sy_img[i] != gt_img[i]), -1)
                detail = (f"mem differs @{diff}: synth=0x{sy_img[diff]:02x} "
                          f"wasmtime=0x{gt_img[diff]:02x}")
            else:
                detail = "image identical"
        fails += 0 if ok else 1
        print(f"{fn}(dst={a},{'src' if fn=='cpy' else 'val'}={b},len={c}) "
              f"trap={exp_trap}: {'OK' if ok else 'MISMATCH'}  [{detail}]")
    print(f"\n{len(VECTORS) - fails}/{len(VECTORS)} match")
    print("ORACLE: PASS" if fails == 0 else f"ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


def _wasm_bytes_path():
    # wat2wasm the harness module once.
    out = "/tmp/bmd.wasm"
    subprocess.run(["wat2wasm", WASM, "-o", out], check=True)
    return out


if __name__ == "__main__":
    main()
