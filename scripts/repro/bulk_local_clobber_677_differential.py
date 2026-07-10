#!/usr/bin/env python3
"""#677 — bulk-memory operand-register clobber differential (thumb-2).

The #374 memory.copy/memory.fill lowering mutated its popped operand registers
in place (dst/src as walking loop pointers, len as the byte buffer). A popped
register is NOT always a dead temp: `local.get` of a register-homed local
(AAPCS param r0-r3, promoted local r4-r8) pushes the HOME register itself, so
a local reused AFTER the op read a wild `mem_base + <loop cursor>` pointer (for
a dest/src) or the last byte copied (for a len). Const operands were unaffected.
The fix copies any still-live popped operand into a scratch register before the
loop mutates it (#193 reservation discipline, `bulk_mutable_operand`).

**wasmtime is ground truth**; **unicorn** runs synth's Thumb-2 output. All
vectors are in-bounds — this gate is about the RETURN VALUE (the reused local)
and the memory image, not traps. Symbols are read from the ELF symtab
(pyelftools), not `synth disasm` text (host-dependent — see PR #489).

Run:
  SYNTH=./target/release/synth python scripts/repro/bulk_local_clobber_677_differential.py
Exits nonzero on any mismatch. RED on pre-fix main, GREEN post-#677.
"""

import os
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_ERR_INSN_INVALID, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("bulk_local_clobber_677.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")

MEM_BYTES = 0x10000  # 1 page = 64 KiB (matches the wat `(memory 1)`)
CODE, LIN, STK, RET = 0x200000, 0x400000, 0x90000, 0x300000

# (fn, arg0, arg1) — arg0 = the local under test (dst/src), arg1 = len.
VECTORS = [
    ("cpy_dst", 32, 4),      # dst local read back: expect 67305985
    ("cpy_dst", 4096, 8),    # different dst, len
    ("fil_dst", 32, 4),      # fill dst local read back: expect 66
    ("fil_dst", 100, 1),
    ("cpy_len", 0, 4),       # len local reused: expect 4
    ("cpy_len", 0, 0),       # len 0: no-op copy, local must still read 0
    ("cpy_src", 16, 4),      # src local reused: expect 16
    ("cpy_const", 0, 4),     # control (const dest): green pre-fix too
]


def load_text_and_syms(elf_path):
    with open(elf_path, "rb") as f:
        ef = ELFFile(f)
        text = ef.get_section_by_name(".text")
        code, base = text.data(), text["sh_addr"]
        syms = {}
        # synth emits .symtab as an unnamed SHT_SYMTAB section, so match by
        # TYPE not name (#489 pattern — get_section_by_name returns None here).
        for sec in ef.iter_sections():
            if sec.header.sh_type == "SHT_SYMTAB":
                for s in sec.iter_symbols():
                    if s.name:
                        syms[s.name] = s["st_value"]
    if not syms:
        # Self-contained images carry no symtab — fall back to `synth disasm`
        # labels (same-arch decode, the established #374-harness pattern).
        import re
        dis = subprocess.run([SYNTH, "disasm", elf_path],
                             capture_output=True, text=True).stdout
        syms = {m.group(2): int(m.group(1), 16)
                for m in re.finditer(r"^([0-9a-f]{8}) <(\w+)>:", dis, re.M)}
    return code, base, syms


def main():
    elf = tempfile.NamedTemporaryFile(suffix=".elf", delete=False).name
    subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", elf, "--target", "cortex-m4",
         "--all-exports", "--safety-bounds", "software"],
        check=True,
    )
    code, base, syms = load_text_and_syms(elf)

    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())

    def wasmtime_run(fn, a, b):
        store = wasmtime.Store(eng)
        inst = wasmtime.Instance(store, mod, [])
        ret = inst.exports(store)[fn](store, a, b)
        mem = inst.exports(store)["memory"]
        img = bytes(mem.read(store, 0, MEM_BYTES))
        return ret & 0xFFFFFFFF, img

    def unicorn_run(fn, a, b):
        fa = syms[fn] & ~1  # thumb bit
        mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        mu.mem_map(CODE, 0x10000)
        mu.mem_map(LIN, MEM_BYTES)
        mu.mem_map(STK - 0x8000, 0x10000)
        mu.mem_map(RET, 0x1000)
        mu.mem_write(CODE, code)
        mu.mem_write(LIN, b"\x00" * MEM_BYTES)
        mu.reg_write(UC_ARM_REG_SP, STK)
        mu.reg_write(UC_ARM_REG_R11, LIN)        # linear-memory base
        mu.reg_write(UC_ARM_REG_R10, MEM_BYTES)  # memory size (bytes)
        mu.reg_write(UC_ARM_REG_R0, a & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_R1, b & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_LR, RET | 1)
        try:
            mu.emu_start((CODE + fa - base) | 1, RET, count=500000)
        except UcError as e:
            # No vector here should trap; UDF or an unmapped access both mean
            # a wild pointer escaped — report as ERR, never a match.
            return f"ERR:{e}", b""
        return mu.reg_read(UC_ARM_REG_R0), bytes(mu.mem_read(LIN, MEM_BYTES))

    fails = 0
    for fn, a, b in VECTORS:
        gt_ret, gt_img = wasmtime_run(fn, a, b)
        sy_ret, sy_img = unicorn_run(fn, a, b)
        if isinstance(sy_ret, str):
            ok, detail = False, sy_ret
        else:
            ok = sy_ret == gt_ret and sy_img == gt_img
            detail = f"ret synth={sy_ret} wasmtime={gt_ret}"
            if sy_img != gt_img:
                diff = next(i for i in range(MEM_BYTES) if sy_img[i] != gt_img[i])
                detail += (f"; mem differs @{diff}: synth=0x{sy_img[diff]:02x} "
                           f"wasmtime=0x{gt_img[diff]:02x}")
        fails += 0 if ok else 1
        print(f"{fn}({a},{b}): {'OK' if ok else 'MISMATCH'}  [{detail}]")
    print(f"\n{len(VECTORS) - fails}/{len(VECTORS)} match")
    print("ORACLE: PASS" if fails == 0 else f"ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
