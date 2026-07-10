#!/usr/bin/env python3
"""#679 — `--safety-bounds mask` bulk-memory coverage oracle (thumb-2).

Pre-fix, `memory.copy`/`memory.fill` under `--safety-bounds mask` were emitted
**byte-identical to `--safety-bounds none`** — no fold, no clamp — while the
`safety-manifest.json` still attested `"safety_bounds": "mask"` for the whole
module: an attestation-integrity hole (the mask sandbox was silently absent
for bulk memory). The fix applies the scalar `mask_effective_address`
wrap-not-trap discipline to the bulk lowering: dst and src effective addresses
fold with `AND (size-1)`, and len clamps to `size - dst` / `size - src` so the
FINAL byte stays in bounds.

Three gates, all RED on pre-fix main:

  1. BYTE-DIFF: the `.text` of a mask build must DIFFER from a `none` build of
     the same module (pre-fix: `cmp` equal). The manifest must attest `mask`
     for the mask build — attestation and emission move together.
  2. ESCAPE/FOLD: run the mask ELF under unicorn with R10 = mem_size = 4096
     (power of two) and dst/src beyond it. Mask semantics are MODELED in
     python (wasmtime cannot model a 4 KiB bound — wasm's minimum is one
     64 KiB page; OOB in wasm traps, mask deliberately wraps instead):
     escaped operands must fold mod 4096, len must clamp to the bound.
  3. CONTAINMENT: after every masked run, NO byte outside [0, mem_size) may
     have changed (the linear map is 64 KiB, so an un-masked escape would
     write silently — exactly the pre-fix failure, not a fault).

Symbols come from the ELF symtab (pyelftools), not `synth disasm` (PR #489).

Run:
  SYNTH=./target/release/synth python scripts/repro/bulk_mask_679_differential.py
Exits nonzero on any failure.
"""

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("bulk_mask_679.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")

MASK_SIZE = 4096       # R10: the power-of-two mem_size the mask folds into
MAP_BYTES = 0x10000    # the 64 KiB actually mapped — escapes write, not fault
CODE, LIN, STK, RET = 0x200000, 0x400000, 0x90000, 0x300000

# (fn, arg0, arg1, expected_return) — mask semantics modeled by hand.
VECTORS = [
    # escaped dst 4096+16 folds to 16 -> the byte lands where we read
    ("cpy_esc", MASK_SIZE + 16, 0, 171),
    # in-bounds control: same op fully in bounds behaves identically
    ("cpy_esc", 16, 0, 171),
    # fill: escaped dst 4096+24 folds to 24
    ("fil_esc", MASK_SIZE + 24, 0, 238),
    ("fil_esc", 24, 0, 238),
    # escaped SRC 4096+40 folds to 40 (read-side masking)
    ("cpy_src_esc", MASK_SIZE + 40, 0, 205),
    ("cpy_src_esc", 40, 0, 205),
    # len clamp: dst=4092, len=400 -> len=4, copy ends AT the bound
    ("cpy_clamp", 0, 400, 119),
    # len already in bounds -> clamp is a no-op
    ("cpy_clamp", 0, 4, 119),
]


def compile_elf(bounds):
    out = tempfile.NamedTemporaryFile(suffix=f"_{bounds}.elf", delete=False).name
    subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, "--target", "cortex-m4",
         "--all-exports", "--safety-bounds", bounds],
        check=True,
    )
    return out


def load_text_and_syms(elf_path):
    with open(elf_path, "rb") as f:
        ef = ELFFile(f)
        text = ef.get_section_by_name(".text")
        code, base = text.data(), text["sh_addr"]
        syms = {}
        symtab = ef.get_section_by_name(".symtab")
        if symtab is not None:
            for s in symtab.iter_symbols():
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


# A module whose functions contain ONLY bulk-memory ops (no scalar
# loads/stores, which mask correctly and would hide the gap): pre-fix, the
# mask build of THIS module is byte-identical to the none build — the
# issue's `cmp` evidence.
PURE_BULK_WAT = """(module (memory 1)
 (func (export "c") (param i32 i32 i32)
   (memory.copy (local.get 0) (local.get 1) (local.get 2)))
 (func (export "f") (param i32 i32 i32)
   (memory.fill (local.get 0) (local.get 1) (local.get 2))))
"""


def main():
    fails = 0
    mask_elf = compile_elf("mask")
    none_elf = compile_elf("none")

    # ---- gate 1: attestation integrity — the emission of a PURE bulk-memory
    # module must differ from `none` (pre-fix: byte-identical, while the
    # manifest attested mask), and the manifest must attest mask.
    pure = Path(tempfile.NamedTemporaryFile(suffix=".wat", delete=False).name)
    pure.write_text(PURE_BULK_WAT)
    pure_elfs = {}
    for bounds in ("mask", "none"):
        out = tempfile.NamedTemporaryFile(suffix=f"_pure_{bounds}.elf",
                                          delete=False).name
        subprocess.run(
            [SYNTH, "compile", str(pure), "-o", out, "--target", "cortex-m4",
             "--all-exports", "--safety-bounds", bounds],
            check=True,
        )
        pure_elfs[bounds], _, _ = load_text_and_syms(out)
    if pure_elfs["mask"] == pure_elfs["none"]:
        print("BYTE-DIFF: FAIL — pure-bulk mask .text is byte-identical to "
              "none (the #679 silent no-op)")
        fails += 1
    else:
        print(f"BYTE-DIFF: OK — pure-bulk mask .text differs from none "
              f"({len(pure_elfs['mask'])} vs {len(pure_elfs['none'])} bytes)")
    manifest_path = Path(mask_elf).with_suffix("") .as_posix() + ".safety-manifest.json"
    candidates = [manifest_path, mask_elf + ".safety-manifest.json",
                  str(Path(mask_elf).with_name(Path(mask_elf).stem + ".safety-manifest.json"))]
    manifest = None
    for c in candidates:
        if os.path.exists(c):
            manifest = json.load(open(c))
            break
    if manifest is None:
        print("MANIFEST: WARN — no safety-manifest sidecar found "
              f"(looked at {candidates})")
    elif str(manifest.get("safety_bounds", "")).lower() not in ("mask", "masking"):
        print(f"MANIFEST: FAIL — mask build attests {manifest.get('safety_bounds')!r}")
        fails += 1
    else:
        print("MANIFEST: OK — mask build attests mask (and now emits it)")

    # ---- gates 2+3: execution under unicorn with R10 = 4096.
    code, base, syms = load_text_and_syms(mask_elf)

    def run(fn, a, b):
        fa = syms[fn] & ~1
        mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        mu.mem_map(CODE, 0x10000)
        mu.mem_map(LIN, MAP_BYTES)
        mu.mem_map(STK - 0x8000, 0x10000)
        mu.mem_map(RET, 0x1000)
        mu.mem_write(CODE, code)
        mu.mem_write(LIN, b"\x00" * MAP_BYTES)
        mu.reg_write(UC_ARM_REG_SP, STK)
        mu.reg_write(UC_ARM_REG_R11, LIN)
        mu.reg_write(UC_ARM_REG_R10, MASK_SIZE)  # mem_size the mask folds into
        mu.reg_write(UC_ARM_REG_R0, a & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_R1, b & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_LR, RET | 1)
        try:
            mu.emu_start((CODE + fa - base) | 1, RET, count=500000)
        except UcError as e:
            return f"ERR:{e}", b""
        return mu.reg_read(UC_ARM_REG_R0), bytes(mu.mem_read(LIN, MAP_BYTES))

    for fn, a, b, expect in VECTORS:
        ret, img = run(fn, a, b)
        if isinstance(ret, str):
            ok, detail = False, ret
        else:
            contained = all(v == 0 for v in img[MASK_SIZE:])
            ok = ret == expect and contained
            detail = f"ret={ret} expect={expect}"
            if not contained:
                leak = next(i for i in range(MASK_SIZE, MAP_BYTES) if img[i] != 0)
                detail += f"; ESCAPED write at raw offset {leak} (>= mem_size)"
        fails += 0 if ok else 1
        print(f"{fn}({a},{b}): {'OK' if ok else 'MISMATCH'}  [{detail}]")

    print(f"\nORACLE: {'PASS' if fails == 0 else f'FAIL ({fails})'}")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
