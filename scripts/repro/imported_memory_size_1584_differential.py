#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 138
"""RQ-89-IMPSIZE (#1584, and the imported-memory residual of #1339) — an
IMPORTED memory 0 must be sized from its own declaration, or refused.

THE DEFECT, measured on v0.88/v0.89-main (d4c0b232) before the fix. Memory 0's
size was read from the first DEFINED memory, and an imported memory is not in
that list, so an imported-only module compiled rc=0 and sized memory 0 by a
fallback:

  * RV32 and AArch64 fell back to ZERO bytes: `memory.size 0` returned 0 where
    wasmtime returns the import's pages, and AArch64 (bounds-checked by
    default) trapped every IN-BOUNDS access;
  * self-contained ARM fell back to ONE page — correct for `(memory 1 1)` only
    by coincidence: an imported `(memory 2 2)` image was byte-identical to the
    `(memory 1 1)` one, so `memory.size` said 1 and the software guard trapped
    the in-bounds second page;
  * an imported `(pagesize 1)` memory skipped the custom-page-size refusal
    (#1339's residual): ARM `--relocatable` lowered `memory.size` as `R10 >>
    16` (0 for a 20000-byte memory; wasmtime 20000) and every other path
    compiled it rc=0 as well.

THE DECISION this oracle pins, per path:

  * ARM `--relocatable`: memory 0's size is the embedder's R10 at run time,
    so every limits shape is accepted (unchanged bytes for 64 KiB pages), and
    `(pagesize 1)` is honoured exactly as for a DEFINED memory (#1441): the
    harness hands R10 the declared byte count and `memory.size` must equal it.
  * self-contained ARM: synth IS the instantiator, and resolving the import
    with a memory of exactly its declared minimum is a legal instantiation
    for ANY declared maximum (the spec lets `memory.grow` fail). So memory 0
    is sized from the import's minimum. `(pagesize 1)` is refused, as for a
    defined memory.
  * RV32 and AArch64: the size is a COMPILE-TIME constant (`memory.size` and
    the bounds limit are baked) in an object whose memory the EMBEDDER
    supplies. The import's declared limits let the host supply any size in
    [min, max], so a baked size is sound only when the limits PIN it
    (max == min) — the #642 imported-table rule. Pinned shapes are sized from
    the declaration; an imported memory with no maximum, or max > min, is
    LOUDLY REFUSED naming #1584 rather than given a size the embedder was
    never told about. `(pagesize 1)` is refused, as for a defined memory.

The reference: wasmtime, instantiated with the import satisfied by
`Memory(MemoryType(Limits(min, max), page_size_log2))` — exactly the declared
minimum, the same instantiation the emulators model. Every accepted leg is
EXECUTED (unicorn) and compared row by row; trap classification is strict
(only the backend's own trap instruction counts — an unmapped fault is a
miscompile), and memory past the declared minimum is mapped and POISONED so an
unchecked out-of-bounds read returns garbage rather than a lucky zero.

Run:  SYNTH=./target/debug/synth python3 scripts/repro/imported_memory_size_1584_differential.py
"""

import importlib.util
import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import (
    UC_ARCH_ARM,
    UC_ARCH_ARM64,
    UC_ARCH_RISCV,
    UC_ERR_EXCEPTION,
    UC_HOOK_INTR,
    UC_MODE_ARM,
    UC_MODE_RISCV32,
    UC_MODE_THUMB,
    Uc,
    UcError,
)
from unicorn.arm64_const import (
    UC_ARM64_REG_LR,
    UC_ARM64_REG_SP,
    UC_ARM64_REG_W0,
    UC_ARM64_REG_X0,
    UC_ARM64_REG_X28,
)
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R9,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)
from unicorn.riscv_const import (
    UC_RISCV_REG_A0,
    UC_RISCV_REG_PC,
    UC_RISCV_REG_RA,
    UC_RISCV_REG_S11,
    UC_RISCV_REG_SP,
)

REPRO = Path(__file__).resolve().parent
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
M32 = 0xFFFFFFFF
POISON = 0xEE
STORED = 0x5A5A1234

# The self-contained boot harness is reused, not re-implemented: it boots the
# image through its own Reset_Handler, which is where memory 0's size (R10)
# is established on that path.
_spec = importlib.util.spec_from_file_location(
    "boot1189", REPRO / "self_contained_boot_sweep_1189_differential.py"
)
boot = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(boot)

# (name, min, max, page_size_log2) — the import's declared limits.
SHAPES = [
    ("1_1", 1, 1, 16),
    ("2_2", 2, 2, 16),
    ("0_0", 0, 0, 16),
    ("1_2", 1, 2, 16),
    ("1_nomax", 1, None, 16),
    ("ps1_20000", 20000, 20000, 0),
]

LEGS = {
    "arm-sc": ["--all-exports", "--target", "cortex-m4", "--safety-bounds", "software"],
    "arm-sc-noopt": ["--all-exports", "--target", "cortex-m4", "--no-optimize",
                     "--safety-bounds", "software"],
    "arm-reloc": ["--all-exports", "--target", "cortex-m4", "--relocatable",
                  "--safety-bounds", "software"],
    "rv32": ["-b", "riscv", "-t", "rv32imac", "--all-exports", "--relocatable",
             "--safety-bounds", "software"],
    "a64": ["-b", "aarch64", "--all-exports"],
    # The single-function path decodes the module on its own and sizes memory
    # 0 independently of the module path; exercised on the two baked-size
    # backends (the single-function Cortex-M image hardcodes one page for
    # EVERY module, imported or defined — outside this lane, not run here).
    "rv32-n": ["-b", "riscv", "-t", "rv32imac", "-n", "size0"],
    "a64-n": ["-b", "aarch64", "-n", "size0"],
}


def page_bytes(log2):
    return 1 << log2


def expected_accept(leg, shape):
    _, mn, mx, log2 = shape
    if leg == "arm-reloc":
        return True, None
    if log2 != 16:
        return False, "pagesize 1"
    if leg.startswith("arm-sc"):
        return True, None
    # rv32 / a64 (module and single-function): the limits must PIN the size.
    if mx == mn:
        return True, None
    return False, "#1584"


def wat_for(shape):
    _, mn, mx, log2 = shape
    lim = f"{mn}" + (f" {mx}" if mx is not None else "")
    ps = " (pagesize 1)" if log2 == 0 else ""
    return f"""(module
  (import "env" "m0" (memory {lim}{ps}))
  (func (export "size0") (result i32) (memory.size 0))
  (func (export "rt") (param i32) (result i32)
    (i32.store (local.get 0) (i32.const {STORED:#x}))
    (i32.load (local.get 0))))
"""


def vectors(shape):
    """[(fn, args)] — the size, the first and last in-bounds word, and the
    first out-of-bounds word, plus a far address."""
    _, mn, _, log2 = shape
    nbytes = mn * page_bytes(log2)
    vs = [("size0", [])]
    if nbytes >= 4:
        vs += [("rt", [0]), ("rt", [nbytes - 4])]
    vs += [("rt", [nbytes]), ("rt", [nbytes - 2 if nbytes >= 2 else 0x7FFFFFF0])]
    vs += [("rt", [nbytes + 0x10000 - 4])]
    return vs


def reference(shape, fn, args):
    _, mn, mx, log2 = shape
    cfg = wasmtime.Config()
    cfg.wasm_custom_page_sizes = True
    engine = wasmtime.Engine(cfg)
    module = wasmtime.Module(engine, wat_for(shape))
    store = wasmtime.Store(engine)
    mem = wasmtime.Memory(store, wasmtime.MemoryType(wasmtime.Limits(mn, mx), page_size_log2=log2))
    inst = wasmtime.Instance(store, module, [mem])
    sargs = [a - (1 << 32) if a & (1 << 31) else a for a in args]
    try:
        r = inst.exports(store)[fn](store, *sargs)
    except wasmtime.Trap:
        return ("trap",)
    return ("value", (r or 0) & M32)


def symbols(path):
    with open(path, "rb") as fh:
        elf = ELFFile(fh)
        text_idx = elf.get_section_index(".text")
        text = elf.get_section_by_name(".text").data()
        if any(s.name.startswith((".rel.text", ".rela.text")) for s in elf.iter_sections()):
            raise RuntimeError("text carries relocations — this harness maps it unlinked")
        st = elf.get_section_by_name(".symtab")
        syms = {s.name: s["st_value"] & ~1 for s in st.iter_symbols()
                if s.name and s["st_shndx"] == text_idx}
    return text, syms


CODE, STK, RET, LIN = 0x100000, 0x400000, 0x500000, 0x1000000


def lin_map(nbytes):
    span = (nbytes + 0x20000 + 0xFFF) & ~0xFFF
    return span


def run_arm_reloc(path, shape, fn, args):
    _, mn, _, log2 = shape
    nbytes = mn * page_bytes(log2)
    text, syms = symbols(path)
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET, 0x1000)
    span = lin_map(nbytes)
    mu.mem_map(LIN, span)
    mu.mem_write(LIN + nbytes, bytes([POISON]) * (span - nbytes))
    mu.mem_write(CODE, text)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    mu.reg_write(UC_ARM_REG_R11, LIN)          # embedder: linear-memory base
    mu.reg_write(UC_ARM_REG_R10, nbytes)       # embedder: size in BYTES (#1131)
    mu.reg_write(UC_ARM_REG_R9, STK - 0x8000)  # an unused globals base
    for i, a in enumerate(args):
        mu.reg_write(UC_ARM_REG_R0 + i, a & M32)
    try:
        mu.emu_start((CODE + syms[fn]) | 1, RET, count=4000)
    except UcError as e:
        pc = mu.reg_read(UC_ARM_REG_PC) & ~1
        hw1, hw2 = struct.unpack("<HH", bytes(mu.mem_read(pc, 4)))
        if (hw1 & 0xFF00) == 0xDE00 or ((hw1 & 0xFFF0) == 0xF7F0 and (hw2 & 0xF000) == 0xA000):
            return ("trap",)
        return ("fault", str(e))
    return ("value", mu.reg_read(UC_ARM_REG_R0) & M32)


def run_rv32(path, shape, fn, args):
    _, mn, _, log2 = shape
    nbytes = mn * page_bytes(log2)
    text, syms = symbols(path)
    mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET, 0x1000)
    span = lin_map(nbytes)
    mu.mem_map(LIN, span)
    mu.mem_write(LIN + nbytes, bytes([POISON]) * (span - nbytes))
    mu.mem_write(CODE, text)
    mu.reg_write(UC_RISCV_REG_SP, STK)
    mu.reg_write(UC_RISCV_REG_S11, LIN)
    mu.reg_write(UC_RISCV_REG_RA, RET)
    for i, a in enumerate(args):
        mu.reg_write(UC_RISCV_REG_A0 + i, a & M32)
    trapped = []

    def on_intr(uc, *_):
        trapped.append(True)
        uc.emu_stop()

    mu.hook_add(UC_HOOK_INTR, on_intr)
    try:
        mu.emu_start(CODE + syms[fn], RET, count=4000)
    except UcError as e:
        # unicorn reports the RV32 `ebreak` as UC_ERR_INSN_INVALID with the PC
        # parked ON it; only that instruction counts as the trap.
        pc = mu.reg_read(UC_RISCV_REG_PC)
        word = struct.unpack("<I", bytes(mu.mem_read(pc, 4)))[0]
        if word == 0x00100073 or (word & 0xFFFF) == 0x9002:
            return ("trap",)
        return ("fault", str(e))
    if trapped:
        return ("trap",)
    return ("value", mu.reg_read(UC_RISCV_REG_A0) & M32)


def run_a64(path, shape, fn, args):
    _, mn, _, log2 = shape
    nbytes = mn * page_bytes(log2)
    text, syms = symbols(path)
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET, 0x1000)
    span = lin_map(nbytes)
    mu.mem_map(LIN, span)
    mu.mem_write(LIN + nbytes, bytes([POISON]) * (span - nbytes))
    mu.mem_write(CODE, text)
    mu.reg_write(UC_ARM64_REG_SP, STK)
    mu.reg_write(UC_ARM64_REG_LR, RET)
    mu.reg_write(UC_ARM64_REG_X28, LIN)
    for i, a in enumerate(args):
        mu.reg_write(UC_ARM64_REG_X0 + i, a & M32)
    try:
        mu.emu_start(CODE + syms[fn], RET, count=4000)
    except UcError as e:
        if e.errno == UC_ERR_EXCEPTION:
            return ("trap",)  # `brk`
        return ("fault", str(e))
    return ("value", mu.reg_read(UC_ARM64_REG_W0) & M32)


def run_arm_sc(img, fn, args):
    res, viol = img.call(fn, list(args), 1)
    if viol:
        return ("fault", "; ".join(viol))
    if res[0] == "ok":
        return ("value", res[1][0])
    return res


def main():
    fails = []
    counts = {"compiled": 0, "refused": 0, "compared": 0}
    tmp = Path(tempfile.mkdtemp(prefix="impsize_1584_"))
    for shape in SHAPES:
        src = tmp / f"{shape[0]}.wat"
        src.write_text(wat_for(shape))
        for leg, flags in LEGS.items():
            want_ok, needle = expected_accept(leg, shape)
            out = tmp / f"{shape[0]}.{leg}.o"
            r = subprocess.run([SYNTH, "compile", str(src), *flags, "-o", str(out)],
                               capture_output=True, text=True)
            tag = f"{shape[0]}|{leg}"
            if not want_ok:
                if r.returncode == 0:
                    fails.append(f"{tag}: compiled rc=0, must REFUSE (naming {needle})")
                elif needle not in r.stderr:
                    fails.append(f"{tag}: refused, but the diagnostic does not name {needle!r}: "
                                 f"{r.stderr.strip()[-300:]}")
                else:
                    counts["refused"] += 1
                    print(f"ok  {tag}: refused, names {needle}")
                continue
            if r.returncode != 0:
                fails.append(f"{tag}: REFUSED rc={r.returncode}, must compile: {r.stderr.strip()[-300:]}")
                continue
            counts["compiled"] += 1
            img = None
            if leg.startswith("arm-sc"):
                try:
                    img = boot.Image(out)
                except boot.Harness as e:
                    fails.append(f"{tag}: not a bootable image: {e}")
                    continue
                if img.boot != "ok":
                    fails.append(f"{tag}: boot {img.boot}")
                    continue
            vs = vectors(shape)
            if leg.endswith("-n"):
                vs = [v for v in vs if v[0] == "size0"]
            for fn, args in vs:
                want = reference(shape, fn, args)
                if leg.startswith("arm-sc"):
                    got = run_arm_sc(img, fn, args)
                elif leg == "arm-reloc":
                    got = run_arm_reloc(out, shape, fn, args)
                elif leg.startswith("rv32"):
                    got = run_rv32(out, shape, fn, args)
                else:
                    got = run_a64(out, shape, fn, args)
                counts["compared"] += 1
                row = f"{tag} {fn}({', '.join(hex(a) for a in args)})"
                if got != want:
                    fails.append(f"{row}: synth {got} != wasmtime {want}")
                else:
                    print(f"ok  {row}: {got}")
    print(f"#1584 compiled={counts['compiled']} refused={counts['refused']} "
          f"compared={counts['compared']}")
    if fails:
        print(f"\nFAIL — {len(fails)} disagreement(s):")
        for f in fails:
            print(f"BUG {f}")
        return 1
    print("PASS — every imported-memory shape is sized from its declaration or refused")
    return 0


if __name__ == "__main__":
    sys.exit(main())
