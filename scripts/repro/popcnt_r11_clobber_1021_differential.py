#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 100
"""#1021 — i32.popcnt expansion clobbers R11, the WASM linear-memory base.

LIVE MEMORY-SAFETY MISCOMPILE in shipped v0.58.0. The Thumb-2 `i32.popcnt`
inline expansion took R11 as a second scratch register (its own comment said
"We need a second scratch register. Use R11.") — six R11 writes, the last
being `lsr.w r11, rd, #16`. R11 is the linear-memory base every subsequent
LDR/STR reads through, and it is NOT in the expansion's saved set, so the
corruption LEAKS to the caller: every later `[r11]` access in the whole call
chain reads through garbage. The A32 transcription (#615) deliberately
mirrored "the Thumb-2 arm's register contract (R11 + R12 as scratch)" and
inherited the defect, so BOTH backends are gated here.

Confirmed observation (unicorn vs wasmtime, `--cortex-m`, v0.58.0):
`pc_load(0xFF)` expected 1242, OBSERVED 0x20020008 — popcnt(0xFF)=8 plus the
word at ADDRESS 0 (the vector table's initial SP), because R11 ended as
`x_intermediate >> 16` = 0.

Three legs, each vs wasmtime ground truth:
  - thumb-optimized : default cortex-m4 compile (optimized ir_to_arm path,
                      asserted non-vacuously via SYNTH_PATH_DEBUG)
  - thumb-direct    : cortex-m4 --no-optimize (direct selector)
  - a32-direct      : cortex-r5 --relocatable --no-optimize (A32, UC_MODE_ARM;
                      the in-module `bl` is resolved in-process, R_ARM_CALL)

Checks per (leg, export, vector):
  1. return VALUE == wasmtime (never merely "the program ran");
  2. the final 64 KiB linear-memory IMAGE == wasmtime's (a store through a
     corrupted base lands outside the image and is caught here even when the
     wrong-base store/load round-trips to a correct-looking return value);
  3. R11 == the linear-memory base after return (the CROSS-CALL leak, checked
     at the harness/caller level on the direct legs where R11 is the seeded
     ABI base; `pc_caller` additionally proves it INSIDE generated code on
     every leg — the caller's own load after `call $leaf` must still see the
     caller's store).

The low 64 KiB of the address space is mapped and POISONED (0xB5 fill) so a
pre-fix read through the corrupted base (which lands in 0x0..0x4000) returns
a legible poison word instead of an unmapped fault.

Exports: pc_load (the confirmed repro), pc_store (store side), pc_caller (the
leak), pc (plain popcnt guard), pc64 (i64.popcnt guard — R3/R4/R5/R12 pushed
scratch, the discipline i32 should have had; must stay green throughout).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/popcnt_r11_clobber_1021_differential.py
"""
import os
import struct
import subprocess
import sys
import tempfile

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = os.path.join(os.path.dirname(__file__), "popcnt_r11_clobber_1021.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

M32 = 0xFFFFFFFF
MEM_BYTES = 0x10000  # (memory 1)
CODE = 0x00200000
# Optimized self-contained path materializes the ABSOLUTE base 0x20000100;
# the direct paths are R11-relative. Same trick as the #377 harness: one
# window serves both.
LIN_PAGE = 0x20000000
LIN = 0x20000100
STK = 0x30010000
RET = 0x00300000
POISON_BYTE = 0xB5  # low-memory fill: a read through a corrupted base is legible

R_ARM_THM_CALL, R_ARM_THM_JUMP24, R_ARM_CALL = 10, 30, 28

EXPORTS = ["pc_load", "pc_store", "pc_caller", "pc", "pc64"]
VECTORS = [0xFF, 0, 1, 0xFFFFFFFF, 0x80000000, 0xDEADBEEF, 0x0F0F0F0F, 0x12345678]


def die(msg):
    print(f"FATAL: {msg}")
    sys.exit(2)


def to_i32(x):
    return x - (1 << 32) if x >= (1 << 31) else x


def compile_leg(td, name, target, extra, expect_optimized):
    out = os.path.join(td, f"pc1021_{name}.o")
    env = dict(os.environ, SYNTH_PATH_DEBUG="1")
    r = subprocess.run(
        [SYNTH, "compile", WAT, "--target", target, "--all-exports", "-o", out] + extra,
        capture_output=True, text=True, env=env,
    )
    if r.returncode != 0:
        die(f"synth compile ({name}) failed rc={r.returncode}:\n{r.stdout}\n{r.stderr}")
    if expect_optimized and "optimized (ir_to_arm ok)" not in r.stderr:
        die(f"leg {name} did not take the optimized path — gate would be vacuous:\n{r.stderr}")
    return out


def encode_thm_bl(pc, target):
    off = (target - (pc + 4)) & 0x1FFFFFF
    s = (off >> 24) & 1
    i1, i2 = (off >> 23) & 1, (off >> 22) & 1
    imm10, imm11 = (off >> 12) & 0x3FF, (off >> 1) & 0x7FF
    j1, j2 = (~i1 & 1) ^ s, (~i2 & 1) ^ s
    return 0xF000 | (s << 10) | imm10, 0xD000 | (j1 << 13) | (j2 << 11) | imm11


def load_elf(path, thumb):
    """(syms, .text bytes with in-module calls resolved, text base addr).

    Calls are patched by the EXECUTION MODE of the leg, not by the declared
    reloc type: synth labels the in-module `bl` R_ARM_THM_CALL (type 10) even
    on the cortex-r5 (A32) object, where the placeholder is an A32 `BL`
    word (0xEBxxxxxx) — patching Thumb halfwords into it produced
    UC_ERR_INSN_INVALID, not a real popcnt finding. (The mislabel itself is a
    synth ELF-builder quirk worth its own issue; a real linker would build an
    interwork veneer or mis-patch the same way this harness first did.)
    """
    e = ELFFile(open(path, "rb"))
    symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
    syms = {s.name: s["st_value"] for s in symtab.iter_symbols() if s.name}
    tsec = e.get_section_by_name(".text")
    text, base = bytearray(tsec.data()), tsec["sh_addr"]

    for sec in e.iter_sections():
        if sec["sh_type"] not in ("SHT_REL", "SHT_RELA"):
            continue
        if not sec.name.endswith(".text"):
            continue
        for r in sec.iter_relocations():
            t = r["r_info_type"]
            name = symtab.get_symbol(r["r_info_sym"]).name
            if name not in syms:
                die(f"reloc names {name!r}, not a defined symbol")
            if t not in (R_ARM_THM_CALL, R_ARM_THM_JUMP24, R_ARM_CALL):
                die(f"unexpected reloc type {t}")
            off = r["r_offset"]
            if thumb:
                hw1, hw2 = encode_thm_bl(CODE + off, CODE + (syms[name] & ~1))
                struct.pack_into("<HH", text, off, hw1, hw2)
            else:
                word = 0xEB000000 | ((((syms[name] & ~1) - (off + 8)) >> 2) & 0xFFFFFF)
                struct.pack_into("<I", text, off, word)
    return syms, bytes(text), base


def wasmtime_run(engine, module, fn, x):
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    ret = inst.exports(store)[fn](store, to_i32(x)) & M32
    mem = inst.exports(store)["memory"]
    return ret, bytes(mem.read(store, 0, MEM_BYTES))


def unicorn_run(mode, syms, text, base, fn, x):
    addr = syms.get(fn)
    if addr is None:
        return None, None, None, f"symbol {fn} missing from .symtab"
    mu = Uc(UC_ARCH_ARM, mode)
    mu.mem_map(0x0, MEM_BYTES)  # poison low memory: corrupted-base target zone
    mu.mem_map(CODE, 0x40000)
    mu.mem_map(LIN_PAGE, 0x11000)
    mu.mem_map(STK - 0x10000, 0x10000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(0x0, bytes([POISON_BYTE]) * MEM_BYTES)
    mu.mem_write(CODE, text)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, LIN)        # linear-memory base (direct paths)
    mu.reg_write(UC_ARM_REG_R10, MEM_BYTES)  # memory size, if a guard wants it
    mu.reg_write(UC_ARM_REG_R0, x & M32)
    thumb = mode == UC_MODE_THUMB
    mu.reg_write(UC_ARM_REG_LR, RET | (1 if thumb else 0))
    try:
        start = CODE + (addr & ~1) - base
        mu.emu_start(start | (1 if thumb else 0), RET, count=200_000)
    except UcError as ex:
        return None, None, None, f"{ex} (pc-ish state unrecoverable)"
    ret = mu.reg_read(UC_ARM_REG_R0) & M32
    img = bytes(mu.mem_read(LIN, MEM_BYTES))
    r11 = mu.reg_read(UC_ARM_REG_R11) & M32
    return ret, img, r11, ""


LEGS = [
    # (name, target, extra flags, expect_optimized, unicorn mode, check r11 after)
    ("thumb-optimized", "cortex-m4", [], True, UC_MODE_THUMB, True),
    ("thumb-direct", "cortex-m4", ["--no-optimize"], False, UC_MODE_THUMB, True),
    ("a32-direct", "cortex-r5", ["--relocatable", "--no-optimize"], False, UC_MODE_ARM, True),
]


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(WAT).read())

    total_fails = 0
    with tempfile.TemporaryDirectory() as td:
        for name, target, extra, expect_opt, mode, check_r11 in LEGS:
            obj = compile_leg(td, name, target, extra, expect_opt)
            syms, text, base = load_elf(obj, thumb=(mode == UC_MODE_THUMB))
            print(f"=== {name} ({target} {' '.join(extra) or 'default'}) ===")
            fails = 0
            for fn in EXPORTS:
                for x in VECTORS:
                    want, want_img = wasmtime_run(engine, module, fn, x)
                    got, got_img, r11, err = unicorn_run(mode, syms, text, base, fn, x)
                    if err:
                        ok, detail = False, f"ERR {err}"
                    else:
                        ok = got == want
                        detail = f"want=0x{want:08x} got=0x{got:08x}"
                        if ok and got_img != want_img:
                            d = next(i for i in range(MEM_BYTES) if got_img[i] != want_img[i])
                            ok = False
                            detail += (f" MEM differs @+{d}: synth=0x{got_img[d]:02x}"
                                       f" wasmtime=0x{want_img[d]:02x}")
                        if ok and check_r11 and r11 != LIN:
                            ok = False
                            detail += f" R11 LEAKED: 0x{r11:08x} != base 0x{LIN:08x}"
                    fails += 0 if ok else 1
                    if not ok or x == 0xFF:
                        print(f"  {'ok ' if ok else 'BUG'} {fn}(0x{x:x}): {detail}")
            print(f"  {len(EXPORTS) * len(VECTORS) - fails}/{len(EXPORTS) * len(VECTORS)}"
                  f" match on {name}\n")
            total_fails += fails

    print(f"#1021 popcnt-R11-clobber ORACLE: "
          f"{'PASS' if total_fails == 0 else f'FAIL ({total_fails} mismatches)'}")
    sys.exit(1 if total_fails else 0)


if __name__ == "__main__":
    main()
