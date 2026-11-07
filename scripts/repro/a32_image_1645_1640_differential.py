#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 54
"""#1645 + #1640 — self-contained A32 (`--target cortex-r5`) images, executed
from the addresses the ELF itself declares, against wasmtime.

THE TWO DEFECTS (both exit 0 before the fix):

  #1645  `build_multi_func_simple_elf` never read `func.relocations`, so every
         internal A32 `bl` shipped as the encoder placeholder `ebfffffe` (a
         branch-and-link to itself) while the CLI printed "Internal calls: N
         resolved in place". The single-function path (`--func-name`) shipped
         the same placeholder with the callee absent from the image.
  #1640  The same images set the Thumb bit on `e_entry` and on every A32
         STT_FUNC value (0x8001, ...), so a loader that honours the ELF's
         interworking bit entered the A32 bodies in Thumb state. The default
         no-target build put A32 bodies behind a Cortex-M vector table and a
         Thumb Reset_Handler, which no core can run.

THE ORACLE. No `sym & ~1` workaround: every function is entered at the
STT_FUNC value exactly as emitted, and bit 0 of that value picks the state
(set = Thumb, as an interworking loader would; clear = ARM). The image is
SECTION-loaded — the cortex-r5 image has no program headers and no reset
code, `e_entry` is the first function — so "boot" here means: `.text` placed
at its `sh_addr`, entered at `e_entry` in the state its bit 0 selects, with
the harness supplying SP, the arguments and an LR sentinel. The first
function of the fixture is a CALLER, so the `e_entry` run itself crosses
internal `bl`s. A step limit turns a `bl .` hang into a red row.

Structural checks per image: `e_entry` is even and equals a FUNC symbol; no
FUNC symbol is odd; no `ebfffffe` word is left in `.text`.

Legs:
  r5          --target cortex-r5 --all-exports            (optimized path)
  r5-noopt    --target cortex-r5 --all-exports --no-optimize
  r5-single   --target cortex-r5 --func-name twice         (callee-free single
              function: its entry must be even too)
Refusal legs (compile only, no emulation):
  r5-single-call  --func-name callsq must REFUSE (#1645): the image would hold
                  only `callsq`, so its `bl` has no callee to patch to.
  no-target       `--all-exports` with no --target must REFUSE (#1640): A32
                  bodies behind a Cortex-M Thumb startup cannot run.
  no-target-single  `--func-name twice` with no --target (call-free, so no
                  other refusal can fire first) must REFUSE (#1640) too.

Calls covered: forward `bl` (entry -> sq, entry -> twice), backward `bl`
(callsq -> sq, the #1645 reproducer), a nested chain (chain -> entry ->
sq/twice, chain -> callsq -> sq), and a call inside a loop (sumsq: a counted
loop, bounded by `n & 15`, calling sq every iteration). The loop's label
branches rely on #1639's fix (PR #1644); before it, sumsq is wrong on a
correctly patched image.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/repro/a32_image_1645_1640_differential.py
Exits nonzero on any mismatch.
"""

import os
import struct
import subprocess
import sys
import tempfile

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_ARM, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_SP,
)

SYNTH = os.environ.get("SYNTH", "./target/release/synth")

# Function 0 (`entry`) is the image's e_entry and makes two FORWARD calls;
# `callsq` makes a BACKWARD call (the #1645 reproducer's shape); `chain`
# nests: it calls `entry` (which calls again) and `callsq` (which calls again).
WAT = r"""(module
  (func $entry (export "entry") (param i32 i32) (result i32)
    (i32.add (call $sq (local.get 0)) (call $twice (local.get 1) (local.get 0))))
  (func $sq (param i32) (result i32)
    (i32.add (i32.mul (local.get 0) (local.get 0)) (i32.const 1)))
  (func $twice (export "twice") (param i32 i32) (result i32)
    (i32.sub (i32.shl (local.get 0) (i32.const 1)) (local.get 1)))
  (func $callsq (export "callsq") (param i32 i32) (result i32)
    (call $sq (local.get 0)))
  (func (export "chain") (param i32 i32) (result i32)
    (i32.sub (call $entry (local.get 0) (local.get 1))
             (call $callsq (local.get 1) (local.get 0))))
  (func (export "sumsq") (param i32 i32) (result i32) (local i32)
    (local.set 0 (i32.and (local.get 0) (i32.const 15)))
    (block $done
      (loop $next
        (br_if $done (i32.eqz (local.get 0)))
        (local.set 2 (i32.add (local.get 2) (call $sq (local.get 0))))
        (local.set 0 (i32.sub (local.get 0) (i32.const 1)))
        (br $next)))
    (i32.add (local.get 2) (local.get 1))))
"""

# $twice has the (i32, i32) signature so it is both a callee (of `entry`,
# with its arguments swapped) and a callee-free single-function export.
VECTORS = [(3, 0), (0, 0), (7, 5), (0x1234, 0xFFFF_FFF0), (0xFFFF_FFFF, 2), (100, 0x8000_0000)]

EXPORTS_MULTI = ["entry", "callsq", "chain", "sumsq"]
TEXT_LIMIT = 0x10_0000
STACK_TOP = 0x8_0000
RET = 0x9_0000  # LR sentinel, word-aligned ARM-state NOP
A32_BL_SELF = 0xEBFF_FFFE


def compile_elf(out, extra):
    return subprocess.run(
        [SYNTH, "compile", WAT_PATH, "-o", out, "-b", "arm", *extra],
        capture_output=True,
        text=True,
    )


def load(elf):
    with open(elf, "rb") as fh:
        f = ELFFile(fh)
        text = f.get_section_by_name(".text")
        code, base = text.data(), text["sh_addr"]
        entry = f.header["e_entry"]
        syms = {}
        for s in f.iter_sections():
            if s.header.sh_type == "SHT_SYMTAB":
                for sym in s.iter_symbols():
                    if sym.name and sym["st_info"]["type"] == "STT_FUNC":
                        syms[sym.name] = sym["st_value"]
    return code, base, entry, syms


def structural(code, entry, syms):
    """Problems with the image's declared states and call sites."""
    bad = []
    if entry & 1:
        bad.append(f"e_entry {entry:#x} has the Thumb bit on A32 code (#1640)")
    if entry not in syms.values():
        bad.append(f"e_entry {entry:#x} is not a FUNC symbol value {sorted(map(hex, syms.values()))}")
    for name, v in sorted(syms.items()):
        if v & 1:
            bad.append(f"FUNC {name} = {v:#x} has the Thumb bit on A32 code (#1640)")
    words = struct.unpack(f"<{len(code) // 4}I", code[: len(code) // 4 * 4])
    selfbl = [i * 4 for i, w in enumerate(words) if w == A32_BL_SELF]
    if selfbl:
        bad.append(f"{len(selfbl)} unpatched `bl .` (ebfffffe) at .text+{selfbl} (#1645)")
    return bad


def wasm_run(func, a, b):
    eng = wasmtime.Engine()
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, wasmtime.Module(eng, wasmtime.wat2wasm(WAT)), [])
    s = [x - 2**32 if x >= 2**31 else x for x in (a, b)]
    return inst.exports(st)[func](st, *s) & 0xFFFF_FFFF


def arm_run(code, base, addr, a, b):
    # UC_MODE_ARM; an odd `addr` makes unicorn start in Thumb state, exactly
    # what a loader honouring the ELF's interworking bit would do.
    mu = Uc(UC_ARCH_ARM, UC_MODE_ARM)
    mu.mem_map(0, TEXT_LIMIT)
    mu.mem_write(base, code)
    mu.mem_write(RET, struct.pack("<I", 0xE1A0_0000))  # mov r0, r0
    mu.reg_write(UC_ARM_REG_R0, a)
    mu.reg_write(UC_ARM_REG_R1, b)
    mu.reg_write(UC_ARM_REG_SP, STACK_TOP)
    mu.reg_write(UC_ARM_REG_LR, RET)
    try:
        mu.emu_start(addr, RET, timeout=5_000_000, count=20_000)
    except UcError as e:
        return f"UC_ERR {e} at pc={mu.reg_read(UC_ARM_REG_PC):#x}"
    pc = mu.reg_read(UC_ARM_REG_PC)
    if pc != RET:
        return f"HANG/no-return: stopped at pc={pc:#x}"
    return mu.reg_read(UC_ARM_REG_R0)


def run_leg(name, extra, funcs, entry_func):
    fails = runs = 0
    with tempfile.TemporaryDirectory() as td:
        elf = os.path.join(td, "a.elf")
        r = compile_elf(elf, extra)
        if r.returncode != 0:
            print(f"[{name}] FAIL compile rc={r.returncode}: {r.stderr.strip()[-400:]}")
            return 1, 0
        code, base, entry, syms = load(elf)
        for p in structural(code, entry, syms):
            print(f"[{name}] FAIL structure: {p}")
            fails += 1
        if syms.get(entry_func) != entry:
            print(f"[{name}] FAIL e_entry {entry:#x} != {entry_func} {syms.get(entry_func)}")
            fails += 1
        for func in funcs:
            if func not in syms:
                print(f"[{name}] FAIL symbol missing: {func}")
                fails += 1
                continue
            # the e_entry function is entered at e_entry itself (the boot leg)
            addr = entry if func == entry_func else syms[func]
            for a, b in VECTORS:
                want = wasm_run(func, a, b)
                got = arm_run(code, base, addr, a, b)
                runs += 1
                tag = f"{func}({a:#x}, {b:#x}) @ {addr:#x}"
                if got != want:
                    fails += 1
                    shown = got if isinstance(got, str) else f"{got:#x}"
                    print(f"[{name}] FAIL {tag}: synth={shown} wasmtime={want:#x}")
                else:
                    print(f"[{name}] ok   {tag} = {want:#x}")
    return fails, runs


def refusal_leg(name, extra, needle):
    with tempfile.TemporaryDirectory() as td:
        elf = os.path.join(td, "a.elf")
        r = compile_elf(elf, extra)
        if r.returncode == 0 or needle not in r.stderr:
            print(f"[{name}] FAIL expected a loud refusal citing {needle}; "
                  f"rc={r.returncode} image_written={os.path.exists(elf)}")
            return 1
        if os.path.exists(elf):
            print(f"[{name}] FAIL refused but still wrote {elf}")
            return 1
        print(f"[{name}] ok   refused loudly ({needle})")
        return 0


def main():
    global WAT_PATH
    with tempfile.TemporaryDirectory() as td:
        WAT_PATH = os.path.join(td, "a32_image_1645_1640.wat")
        with open(WAT_PATH, "w") as fh:
            fh.write(WAT)
        fails = runs = 0
        for name, extra in (
            ("r5", ["--target", "cortex-r5", "--all-exports"]),
            ("r5-noopt", ["--target", "cortex-r5", "--all-exports", "--no-optimize"]),
        ):
            f, n = run_leg(name, extra, EXPORTS_MULTI, "entry")
            fails += f
            runs += n
        f, n = run_leg("r5-single", ["--target", "cortex-r5", "--func-name", "twice"],
                       ["twice"], "twice")
        fails += f
        runs += n
        fails += refusal_leg("r5-single-call",
                             ["--target", "cortex-r5", "--func-name", "callsq"], "(#1645)")
        fails += refusal_leg("no-target", ["--all-exports"], "(#1640)")
        fails += refusal_leg("no-target-single", ["--func-name", "twice"], "(#1640)")
    if fails:
        sys.exit(f"\n#1645/#1640 A32 image differential: {fails} failure(s), {runs} emulations")
    print(f"\n#1645/#1640 A32 image differential: all {runs} emulations green, 3 refusals loud")


if __name__ == "__main__":
    main()
