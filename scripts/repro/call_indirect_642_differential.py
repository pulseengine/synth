#!/usr/bin/env python3
"""#642 — call_indirect bounds-guard oracle: OOB index must TRAP, not branch.

The Thumb-2 `call_indirect` expansion (`lsl.w ip, idx, #2; ldr.w ip, [r11,
ip]; blx ip`) had NO bounds check and NO type check: an out-of-bounds index
read past the table and BLXed whatever word lay there — an uncontrolled
indirect branch where WASM Core §4.4.8 mandates a deterministic trap. The fix
prepends `movw ip, #size; cmp idx, ip; blo +1; udf #0` (the type check is
discharged at compile time via the closed-world table verification — the raw
code-pointer table carries no runtime type ids).

This harness compiles the fixture via the direct-selector path, then for each
case runs BOTH engines:
  - wasmtime (oracle): in-bounds indices return add/sub/mul results; OOB
    indices trap.
  - unicorn (synth's code, table linked at r11): in-bounds results must match
    wasmtime; OOB indices must stop at a `udf` (0xDExx) — the §4.4.8 trap.

RED-CASE NON-VACUITY: the words PAST the 3-entry table are seeded with a
valid Thumb decoy (`movs r0, #0x5A; bx lr`), so on an unguarded build the OOB
index does NOT fault — it "successfully" calls the decoy and returns 0x5A,
which is precisely the uncontrolled-indirect-branch hole. The harness fails
loudly on that outcome (this is what origin/main does).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/call_indirect_642_differential.py
Exits nonzero on any mismatch, missed trap, or decoy execution.
"""

import os
import struct
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("call_indirect_642_oob.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

CODE, TABLE, STK = 0x1000000, 0x3000000, 0x6000000
RET = CODE + 0xFFF0  # return pad (inside the CODE map)
DECOY = CODE + 0xFF00  # decoy "function" the unguarded build would call
A = 5
IN_BOUNDS = [0, 1, 2]
OOB = [3, 5, 99]


def compile_direct(out: str, target: str) -> None:
    """Compile via the direct-selector path (the one that lowers call_indirect)."""
    r = subprocess.run(
        [
            SYNTH,
            "compile",
            str(WAT),
            "-o",
            out,
            "--target",
            target,
            "--all-exports",
            "--relocatable",
            "--no-optimize",
        ],
        capture_output=True,
        text=True,
    )
    if r.returncode != 0:
        print(f"COMPILE FAILED:\n{r.stdout}\n{r.stderr}")
        sys.exit(1)


def wasmtime_oracle():
    """Ground truth: result per in-bounds index; OOB indices must trap."""
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, WAT.read_text())
    results = {}
    for idx in IN_BOUNDS + OOB:
        store = wasmtime.Store(engine)  # fresh instance per call (stateful)
        f = wasmtime.Instance(store, module, []).exports(store)["f"]
        try:
            results[idx] = f(store, A, idx) & 0xFFFFFFFF
        except wasmtime.Trap:
            results[idx] = "trap"
    return results


def run_unicorn(text: bytes, syms: dict, idx: int, a32: bool):
    """Execute f(A, idx); returns ('ok', r0) or ('trap-udf', pc) or a failure."""
    mu = Uc(UC_ARCH_ARM, UC_MODE_ARM if a32 else UC_MODE_THUMB)
    mu.mem_map(CODE, 0x100000)
    mu.mem_map(TABLE, 0x10000)
    mu.mem_map(STK, 0x100000)
    mu.mem_write(CODE, text)
    if a32:
        # Return pad: A32 NOPs. Decoy: `mov r0, #0x5A; bx lr`.
        mu.mem_write(RET, struct.pack("<II", 0xE320F000, 0xE320F000))
        mu.mem_write(DECOY, struct.pack("<II", 0xE3A0005A, 0xE12FFF1E))
        thumb_bit = 0
    else:
        # Return pad: Thumb NOPs. Decoy: `movs r0, #0x5A; bx lr`.
        mu.mem_write(RET, struct.pack("<HH", 0xBF00, 0xBF00))
        mu.mem_write(DECOY, struct.pack("<HH", 0x205A, 0x4770))
        thumb_bit = 1
    # table[i] = code address (Thumb: bit 0 SET for BLX interwork); slots PAST
    # the declared 3-entry table are seeded with the decoy — a "valid" word an
    # unguarded OOB load would happily BLX (the #642 hole, non-vacuous red).
    entries = [syms["func_0"], syms["func_1"], syms["func_2"]]
    for i, off in enumerate(entries):
        mu.mem_write(TABLE + 4 * i, struct.pack("<I", (CODE + off) | thumb_bit))
    for i in range(len(entries), 128):
        mu.mem_write(TABLE + 4 * i, struct.pack("<I", DECOY | thumb_bit))

    mu.reg_write(UC_ARM_REG_R0, A)
    mu.reg_write(UC_ARM_REG_R1, idx)
    mu.reg_write(UC_ARM_REG_R11, TABLE)
    mu.reg_write(UC_ARM_REG_SP, STK + 0x80000)
    mu.reg_write(UC_ARM_REG_LR, RET | thumb_bit)
    try:
        mu.emu_start((CODE + syms["f"]) | thumb_bit, RET, count=2000)
    except UcError as e:
        pc = mu.reg_read(UC_ARM_REG_PC)
        # A deterministic §4.4.8 trap = execution stopped ON a udf
        # (Thumb 0xDExx / A32 0xE7F000F0).
        if CODE <= pc < CODE + len(text):
            if a32:
                w = struct.unpack("<I", text[pc - CODE : pc - CODE + 4])[0]
                if w == 0xE7F000F0:
                    return ("trap-udf", pc)
            else:
                hw = struct.unpack("<H", text[pc - CODE : pc - CODE + 2])[0]
                if hw & 0xFF00 == 0xDE00:
                    return ("trap-udf", pc)
        return ("fault", f"{e} at pc={pc:#x} (NOT a udf trap)")
    return ("ok", mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF)


def run_isa(oracle: dict, target: str, a32: bool) -> int:
    elf_path = f"/tmp/ci642_{'a32' if a32 else 'thumb'}.o"
    compile_direct(elf_path, target)

    with open(elf_path, "rb") as fh:
        e = ELFFile(fh)
        text = bytes(e.get_section_by_name(".text").data())
        # Symbols from the symtab, never from disasm text (host-dependent).
        st = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
        syms = {s.name: s["st_value"] & ~1 for s in st.iter_symbols() if s.name}
    for need in ("f", "func_0", "func_1", "func_2"):
        if need not in syms:
            print(f"SYMBOL MISSING: {need}")
            return 1

    isa = "A32" if a32 else "Thumb-2"
    fails = 0
    for idx in IN_BOUNDS:
        want = oracle[idx]
        kind, got = run_unicorn(text, syms, idx, a32)
        ok = kind == "ok" and got == want
        fails += 0 if ok else 1
        got_s = f"{got:#x}" if isinstance(got, int) else got
        print(
            f"[{isa}] f({A},{idx}) = {kind}:{got_s} (wasmtime: {want:#x}) "
            f"{'OK' if ok else 'MISMATCH'}"
        )

    for idx in OOB:
        assert oracle[idx] == "trap", f"oracle must trap OOB index {idx}"
        kind, got = run_unicorn(text, syms, idx, a32)
        ok = kind == "trap-udf"
        fails += 0 if ok else 1
        if ok:
            print(f"[{isa}] f({A},{idx}) = udf trap at {got:#x} (wasmtime: trap) OK")
        elif kind == "ok" and got == 0x5A:
            print(
                f"[{isa}] f({A},{idx}) = {got:#x} — the DECOY past the table was "
                "CALLED: uncontrolled indirect branch, no bounds guard (#642) MISMATCH"
            )
        else:
            print(f"[{isa}] f({A},{idx}) = {kind}:{got} (wasmtime: trap) MISMATCH")
    return fails


def main() -> int:
    oracle = wasmtime_oracle()
    print(f"wasmtime oracle: {oracle}")

    # Both ISAs share the #642 gap and the fix: Thumb-2 (cortex-m3) and the
    # #596-added A32 expansion (cortex-r5).
    fails = run_isa(oracle, "cortex-m3", a32=False)
    fails += run_isa(oracle, "cortex-r5", a32=True)

    if fails == 0:
        print("ORACLE: PASS")
        return 0
    print(f"ORACLE: FAIL — {fails} case(s) diverged from wasmtime (#642)")
    return 1


if __name__ == "__main__":
    sys.exit(main())
