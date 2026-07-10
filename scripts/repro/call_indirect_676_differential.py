#!/usr/bin/env python3
"""#676 — heterogeneous-table call_indirect oracle: runtime type check.

The fixture's 5-slot table interleaves TWO structural signature classes
(slots 0/2 = (i32,i32)->i32, slot 1 = (i32)->i32 — via a structurally-
duplicate type decl for slot 2, the meld dedup shape) and leaves slots 3/4
null. Pre-#676 the closed-world verifier rejected EVERY expected type on
such a table and both dispatchers loud-declined — on origin/main this
harness is RED at the compile step (SYMBOL MISSING). #676 discharges the
WASM Core §4.4.8 type check at RUNTIME: the object carries a type-id
sidecar (`.synth.table_type_ids`, one u32 structural class id per slot,
id 0 = null) which the harness links at `R11 + sum(table sizes)*4` per the
layout contract, and the dispatch compares the indexed slot's id against
the expected class id (compile-time immediate), UDF-trapping on mismatch —
which also subsumes the #664 null trap (0 never equals an expected id).

For each case both engines run:
  - wasmtime (oracle): matching-class calls return values; wrong-class
    calls trap ("indirect call type mismatch"); null slots trap
    ("uninitialized element"); OOB indices trap ("undefined element").
  - unicorn (synth's code, pointer region at r11 + sidecar words at
    r11+20, copied VERBATIM from the object's section): matching calls
    must equal wasmtime; wrong-class, null AND OOB indices must all stop
    AT A UDF.

Non-vacuity: a build without the type check BLXes the wrong-typed function
and returns a wrong VALUE (e.g. via2(5,1) would call $neg and yield -5),
which the harness reports as a mismatch — red, not vacuously green. A
missing null check BLXes address 0 (fault, distinguished from the
deterministic UDF); the OOB decoy is inherited from #642/#650/#664 and
seeded PAST the sidecar words.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/call_indirect_676_differential.py
Exits nonzero on any compile decline, missing sidecar, mismatch, or missed
trap.
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

WAT = Path(__file__).with_name("call_indirect_676_heterogeneous.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

CODE, TABLE, STK = 0x1000000, 0x3000000, 0x6000000
RET = CODE + 0xFFF0  # return pad (inside the CODE map)
DECOY = CODE + 0xFF00  # decoy "function" an unguarded/short-guarded build calls
X = 5
N_SLOTS = 5
SLOT_FUNCS = {0: "func_0", 1: "func_1", 2: "func_2"}  # $add $neg $sub
# Per dispatcher: index -> expected wasmtime outcome kind.
CASES = {
    "via2": {"ok": [0, 2], "type": [1], "null": [3, 4], "oob": [5, 99]},
    "via1": {"ok": [1], "type": [0, 2], "null": [3, 4], "oob": [5, 99]},
}


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


# The §4.4.8 trap reason wasmtime must report per expected category — the
# CASES table above is itself oracle-checked, not hand-trusted.
TRAP_REASON = {
    "type": "indirect call type mismatch",
    "null": "uninitialized element",
    "oob": "undefined element",
}


def wasmtime_oracle():
    """Ground truth: (export, idx) -> result or 'trap:<reason>'."""
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, WAT.read_text())
    results = {}
    for export, groups in CASES.items():
        for why, idxs in groups.items():
            for idx in idxs:
                store = wasmtime.Store(engine)  # fresh instance per call
                f = wasmtime.Instance(store, module, []).exports(store)[export]
                try:
                    results[(export, idx)] = f(store, X, idx) & 0xFFFFFFFF
                    assert why == "ok", f"{export}({X},{idx}) must trap ({why})"
                except wasmtime.Trap as t:
                    reason = TRAP_REASON[why]
                    assert reason in t.message, (
                        f"{export}({X},{idx}) must trap with '{reason}': {t.message}"
                    )
                    results[(export, idx)] = f"trap:{reason}"
    return results


def run_unicorn(text: bytes, syms: dict, sidecar: bytes, export: str, idx: int, a32: bool):
    """Execute export(X, idx); returns ('ok', r0) or ('trap-udf', pc) or a failure."""
    mu = Uc(UC_ARCH_ARM, UC_MODE_ARM if a32 else UC_MODE_THUMB)
    mu.mem_map(CODE, 0x100000)
    mu.mem_map(TABLE, 0x10000)
    mu.mem_map(STK, 0x100000)
    mu.mem_write(CODE, text)
    if a32:
        mu.mem_write(RET, struct.pack("<II", 0xE320F000, 0xE320F000))
        mu.mem_write(DECOY, struct.pack("<II", 0xE3A0005A, 0xE12FFF1E))
        thumb_bit = 0
    else:
        mu.mem_write(RET, struct.pack("<HH", 0xBF00, 0xBF00))
        mu.mem_write(DECOY, struct.pack("<HH", 0x205A, 0x4770))
        thumb_bit = 1
    # Layout contract: pointer slots at R11 (null slots ZERO, #664), the
    # type-id sidecar copied VERBATIM at R11 + N_SLOTS*4 (#676), and decoys
    # PAST the sidecar so a missing/short bounds guard "succeeds" loudly
    # with 0x5A instead of faulting (#642/#650).
    for slot in range(N_SLOTS):
        if slot in SLOT_FUNCS:
            ptr = (CODE + syms[SLOT_FUNCS[slot]]) | thumb_bit
        else:
            ptr = 0  # null funcref — the contract's zero word
        mu.mem_write(TABLE + 4 * slot, struct.pack("<I", ptr))
    mu.mem_write(TABLE + 4 * N_SLOTS, sidecar)
    for i in range(2 * N_SLOTS, 128):
        mu.mem_write(TABLE + 4 * i, struct.pack("<I", DECOY | thumb_bit))

    mu.reg_write(UC_ARM_REG_R0, X)
    mu.reg_write(UC_ARM_REG_R1, idx)
    mu.reg_write(UC_ARM_REG_R11, TABLE)
    mu.reg_write(UC_ARM_REG_SP, STK + 0x80000)
    mu.reg_write(UC_ARM_REG_LR, RET | thumb_bit)
    try:
        mu.emu_start((CODE + syms[export]) | thumb_bit, RET, count=2000)
    except UcError as e:
        pc = mu.reg_read(UC_ARM_REG_PC)
        # A deterministic §4.4.8 trap = execution stopped ON a udf
        # (Thumb 0xDExx / A32 0xE7F000F0). Anything else (e.g. a BLX to a
        # wrong-typed callee corrupting state, or to address 0) is 'fault'.
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
    elf_path = f"/tmp/ci676_{'a32' if a32 else 'thumb'}.o"
    compile_direct(elf_path, target)

    with open(elf_path, "rb") as fh:
        e = ELFFile(fh)
        text = bytes(e.get_section_by_name(".text").data())
        sidecar_sec = e.get_section_by_name(".synth.table_type_ids")
        if sidecar_sec is None:
            print("SIDECAR MISSING: no .synth.table_type_ids section (#676 red)")
            return 1
        sidecar = bytes(sidecar_sec.data())
        # Symbols from the symtab, never from disasm text (host-dependent).
        st = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
        syms = {s.name: s["st_value"] & ~1 for s in st.iter_symbols() if s.name}
    if len(sidecar) != 4 * N_SLOTS:
        print(f"SIDECAR SIZE: {len(sidecar)} bytes, want {4 * N_SLOTS} (#676 red)")
        return 1
    for need in sorted(CASES) + sorted(SLOT_FUNCS.values()):
        if need not in syms:
            print(f"SYMBOL MISSING: {need} (a decline drops the function — #676 red)")
            return 1

    isa = "A32" if a32 else "Thumb-2"
    ids = struct.unpack(f"<{N_SLOTS}I", sidecar)
    print(f"[{isa}] sidecar class ids: {list(ids)}")
    fails = 0
    for export, groups in CASES.items():
        for idx in groups["ok"]:
            want = oracle[(export, idx)]
            kind, got = run_unicorn(text, syms, sidecar, export, idx, a32)
            ok = kind == "ok" and got == want
            fails += 0 if ok else 1
            got_s = f"{got:#x}" if isinstance(got, int) else got
            print(
                f"[{isa}] {export}({X},{idx}) = {kind}:{got_s} (wasmtime: {want:#x}) "
                f"{'OK' if ok else 'MISMATCH'}"
            )
        for why in ["type", "null", "oob"]:
            for idx in groups[why]:
                want = oracle[(export, idx)]
                assert isinstance(want, str) and want.startswith("trap"), (
                    f"oracle must trap {export}({X},{idx}): {want}"
                )
                kind, got = run_unicorn(text, syms, sidecar, export, idx, a32)
                ok = kind == "trap-udf"
                fails += 0 if ok else 1
                if ok:
                    print(
                        f"[{isa}] {export}({X},{idx}) = udf trap at {got:#x} "
                        f"({why} — wasmtime: {want}) OK"
                    )
                elif kind == "ok" and got == 0x5A:
                    print(
                        f"[{isa}] {export}({X},{idx}) = {got:#x} — the DECOY past the "
                        f"region was CALLED ({why}): bounds guard missing or short MISMATCH"
                    )
                else:
                    got_s = f"{got:#x}" if isinstance(got, int) else got
                    print(
                        f"[{isa}] {export}({X},{idx}) = {kind}:{got_s} ({why} — "
                        f"wasmtime: {want}) MISMATCH — a missing type check calls the "
                        "wrong-typed function (wrong value) or BLXes address 0"
                    )
    return fails


def main() -> int:
    oracle = wasmtime_oracle()
    print(f"wasmtime oracle: {oracle}")

    # Both ISAs share the expansion: Thumb-2 (cortex-m3) and A32 (cortex-r5).
    fails = run_isa(oracle, "cortex-m3", a32=False)
    fails += run_isa(oracle, "cortex-r5", a32=True)

    if fails == 0:
        print("ORACLE: PASS")
        return 0
    print(f"ORACLE: FAIL — {fails} case(s) diverged from wasmtime (#676)")
    return 1


if __name__ == "__main__":
    sys.exit(main())
