#!/usr/bin/env python3
# NOTE on home: this lives in scripts/ (with claim_check.py and
# tier_census_1021.py — derivation/audit tooling over shipped artifacts), not
# scripts/repro/ (defect oracles). It is RQ-62-EMBEDDER's executable
# derivation of docs/embedder-abi-relocatable-arm.md: it compiles a real
# module on the --relocatable path and asserts every register fact the
# document states against the EMITTED BYTES. The claims.yaml claim
# SYNTH-EMBEDDER-ABI-RELOCATABLE-1131 is the CI-enforced doc<->source
# binding; this script is the byte-level cross-check (manual/on-demand —
# needs a built synth binary plus pyelftools and capstone).
"""RQ-62-EMBEDDER (#1131) — the --relocatable embedder ABI, asserted on bytes.

Facts asserted (each is a stated sentence in
docs/embedder-abi-relocatable-arm.md):

  1. The symbol table is found by SHT_SYMTAB section TYPE (the ARM builder
     names its symtab with an EMPTY name; get_section_by_name returns None).
  2. Every relocation is a call relocation (R_ARM_THM_CALL) — no data
     relocation supplies any base; bases arrive in registers.
  3. Memory-0 accesses go through R11/fp ([fp, ip] / [fp, #imm]).
  4. Globals go through R9/sb at the #643 summed-width offsets: with globals
     (i32, i64, i32) the i64 pair sits at [sb,#4]/[sb,#8] and the third
     global at [sb,#0xc].
  5. memory.size is LSR rd, sl(R10), #16 — R10 holds the size in BYTES.
  6. No emitted instruction WRITES r9/sb, sl/r10, or fp/r11 (the reserved
     set; the #1021 clobber class).
  7. The prologue's saved set is a subset of {r4-r8, lr} — R9/R10/R11 are
     never pushed/popped, so the embedder's values survive by never being
     touched, not by save/restore.
  8. Under --safety-bounds software the per-access guard READS sl/R10 (the
     size register is load-bearing there, not informational).

Usage:
    SYNTH=./target/debug/synth python3 scripts/embedder_abi_audit_1131.py
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from pathlib import Path

from capstone import CS_ARCH_ARM, CS_MODE_THUMB, Cs
from elftools.elf.elffile import ELFFile

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

R_ARM_THM_CALL = 10

WAT = """
(module
  (memory 1)
  (global $g0 (mut i32) (i32.const 8192))
  (global $g1 (mut i64) (i64.const 77))
  (global $g2 (mut i32) (i32.const 17825))
  (data (i32.const 16) "\\01\\02\\03\\04")
  (func $helper (param i32) (result i32)
    local.get 0
    i32.const 1
    i32.add)
  (func (export "run") (param i32) (result i32)
    local.get 0
    i32.load offset=16
    global.get $g0
    i32.add
    global.get $g2
    i32.add
    call $helper
    memory.size
    i32.add)
  (func (export "setg") (param i32)
    local.get 0
    global.set $g0
    i32.const 0
    i64.extend_i32_u
    global.set $g1)
  (func (export "st") (param i32 i32)
    local.get 0
    local.get 1
    i32.store offset=8)
)
"""

# Capstone spells R9 "sb", R10 "sl", R11 "fp", R12 "ip".
RESERVED = {"sb", "r9", "sl", "r10", "fp", "r11"}
PROLOGUE_ALLOWED = {"r4", "r5", "r6", "r7", "r8", "lr", "pc"}


def compile_obj(wat_path: Path, out: Path, extra: list[str]) -> None:
    cmd = [
        SYNTH,
        "compile",
        str(wat_path),
        "-o",
        str(out),
        "-t",
        "thumbv7em-none-eabi",
        "--relocatable",
        "--embedder-data-init",
        "--embedder-global-init",
        *extra,
    ]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"FAIL: compile exited {r.returncode}:\n{r.stderr}")


def load(path: Path):
    elf = ELFFile(open(path, "rb"))
    symtab = None
    for sec in elf.iter_sections():
        if sec["sh_type"] == "SHT_SYMTAB":
            symtab = sec  # fact 1: by TYPE, never by name
            break
    if symtab is None:
        sys.exit("FAIL: no SHT_SYMTAB section (fact 1)")
    text = next(s for s in elf.iter_sections() if s.name == ".text")
    funcs = sorted(
        {
            (s.name, s["st_value"] & ~1, s["st_size"])
            for s in symtab.iter_symbols()
            if s["st_info"]["type"] == "STT_FUNC"
        },
        key=lambda t: t[1],
    )
    relocs = []
    for sec in elf.iter_sections():
        if sec["sh_type"] in ("SHT_REL", "SHT_RELA"):
            relocs.extend(r["r_info_type"] for r in sec.iter_relocations())
    return text.data(), funcs, relocs


def disasm(data: bytes, off: int, size: int):
    md = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    md.detail = True
    return list(md.disasm(data[off : off + size], off))


def main() -> None:
    tmp = Path(tempfile.mkdtemp(prefix="embedder_abi_1131_"))
    wat = tmp / "contract.wat"
    wat.write_text(WAT)
    obj = tmp / "contract.o"
    obj_sw = tmp / "contract_sw.o"
    compile_obj(wat, obj, [])
    compile_obj(wat, obj_sw, ["--safety-bounds", "software"])

    data, funcs, relocs = load(obj)
    failures: list[str] = []

    # fact 2: only call relocations.
    bad = [t for t in relocs if t != R_ARM_THM_CALL]
    if bad:
        failures.append(f"fact 2: non-call relocation types {bad}")

    seen = {
        "fp_access": False,
        "sb_pair": set(),
        "memsize": False,
    }
    for name, off, size in funcs:
        for insn in disasm(data, off, size):
            _, regs_write = insn.regs_access()
            wr = {insn.reg_name(r) for r in regs_write}
            hit = wr & RESERVED
            if hit:
                failures.append(
                    f"fact 6: {name}@{insn.address:#x} `{insn.mnemonic} "
                    f"{insn.op_str}` WRITES reserved {sorted(hit)}"
                )
            if insn.mnemonic in ("push", "push.w", "pop", "pop.w"):
                regs = {r.strip() for r in insn.op_str.strip("{}").split(",")}
                extra = regs - PROLOGUE_ALLOWED
                if extra:
                    failures.append(
                        f"fact 7: {name}@{insn.address:#x} saves/restores "
                        f"{sorted(extra)} beyond {{r4-r8, lr}}"
                    )
            ops = insn.op_str
            if "[fp" in ops:
                seen["fp_access"] = True
            if "[sb" in ops:
                # collect the immediate offsets used against R9
                imm = ops.split("[sb")[1]
                seen["sb_pair"].add(imm.split("]")[0])
            if insn.mnemonic.startswith("lsr") and ops.startswith(
                ("r0, sl", "r1, sl", "r2, sl", "r3, sl", "r4, sl", "r5, sl",
                 "r6, sl", "r7, sl", "r8, sl")
            ) and ops.endswith("#0x10"):
                seen["memsize"] = True

    if not seen["fp_access"]:
        failures.append("fact 3: no [fp, ...] linear-memory access emitted")
    for want in (", #4", ", #8", ", #0xc"):
        if want not in seen["sb_pair"]:
            failures.append(
                f"fact 4: expected a [sb{want}] globals access "
                f"(#643 summed-width layout); saw {sorted(seen['sb_pair'])}"
            )
    if not seen["memsize"]:
        failures.append("fact 5: no `lsr rd, sl, #0x10` memory.size emission")

    # fact 8: the software-bounds variant must READ sl in a guard compare.
    data_sw, funcs_sw, _ = load(obj_sw)
    guard_reads_sl = False
    for name, off, size in funcs_sw:
        for insn in disasm(data_sw, off, size):
            if insn.mnemonic.startswith(("cmp", "sub")) and "sl" in insn.op_str:
                guard_reads_sl = True
    if not guard_reads_sl:
        failures.append(
            "fact 8: --safety-bounds software emitted no guard reading sl/R10"
        )

    if failures:
        print("RESULT: FAIL")
        for f in failures:
            print("  " + f)
        sys.exit(1)
    print(
        f"RESULT: PASS — {len(funcs)} functions audited; reserved-register "
        f"writes: 0; relocs all R_ARM_THM_CALL ({len(relocs)}); "
        f"globals offsets {sorted(seen['sb_pair'])}"
    )


if __name__ == "__main__":
    main()
