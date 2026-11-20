#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 456
"""RQ-91-A64BELOW (#1740) — AArch64 dead code below a frame's entry height,
EXECUTED against wasmtime.

THE DEFECT. WASM validates the code after an unconditional transfer (br /
br_table / return / unreachable) against a POLYMORPHIC stack, so it may pop
values the selector's straight-line model holds for the code BENEATH the
frame (`br 1 ; drop ; drop`). The AArch64 selector lowered that dead code
against its model and popped the live values beneath out of it: a debug build
PANICKED at the join ("void frame must restore stack height"), a release build
declined with an uninformative `binop underflow`. The selector now SKIPS dead
code (nothing can reach it at runtime), so these shapes compile. It also
treats the code after a frame's `end` as dead when no live edge enters that
join (every path through the frame ended in br-outward / return /
unreachable).

THE FIXTURES. `aarch64_dead_below_1740.wat`: eleven below-entry `b_*` shapes
(the #1691 `refuse_below`, a value beneath inside the block, a dead binop, a
dead then-arm beside a live else, dead if/block/loop frames nested in the dead
code, a dead multi-value block before a live value-carrying one, after
`unreachable` and `br_table`, at i64/f32/f64), each with an `l_*` twin that is
the same function with the dead code deleted; ten of the eleven were red on
265235dc (`b_then_below_else_live` compiled and ran correctly there and stays
as a control). Seven `r_*` frames that no live edge enters: an earlier cut of
this change still lowered the code after their `end` and regressed three of
them (`r_f64_deadbr`, `r_f64_ret_br`, `r_f32_deadbr`, all correct on
265235dc) to `funop: expected FP operand, got GP`; `r_f64_plain` and
`r_f64_store` were declined on 265235dc too. Four `w_*` float frames whose
only live edge is a `br` from an inner float frame that no edge enters:
265235dc compiled three of them to SILENT WRONG CODE (it returned x0 and
never wrote d0/s0; Refs #1747) and declined `w_f64_const`. `if_arm_dead_value_1691.wat`:
the #1691 dead-arm shapes, which never ran on AArch64 before, executed here so
the skip is checked on every dead-value shape the ARM lane collected. Its two
`br_table` exports carry a value through the table and are loud-declined by
name (VCR-A64-CF-001); that decline set is checked EXACTLY.

EXECUTION. Each export is compiled on its own (`-b aarch64 --func-name X
--relocatable`); every compiled export is called with x in {0, 1, 5, 7} in
two machine states (caller-saved x/v registers zeroed, and filled from a
seeded RNG) under unicorn, and compared BIT-EXACT with wasmtime: same value,
or a trap on both sides (`brk`). The floor is derived from the fixtures and
checked against the header before anything runs.

RED on 265235dc (debug): 37 failures, 344 of 456 emulations — 7 panics
(exit 101: six `b_*` and the #1691 `refuse_below`), 7 declines
(`b_dead_frames` drop underflow, `b_ordinal_after` multi-value block type,
`b_after_unreachable` and `b_after_br_table` binop underflow, `r_f64_plain`
and `w_f64_const` funop, `r_f64_store` local.set operand class), and 23 WRONG
VALUES from `w_f32_conv`, `w_f64_if` and `w_f32_ret_tail` (exit 0; the one
call that matched returns 0.0 by coincidence). GREEN after -> RESULT: PASS.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/oracle_run.py \\
      scripts/repro/aarch64_dead_below_1740_differential.py
"""
import os
import random
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM64, UC_MODE_ARM, Uc, UcError
from unicorn import arm64_const as A

HERE = Path(__file__).resolve().parent
FIXTURES = {
    "1740": (HERE / "aarch64_dead_below_1740.wat", set()),
    "1691": (HERE / "if_arm_dead_value_1691.wat", {"t_i32_br_table", "t_f32_br_table"}),
}
DECLINE_TEXT = "br_table with VALUE-CARRYING targets"
SYNTH = os.environ.get("SYNTH") or os.environ.get("SYNTH_BIN", "./target/debug/synth")

XS = (0, 1, 5, 7)
STATES = ("zeroed", "garbage")
CODE, STK, RET = 0x100000, 0x200000, 0x300000
M32, M64 = (1 << 32) - 1, (1 << 64) - 1


def exports(wat):
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, wat.read_text())
    return [(e.name, str(e.type.results[0])) for e in mod.exports]


def expected_emulations():
    n = 0
    for wat, declined in FIXTURES.values():
        n += sum(1 for name, _ in exports(wat) if name not in declined)
    return n * len(XS) * len(STATES)


def declared_floor():
    m = re.search(r"^# ci-checks: emulations >= (\d+)$", Path(__file__).read_text(), re.M)
    if not m:
        sys.exit("REFUSE: no `# ci-checks: emulations >= N` header in this file")
    return int(m.group(1))


def bits(v, ty):
    if ty == "i32":
        return v & M32
    if ty == "i64":
        return v & M64
    if ty == "f32":
        return struct.unpack("<I", struct.pack("<f", v))[0]
    return struct.unpack("<Q", struct.pack("<d", v))[0]


def reference(wat, ex):
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, wat.read_text())
    out = {}
    for name, ty in ex:
        for x in XS:
            store = wasmtime.Store(eng)
            inst = wasmtime.Instance(store, mod, [])
            try:
                out[(name, x)] = ("ok", bits(inst.exports(store)[name](store, x), ty))
            except wasmtime.Trap:
                out[(name, x)] = ("trap",)
    return out


def compile_export(wat, name, tmp):
    """(text, symbol offset) | ("declined", message) | ("error", message).

    One object per export (`--func-name`): `--all-exports` exits non-zero when
    any export is declined (#952), which would hide the per-export verdicts."""
    obj = Path(tmp) / f"{wat.stem}.{name}.o"
    r = subprocess.run(
        [SYNTH, "compile", str(wat), "-b", "aarch64", "--func-name", name,
         "--relocatable", "-o", str(obj)],
        capture_output=True, text=True,
    )
    if r.returncode != 0:
        lines = [ln for ln in r.stderr.splitlines() if "panicked" in ln or "Error" in ln]
        msg = (lines or r.stderr.splitlines()[-1:] or ["?"])[0][:240]
        kind = "declined" if r.returncode == 1 and "panicked" not in r.stderr else "error"
        return kind, f"exit {r.returncode}: {msg}"
    elf = ELFFile(open(obj, "rb"))
    text = elf.get_section_by_name(".text").data()
    syms = {s.name: s["st_value"] for s in elf.get_section_by_name(".symtab").iter_symbols()}
    if name not in syms:
        return "error", "no symbol for the export in the object"
    return text, syms[name]


def run(text, off, x, ty, state, rng):
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, text)
    if state == "garbage":
        for r in range(1, 18):  # x1..x17 (x0 is the argument)
            mu.reg_write(getattr(A, f"UC_ARM64_REG_X{r}"), rng.getrandbits(64))
        for r in range(0, 8):
            mu.reg_write(getattr(A, f"UC_ARM64_REG_D{r}"), rng.getrandbits(64))
    mu.reg_write(A.UC_ARM64_REG_SP, STK)
    mu.reg_write(A.UC_ARM64_REG_LR, RET)
    mu.reg_write(A.UC_ARM64_REG_X0, x)
    try:
        mu.emu_start(CODE + off, RET, count=100000)
    except UcError:
        return ("trap",)
    if mu.reg_read(A.UC_ARM64_REG_PC) != RET:
        return ("did-not-return",)
    if ty == "i32":
        return ("ok", mu.reg_read(A.UC_ARM64_REG_X0) & M32)
    if ty == "i64":
        return ("ok", mu.reg_read(A.UC_ARM64_REG_X0) & M64)
    if ty == "f32":
        return ("ok", mu.reg_read(A.UC_ARM64_REG_S0) & M32)
    return ("ok", mu.reg_read(A.UC_ARM64_REG_D0) & M64)


def main():
    want_n = expected_emulations()
    floor = declared_floor()
    if want_n != floor:
        sys.exit(f"REFUSE: derived emulation count {want_n} != header floor {floor}")
    fails, n = [], 0
    rng = random.Random(1740)
    with tempfile.TemporaryDirectory() as tmp:
        for tag, (wat, declined) in FIXTURES.items():
            ex = exports(wat)
            ref = reference(wat, ex)
            seen_declined = set()
            for name, ty in ex:
                text, off = compile_export(wat, name, tmp)
                if text == "declined" and name in declined and DECLINE_TEXT in off:
                    seen_declined.add(name)
                    continue
                if isinstance(text, str):
                    fails.append(f"[{tag}] {name}: {text}: {off}")
                    continue
                if name in declined:
                    fails.append(f"[{tag}] {name}: compiled, but is pinned as declined")
                    continue
                for state in STATES:
                    for x in XS:
                        n += 1
                        g = run(text, off, x, ty, state, rng)
                        w = ref[(name, x)]
                        if g != w:
                            fails.append(f"[{tag}] {name}({x}) {state}: got {g} want {w}")
            if seen_declined != declined:
                fails.append(f"[{tag}] declined {sorted(seen_declined)} != {sorted(declined)}")
    for f in fails[:40]:
        print("MISMATCH", f)
    print(f"ORACLE-EVIDENCE emulations={n} expected={want_n} failures={len(fails)}")
    if fails or n != want_n:
        print("RESULT: FAIL")
        sys.exit(1)
    print("RESULT: PASS")


if __name__ == "__main__":
    main()
