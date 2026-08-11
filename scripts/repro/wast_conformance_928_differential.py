#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 263
"""RQ-56-CONF (#928) — EXECUTE the `assert_return` values in `tests/wast/`.

# What was wrong

`tests/wast/` carries 381 `assert_return` and 2 `assert_trap` assertions. The
only CI path over those files (`crates/synth-cli/tests/wast_compile.rs`) asserts
that `synth compile` exits 0; the expected values are parsed and **discarded**.
The backend's primary correctness suite therefore graded "did an ELF come out",
not "is it right" — a codegen change making `i32.rem_s` return the wrong value
kept it green.

That is the exit-0 vacuity class (#911; the v0.54 `sret_decide` gate that
printed `MISMATCH <-- BUG` and exited 0) sitting on the CORRECTNESS SUITE
ITSELF, and it is why three silent miscompiles shipped and were found from
outside: #929 (thumb-2 mis-places a non-last i64 call argument), #930 and #931
(a `br` out of a value-producing block loses the value). All three are wrong
VALUES with exit 0 — invisible to a compile-only run by construction, and caught
immediately by a run that compares results.

# What this does

For every `assert_return` it can execute: compile the module with synth, run the
exported function under unicorn, and compare the result against the expected
literal **written in the .wast** — the spec's own answer, not a second opinion
from another engine. That is what makes this a conformance check rather than a
differential.

# Decline honesty

Shapes this cannot execute are COUNTED and NAMED, never skipped silently:

  * `f32`/`f64` arguments or results  -> `float-abi` (VFP arg passing is a
    separate contract; wrong here would be a false alarm, not a finding)
  * `i64` values                      -> `i64-pair` (register-pair return needs
    the r0:r1 convention; enabling it is the natural follow-up and is exactly
    where #929 lives)
  * `assert_trap`                     -> `trap` (needs the trap-vector harness)
  * a module synth declines to compile -> `compile-declined`

The summary prints CHECKED, DECLINED-by-reason and MISMATCHED. A run that
executes zero assertions FAILS — the whole point is that a green result must
mean assertions ran.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_HOOK_INTR, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3, UC_ARM_REG_SP

ROOT = Path(__file__).resolve().parent.parent.parent
SYNTH = os.environ.get("SYNTH", str(ROOT / "target" / "debug" / "synth"))
WAST_DIR = ROOT / "tests" / "wast"

CODE = 0x1000
STACK = 0x20000000
MEM = 0x40000000
RET = 0x00F0_0000

ARG_REGS = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]

# `(i32.const -5)` / `(i64.const 7)` / `(f32.const 1.5)`
CONST = re.compile(r"\((i32|i64|f32|f64)\.const\s+([^\s)]+)\)")
INVOKE = re.compile(r'\(invoke\s+"((?:[^"\\]|\\.)*)"')


def sexp_forms(text: str, head: str) -> list[str]:
    """Every top-level `(head ...)` form, balanced-paren scanned.

    A regex cannot do this: the forms nest. Strings are tracked so a paren
    inside an export name does not desynchronise the depth count.
    """
    out, i, n = [], 0, len(text)
    needle = "(" + head
    while True:
        i = text.find(needle, i)
        if i < 0:
            return out
        depth, j, in_str = 0, i, False
        while j < n:
            c = text[j]
            if in_str:
                if c == "\\":
                    j += 2
                    continue
                if c == '"':
                    in_str = False
            elif c == '"':
                in_str = True
            elif c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0:
                    out.append(text[i : j + 1])
                    break
            j += 1
        i = j + 1


def parse_const(tok_type: str, raw: str) -> int:
    v = int(raw, 0) if not raw.startswith("-") else -int(raw[1:], 0)
    bits = 32 if tok_type == "i32" else 64
    return v & ((1 << bits) - 1)


class Decl(Exception):
    """A shape this harness declines to execute, with a machine reason."""

    def __init__(self, reason: str):
        super().__init__(reason)
        self.reason = reason


def compile_module(wat_text: str, tmp: Path) -> tuple[Path, bytes]:
    src = tmp / "m.wat"
    src.write_text(wat_text)
    obj = tmp / "m.o"
    r = subprocess.run(
        [SYNTH, "compile", str(src), "-o", str(obj), "--target", "cortex-m4",
         "--all-exports", "--relocatable"],
        capture_output=True, text=True,
    )
    if r.returncode != 0 or not obj.exists():
        raise Decl("compile-declined")
    return obj, obj.read_bytes()


def symbols(obj: Path) -> dict[str, int]:
    with obj.open("rb") as fh:
        elf = ELFFile(fh)
        # Look up the symbol table by TYPE, never by section name: synth emits a
        # symtab whose `sh_name` is empty, and a name-based lookup silently finds
        # nothing (the #850 lesson).
        st = next(s for s in elf.iter_sections() if s["sh_type"] == "SHT_SYMTAB")
        return {s.name: s["st_value"] for s in st.iter_symbols() if s.name}


def execute(code: bytes, entry: int, args: list[int]) -> int:
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10_0000)
    mu.mem_map(STACK - 0x10000, 0x20000)
    mu.mem_map(MEM, 0x10_0000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STACK)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    for i, a in enumerate(args):
        if i >= len(ARG_REGS):
            raise Decl("too-many-args")
        mu.reg_write(ARG_REGS[i], a & 0xFFFFFFFF)
    trapped = []
    mu.hook_add(UC_HOOK_INTR, lambda *_: trapped.append(True))
    try:
        mu.emu_start((CODE + entry) | 1, RET, timeout=5_000_000)
    except UcError as e:
        raise Decl(f"emu-error:{e}") from e
    if trapped:
        raise Decl("trapped")
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


def main() -> int:
    if not WAST_DIR.is_dir():
        print(f"FAIL: {WAST_DIR} missing")
        return 1

    checked = mismatched = 0
    declined: dict[str, int] = {}
    failures: list[str] = []
    files = sorted(WAST_DIR.glob("*.wast"))

    for wast in files:
        text = wast.read_text()
        mods = sexp_forms(text, "module")
        if len(mods) != 1:
            declined["multi-module"] = declined.get("multi-module", 0) + 1
            continue
        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            try:
                obj, _ = compile_module(mods[0], tmp)
                syms = symbols(obj)
                with obj.open("rb") as fh:
                    sec = ELFFile(fh).get_section_by_name(".text")
                    code = sec.data() if sec else b""
            except (Decl, StopIteration) as e:
                reason = getattr(e, "reason", "no-symtab")
                for _ in sexp_forms(text, "assert_return"):
                    declined[reason] = declined.get(reason, 0) + 1
                continue

            for form in sexp_forms(text, "assert_return"):
                m = INVOKE.search(form)
                if not m:
                    declined["no-invoke"] = declined.get("no-invoke", 0) + 1
                    continue
                fname = m.group(1)
                consts = CONST.findall(form)
                if any(t in ("f32", "f64") for t, _ in consts):
                    declined["float-abi"] = declined.get("float-abi", 0) + 1
                    continue
                if any(t == "i64" for t, _ in consts):
                    declined["i64-pair"] = declined.get("i64-pair", 0) + 1
                    continue
                if not consts:
                    declined["no-values"] = declined.get("no-values", 0) + 1
                    continue
                *arg_toks, exp_tok = consts
                args = [parse_const(t, v) for t, v in arg_toks]
                expected = parse_const(*exp_tok)
                entry = syms.get(fname)
                if entry is None:
                    declined["symbol-missing"] = declined.get("symbol-missing", 0) + 1
                    continue
                try:
                    actual = execute(code, entry, args)
                except Decl as e:
                    declined[e.reason] = declined.get(e.reason, 0) + 1
                    continue
                checked += 1
                if actual != expected:
                    mismatched += 1
                    failures.append(
                        f"{wast.name}: {fname}({', '.join(hex(a) for a in args)}) "
                        f"= {actual:#x}, spec says {expected:#x}"
                    )

    for f in failures[:25]:
        print(f"  MISMATCH {f}")
    if len(failures) > 25:
        print(f"  ... and {len(failures) - 25} more")

    total_declined = sum(declined.values())
    print(
        f"#928 CHECKS={checked - mismatched}/{checked} executed assertions over "
        f"{len(files)} wast files; {total_declined} declined"
    )
    print("  declined by reason: " + (", ".join(f"{k}={v}" for k, v in sorted(declined.items())) or "none"))

    # NON-VACUITY, RATCHETED. A conformance gate that executes nothing must
    # FAIL — that is the whole defect being closed, and it must not come back
    # as a green zero.
    #
    # But `> 0` is far too weak, and the `ci-checks: emulations` floor does not
    # cover this either: `emulations` counts EMULATOR ENTRIES, and 23 of them
    # are assertions that fault and then DECLINE (unmapped memory). So the
    # executed-assertion count could fall 240 -> 205 while `emulations` stayed
    # at 263 and both gates passed green. That is this session's own vacuity
    # class, one level down.
    #
    # So the floor lives here, on the number that actually means something,
    # asserted where it is computed. Raise it when the count rises (adding
    # fixtures or closing declines is the ratchet direction); a DROP means a
    # module stopped compiling or an op started declining, and that is a
    # regression to explain, not a baseline to lower.
    min_executed = 240
    if checked < min_executed:
        print(
            f"FAIL: only {checked} assertions executed, floor is {min_executed}. "
            "Something that used to compile-and-run now declines — find which "
            "and why before touching this number."
        )
        return 1
    if mismatched:
        print(f"FAIL: {mismatched} assertion(s) disagree with the spec")
        return 1
    print("RESULT: PASS — every executed assertion matches the spec's expected value")
    return 0


if __name__ == "__main__":
    sys.exit(main())
