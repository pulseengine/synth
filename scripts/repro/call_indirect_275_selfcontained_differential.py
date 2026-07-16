#!/usr/bin/env python3
"""#275 — self-contained call_indirect: emission + residual-decline oracle.

The v0.42 #717 interim (loud-decline on the whole self-contained path) was
CONVERTED in v0.47: the Thumb-2 `--cortex-m` image path now lowers
`call_indirect` through a flash-resident funcref table addressed PC-RELATIVE
(an `LdrSym` literal against `__synth_func_table`, patched post-layout) —
never via R11, the linear-memory base the #717 collision corrupted. Execution
(incl. every §4.4.8 trap) is gated by the companion
`call_indirect_275_selfcontained_execution_differential.py`.

This oracle asserts, using only `synth` + pyelftools (no unicorn/wasmtime):
  1. self-contained `--cortex-m` (Thumb-2): the `entry` (call_indirect)
     function now EMITS — with the `#275 funcref table` diagnostic — and the
     non-call_indirect functions still compile;
  2. RESIDUAL DECLINE — A32/Cortex-R5 self-contained (no `--relocatable`, not
     the cortex-m image builder): `call_indirect` still LOUD-declines with a
     `#275` diagnostic and `entry` stays ABSENT (the flash-table lowering is
     Thumb-2 `--cortex-m` only; anything else would be the silent R11
     collision);
  3. `--relocatable`: the SAME module still emits `entry` on both Thumb-2 and
     A32 (the host-linked path, where a runtime places the table region at
     R11, is untouched).

Run:  SYNTH=<path-to-synth> python scripts/repro/call_indirect_275_selfcontained_differential.py
Exits nonzero on a self-contained cortex-m decline (regression to #717), a
SILENT emit on the residual A32 path, or a declined relocatable path.
"""

import os
import subprocess
import sys
from pathlib import Path

from elftools.elf.elffile import ELFFile

WAT = Path(__file__).with_name("call_indirect_275_selfcontained.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")


def symbols(elf_path: str) -> set:
    with open(elf_path, "rb") as fh:
        e = ELFFile(fh)
        st = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"]
        if not st:
            return set()
        return {s.name for s in st[0].iter_symbols() if s.name}


def run(args):
    return subprocess.run([SYNTH, "compile", str(WAT), *args], capture_output=True, text=True)


def check_selfcontained_cortex_m() -> int:
    """#275 converted: the Thumb-2 cortex-m image EMITS the dispatch."""
    out = "/tmp/ci275_selfcontained_oracle.elf"
    r = run(["--cortex-m", "--target", "cortex-m3", "-o", out])
    fails = 0
    if r.returncode != 0:
        print(f"self-contained cortex-m: compile failed:\n{r.stderr}")
        return 1
    if "skipping function 'entry'" in r.stderr:
        print("self-contained cortex-m: entry LOUD-declined — regression to the "
              f"#717 interim MISMATCH:\n{r.stderr}")
        fails += 1
    if "#275 funcref table" not in r.stdout + r.stderr:
        print("self-contained cortex-m: no funcref-table diagnostic — the "
              f"flash table was not emitted MISMATCH:\n{r.stdout}\n{r.stderr}")
        fails += 1
    syms = symbols(out)
    for f in ("entry", "func_1", "func_2", "func_3"):
        if f not in syms:
            print(f"self-contained cortex-m: {f} missing from the image MISMATCH")
            fails += 1
    if fails == 0:
        print("self-contained cortex-m: entry emits the flash-table dispatch "
              "(+ funcref table) OK")
    return fails


def check_selfcontained_a32_residual() -> int:
    """The RESIDUAL decline: A32/Cortex-R5 self-contained must still refuse —
    its builder emits no funcref table, so a dispatch would be the #717 R11
    collision (a silent miscompile)."""
    out = "/tmp/ci275_selfcontained_r5.elf"
    r = run(["--target", "cortex-r5", "-o", out])
    fails = 0
    if r.returncode != 0:
        print(f"self-contained cortex-r5: compile hard-failed (expected skip-and-continue):\n{r.stderr}")
        return 1
    if "skipping function 'entry'" not in r.stderr or "#275" not in r.stderr:
        print("self-contained cortex-r5: call_indirect was NOT loud-declined — "
              f"a silent R11 collision (#275) MISMATCH:\n{r.stderr}")
        fails += 1
    elif "entry" in symbols(out):
        print("self-contained cortex-r5: `entry` EMITTED — silent colliding dispatch MISMATCH")
        fails += 1
    else:
        print("self-contained cortex-r5: residual LOUD decline (A32 has no "
              "flash-table lowering yet) OK")
    return fails


def check_relocatable() -> int:
    fails = 0
    for target in ("cortex-m3", "cortex-r5"):
        out = f"/tmp/ci275_reloc_oracle_{target}.o"
        r = run(["--target", target, "--all-exports", "--relocatable", "--no-optimize", "-o", out])
        if r.returncode != 0:
            print(f"relocatable ({target}): compile failed:\n{r.stderr}")
            fails += 1
            continue
        if "skipping function 'entry'" in r.stderr:
            print(f"relocatable ({target}): entry declined — #275 must NOT touch this path MISMATCH")
            fails += 1
            continue
        if "entry" not in symbols(out):
            print(f"relocatable ({target}): `entry` missing — dispatch dropped MISMATCH")
            fails += 1
            continue
        print(f"relocatable ({target}): `entry` still emits its guarded dispatch OK")
    return fails


def main() -> int:
    fails = (
        check_selfcontained_cortex_m()
        + check_selfcontained_a32_residual()
        + check_relocatable()
    )
    if fails == 0:
        print("ORACLE: PASS")
        return 0
    print(f"ORACLE: FAIL — {fails} check(s) diverged (#275)")
    return 1


if __name__ == "__main__":
    sys.exit(main())
