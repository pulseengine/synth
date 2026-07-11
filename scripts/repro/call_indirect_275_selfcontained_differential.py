#!/usr/bin/env python3
"""#275 — self-contained `--cortex-m` call_indirect: LOUD-DECLINE oracle.

Companion to the #642/#650/#664/#676 EXECUTION differentials, but this one
gates outcome B (the sound interim): on the SELF-CONTAINED image path
(`build_multi_func_cortex_m_elf`, no `--relocatable`) `call_indirect` must
DECLINE LOUDLY rather than silently emit the R11-table dispatch that reads
function pointers from linear-memory DATA (a silent miscompile).

Root cause: the guarded dispatch loads the function pointer from the contiguous
R11 funcref-table region, but R11 is the LINEAR-MEMORY base and a self-contained
image has NO runtime to populate that region — so `ldr ip,[r11,idx*4]` reads
whatever linear-memory data lives at that offset. Until the dedicated
func-pointer table (silicon-gated, #275) lands, the self-contained path refuses
(AFD-008: an unlowerable op must Err, never silently continue).

This oracle asserts, using only `synth` + pyelftools (no unicorn/wasmtime):
  1. self-contained: the `entry` (call_indirect) function is LOUD-skipped (a
     `#275` diagnostic + a skip count) and is ABSENT from the ELF symtab — no
     silent colliding dispatch — while `func_1/2/3` still compile;
  2. `--relocatable`: the SAME module still emits `entry` (the host-linked path,
     where a runtime places the table region at R11, is untouched).

Run:  SYNTH=<path-to-synth> python scripts/repro/call_indirect_275_selfcontained_differential.py
Exits nonzero on a silent emit (regression) or a declined relocatable path.
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


def check_selfcontained() -> int:
    out = "/tmp/ci275_selfcontained_oracle.elf"
    r = run(["--cortex-m", "--target", "cortex-m3", "-o", out])
    fails = 0
    if r.returncode != 0:
        print(f"self-contained: compile hard-failed (expected skip-and-continue):\n{r.stderr}")
        return 1
    if "skipping function 'entry'" not in r.stderr or "#275" not in r.stderr:
        print(f"self-contained: call_indirect was NOT loud-declined (#275):\n{r.stderr}")
        fails += 1
    else:
        print("self-contained: entry LOUD-declined with a #275 diagnostic OK")
    syms = symbols(out)
    if "entry" in syms:
        print("self-contained: `entry` EMITTED — a silent colliding dispatch (regression) MISMATCH")
        fails += 1
    else:
        print("self-contained: `entry` absent from the ELF (no silent dispatch) OK")
    for f in ("func_1", "func_2", "func_3"):
        if f not in syms:
            print(f"self-contained: {f} missing — decline must be scoped to call_indirect MISMATCH")
            fails += 1
    if fails == 0:
        print("self-contained: non-call_indirect functions still compile OK")
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
    fails = check_selfcontained() + check_relocatable()
    if fails == 0:
        print("ORACLE: PASS")
        return 0
    print(f"ORACLE: FAIL — {fails} check(s) diverged (#275)")
    return 1


if __name__ == "__main__":
    sys.exit(main())
