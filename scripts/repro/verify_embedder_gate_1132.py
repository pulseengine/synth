#!/usr/bin/env python3
# ci-status: wired
# ci-checks: stdout /^1132 CHECKS=(\d+)\/9$/ >= 9
"""RQ-62-VERIFYEMBED (#1132) — `synth verify-embedder`, red-first both ways.

The embedder side of the --relocatable ARM register contract (R9 globals
base, R10 linmem size, R11 linmem base — docs/embedder-abi-relocatable-arm.md)
got a mechanical check in `synth verify-embedder <elf>`. This gate proves the
check DISCRIMINATES — it is negative-controlled in both directions on every
run, because a check nobody has seen reject is not a check:

  RED  — a deliberately clobbering object (assembled fresh from .s with the
         real ARM toolchain: direct `mov r11, r0`, `ldr r9, [r0]`, the jess
         luck-2 frame shape `push/pop {r11}`, and post-index writeback
         `str r0, [r10], #4`) must REFUSE with exactly the pinned write count
         and name every one of the three reserved registers.
  RED  — a conforming shim linked beside its own boot code must refuse when
         the establishment site is NOT acknowledged, and a misspelled
         `--allow-writer` must refuse rather than silently waive nothing.
  GREEN— the same image with `--allow-writer boot_entry` passes and reports
         the acknowledgement; synth's own Thumb-2 AND A32 --relocatable
         objects pass with a nonzero instruction count (the non-vacuity
         floor: "0 instructions scanned" is a refusal, not a pass).

Needs: a built synth ($SYNTH, default ./target/debug/synth) and ARM binutils
(arm-none-eabi-as + arm-none-eabi-objdump; llvm-objdump works for the
subcommand itself, but the clobber fixtures are assembled here from .s so the
gate checks real toolchain output, not synthetic ELF bytes).
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
AS = os.environ.get("ARM_AS", "arm-none-eabi-as")

CLOBBER_S = """\
\t.syntax unified
\t.cpu cortex-m7
\t.thumb
\t.text
\t.global bad_mov
\t.thumb_func
bad_mov:
\tmov\tr11, r0
\tbx\tlr
\t.global bad_load
\t.thumb_func
bad_load:
\tldr\tr9, [r0]
\tbx\tlr
\t.global bad_frame
\t.thumb_func
bad_frame:
\tpush\t{r11, lr}
\tmov\tr11, sp
\tmovs\tr0, #0
\tpop\t{r11, pc}
\t.global bad_writeback
\t.thumb_func
bad_writeback:
\tstr\tr0, [r10], #4
\tbx\tlr
"""

# A conforming shim (reads through the contract registers — the contract
# itself) plus the establishment site that legitimately writes them.
CONFORM_S = """\
\t.syntax unified
\t.cpu cortex-m7
\t.thumb
\t.text
\t.global good_shim
\t.thumb_func
good_shim:
\tpush\t{r4, lr}
\tldr\tr0, [r11, r0]
\tldr\tr1, [r9]
\tmov\tr3, r10
\tadd\tr0, r0, r1
\tpop\t{r4, pc}
\t.global boot_entry
\t.thumb_func
boot_entry:
\tldr\tr11, =0x20000000
\tldr\tr10, =0x10000
\tldr\tr9, =0x20010100
\tbx\tlr
"""

WAT = """\
(module
  (memory 1)
  (global $g0 (mut i32) (i32.const 8192))
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
    call $helper
    memory.size
    i32.add)
)
"""

# The clobber fixture's write set, pinned EXACTLY (not >=): 4 functions, 5
# refused lines (bad_frame contributes two — the frame-pointer mov AND the
# restoring pop, both real writes). A drift in either direction is a finding.
EXPECT_CLOBBER_WRITES = 5

passed = 0
failed: list[str] = []


def check(name: str, ok: bool, detail: str = "") -> None:
    global passed
    if ok:
        passed += 1
        print(f"  ok  {name}")
    else:
        failed.append(name)
        print(f"  FAIL {name}: {detail}")


def run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(list(args), capture_output=True, text=True)


def main() -> None:
    tmp = Path(tempfile.mkdtemp(prefix="verify_embedder_1132_"))
    clobber_s = tmp / "clobber.s"
    conform_s = tmp / "conform.s"
    clobber_s.write_text(CLOBBER_S)
    conform_s.write_text(CONFORM_S)
    clobber_o = tmp / "clobber.o"
    conform_o = tmp / "conform.o"
    for src, obj in ((clobber_s, clobber_o), (conform_s, conform_o)):
        r = run(AS, "-mcpu=cortex-m7", "-mthumb", str(src), "-o", str(obj))
        if r.returncode != 0:
            sys.exit(f"FAIL: {AS} could not assemble {src.name}:\n{r.stderr}")

    # 1. RED: the clobbering object refuses.
    r = run(SYNTH, "verify-embedder", str(clobber_o))
    check("clobber object REFUSED", r.returncode != 0, f"exit {r.returncode}")

    # 2. RED precision: exactly the pinned write count, and each reserved
    #    register named at least once — the check discriminates by register,
    #    not just by exit code.
    m = re.search(r"(\d+) write\(s\) to reserved registers", r.stderr)
    check(
        f"refusal counts exactly {EXPECT_CLOBBER_WRITES} writes",
        m is not None and int(m.group(1)) == EXPECT_CLOBBER_WRITES,
        f"stderr: {r.stderr[:300]}",
    )
    named = {reg for reg in ("r9", "r10", "r11") if f"[{reg}]" in r.stderr}
    check(
        "all three reserved registers named in the refusal",
        named == {"r9", "r10", "r11"},
        f"named only {sorted(named)}",
    )

    # 3. RED: the conforming image WITHOUT acknowledging its boot code
    #    refuses (the establishment writes are real writes).
    r = run(SYNTH, "verify-embedder", str(conform_o))
    check("unacknowledged establishment site REFUSED", r.returncode != 0)

    # 4. RED: a misspelled --allow-writer refuses (waives nothing silently).
    r = run(SYNTH, "verify-embedder", str(conform_o), "--allow-writer", "boot_entryy")
    check(
        "misspelled --allow-writer REFUSED",
        r.returncode != 0 and "no symbol of that name" in (r.stderr + r.stdout),
        f"exit {r.returncode}",
    )

    # 5. GREEN: acknowledged, the same image passes and reports it.
    r = run(SYNTH, "verify-embedder", str(conform_o), "--allow-writer", "boot_entry")
    check(
        "acknowledged establishment site ACCEPTED",
        r.returncode == 0 and "acknowledged (--allow-writer): boot_entry" in r.stdout,
        f"exit {r.returncode}: {r.stderr[:200]}",
    )

    # 6+7. GREEN: synth's own --relocatable output passes on BOTH ISAs, with
    #      a nonzero instruction count (non-vacuity: the floor exists in the
    #      subcommand; here we assert the count is visible and > 0).
    wat = tmp / "contract.wat"
    wat.write_text(WAT)
    for name, target_args in (
        ("thumb2", ["-t", "thumbv7em-none-eabi"]),
        ("a32", ["--target", "cortex-r5"]),
    ):
        obj = tmp / f"contract_{name}.o"
        r = run(
            SYNTH,
            "compile",
            str(wat),
            "-o",
            str(obj),
            *target_args,
            "--relocatable",
            "--embedder-data-init",
            "--embedder-global-init",
        )
        if r.returncode != 0:
            sys.exit(f"FAIL: synth compile ({name}) exited {r.returncode}:\n{r.stderr}")
        r = run(SYNTH, "verify-embedder", str(obj))
        m = re.search(r"0 reserved-register writes in (\d+) instructions", r.stdout)
        check(
            f"synth {name} --relocatable object ACCEPTED, nonzero scan",
            r.returncode == 0 and m is not None and int(m.group(1)) > 0,
            f"exit {r.returncode}: {(r.stderr or r.stdout)[:200]}",
        )

    # 8. Non-vacuity is a REFUSAL, not a pass: an ELF whose executable
    #    sections decode to nothing must not report conformance. An empty
    #    .text object is the probe.
    empty_s = tmp / "empty.s"
    empty_s.write_text("\t.syntax unified\n\t.cpu cortex-m7\n\t.thumb\n\t.text\n")
    empty_o = tmp / "empty.o"
    r = run(AS, "-mcpu=cortex-m7", "-mthumb", str(empty_s), "-o", str(empty_o))
    if r.returncode != 0:
        sys.exit(f"FAIL: could not assemble empty.s:\n{r.stderr}")
    r = run(SYNTH, "verify-embedder", str(empty_o))
    check(
        "0-instruction scan REFUSED (non-vacuity floor)",
        r.returncode != 0,
        f"exit {r.returncode}: {r.stdout[:200]}",
    )

    print(f"1132 CHECKS={passed}/9")
    if failed:
        print("RESULT: FAIL — " + ", ".join(failed))
        sys.exit(1)
    print("RESULT: PASS")


if __name__ == "__main__":
    main()
