#!/usr/bin/env python3
# ci-status: manual (toolchain) — needs LLVM's llvm-objdump/llvm-objcopy (a thumbv6m-none-eabi decoder); the CI image installs only GNU binutils-arm-none-eabi, which is NOT an ARMv6-M oracle (measured: `--architecture=armv6-m` decodes movw, udiv, it and cbz without complaint). In CI the same ARMv6-M legality is gated by the in-tree predicate against the frozen fixture this script writes (crates/synth-backend/src/armv6m.rs unit test) and by armv6m_1301_differential.py (wired).
"""RQ-91-ARMV6M (#1301) — the LLVM cross-check of synth's ARMv6-M check.

synth refuses, per function, any encoded instruction outside ARMv6-M
(`crates/synth-backend/src/armv6m.rs`). This script checks that predicate
against an INDEPENDENT decoder — LLVM's `thumbv6m-none-eabi` — in three ways:

  --fixture-check   re-enumerate all 59,392 non-prefix 16-bit halfwords under
                    llvm-objdump thumbv6m and require the result to EQUAL the
                    committed fixture tests/fixtures/armv6m_legal16_1301.json
                    (which the Rust unit test pins the in-tree table to).
                    `--regen` writes the fixture instead.
  --wide-check      decode a 786,432-pair sample of the 32-bit space and
                    require: every pair synth's rule accepts (BL, DMB/DSB/ISB
                    SY) is accepted by LLVM. The rule is deliberately STRICTER
                    than ARMv6-M (MSR/MRS/UDF.W are refused); the count of
                    LLVM-only accepts is printed, not failed.
  --objects SYNTH   compile every tracked .wat/.wasm in this repo with
                    `--target cortex-m0 --relocatable --all-exports
                    --allow-skipped-exports --embedder-data-init
                    --embedder-global-init`, and decode every produced object
                    with llvm-objdump thumbv6m AFTER STRIPPING .ARM.attributes.
                    Zero `<unknown>` instructions are allowed. A PLANTED
                    positive control (one accepted object with a v7-M MOVW
                    patched into its .text) must go RED, or the check is blind.

WHY THE ATTRIBUTES ARE STRIPPED. llvm-objdump obeys an object's
.ARM.attributes OVER `--triple`: on gale's cm3 objects (v7 attributes) the
thumbv6m decode reported 2,539 illegal instructions instead of 9,185 — it
decoded add.w/ldr.w/push.w as if v6-M had them. synth's cortex-m0 objects
carry v6-M attributes, so stripping is belt-and-braces there, but the control
below is planted in such an object, and the census tools must not depend on it.

Exit non-zero on any disagreement.
"""
import argparse
import hashlib
import json
import os
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "tests/fixtures/armv6m_legal16_1301.json"
LLVM = os.environ.get("LLVM_BIN", "/opt/homebrew/opt/llvm/bin")
OD = os.path.join(LLVM, "llvm-objdump")
OC = os.path.join(LLVM, "llvm-objcopy")
LINE = re.compile(r"^\s*([0-9a-f]+):\s+((?:[0-9a-f]{4} ?){1,2})\s+(.*)$")


def is_prefix(h):
    return (h >> 11) in (0b11101, 0b11110, 0b11111)


def raw_to_elf(blob, td):
    b = os.path.join(td, "x.bin")
    o = os.path.join(td, "x.o")
    Path(b).write_bytes(blob)
    subprocess.run([OC, "-I", "binary", "-O", "elf32-littlearm", b, o], check=True)
    return o


def decode_data(obj, n_expected, step):
    out = subprocess.run(
        [OD, "-D", "-j", ".data", "--triple=thumbv6m-none-eabi", obj],
        capture_output=True, text=True, check=True,
    ).stdout
    res = {}
    for l in out.splitlines():
        m = LINE.match(l)
        if m:
            res[int(m.group(1), 16)] = (m.group(2).replace(" ", ""), m.group(3).strip())
    return res


def ranges(xs):
    out, s, p = [], None, None
    for x in xs:
        if s is None:
            s = p = x
        elif x == p + 1:
            p = x
        else:
            out.append([s, p])
            s = p = x
    if s is not None:
        out.append([s, p])
    return out


def llvm_version():
    v = subprocess.run([OD, "--version"], capture_output=True, text=True).stdout
    m = re.search(r"LLVM version ([\d.]+)", v)
    return m.group(1) if m else "unknown"


def derive16():
    hws = [h for h in range(65536) if not is_prefix(h)]
    with tempfile.TemporaryDirectory() as td:
        o = raw_to_elf(b"".join(struct.pack("<H", h) for h in hws), td)
        res = decode_data(o, len(hws), 2)
    legal = []
    for i, h in enumerate(hws):
        raw, txt = res[2 * i]
        assert int(raw, 16) == h, (hex(h), raw)
        if not txt.startswith("<unknown>"):
            legal.append(h)
    return len(hws), legal


def fixture_check(regen):
    n, legal = derive16()
    doc = {"legal_count": len(legal), "legal_ranges": ranges(legal),
           "provenance": (f"llvm-objdump --triple=thumbv6m-none-eabi (LLVM "
                          f"{llvm_version()}) over all {n} non-prefix halfwords; "
                          f"written by scripts/repro/armv6m_llvm_crosscheck_1301.py "
                          f"--regen")}
    if regen:
        FIXTURE.write_text(
            '{"legal_count": %d, "legal_ranges": %s, "provenance": %s}\n'
            % (doc["legal_count"], json.dumps(doc["legal_ranges"]), json.dumps(doc["provenance"])))
        print(f"wrote {FIXTURE.relative_to(ROOT)}: {len(legal)} legal of {n}, "
              f"{len(doc['legal_ranges'])} ranges")
        return True
    cur = json.loads(FIXTURE.read_text())
    ok = cur["legal_count"] == doc["legal_count"] and cur["legal_ranges"] == doc["legal_ranges"]
    print(f"16-bit: LLVM {llvm_version()} accepts {len(legal)} of {n}; fixture "
          f"{cur['legal_count']} — {'EQUAL' if ok else 'DIFFERENT'}")
    return ok


def rule32(a, b):
    # The SAME rule as armv6m::legal_32 (a cross-check target, not a source).
    return (a >> 11 == 0b11110 and b & 0xD000 == 0xD000) or (
        a == 0xF3BF and b in (0x8F4F, 0x8F5F, 0x8F6F))


def wide_check():
    hw1s = [h for h in range(65536) if is_prefix(h)]
    hw2s = [(n << 12) | lo for n in range(16)
            for lo in (0x000, 0x800, 0xF4F, 0xF5F, 0xF6F, 0x123, 0xFFF, 0x40F)]
    pairs = [(a, b) for a in hw1s for b in hw2s]
    with tempfile.TemporaryDirectory() as td:
        o = raw_to_elf(b"".join(struct.pack("<HH", a, b) for a, b in pairs), td)
        res = decode_data(o, len(pairs), 4)
    rule_only = llvm_only = both = 0
    for i, (a, b) in enumerate(pairs):
        raw, txt = res.get(4 * i, ("", "<unknown>"))
        llvm_ok = len(raw) == 8 and not txt.startswith("<unknown>")
        r = rule32(a, b)
        both += r and llvm_ok
        rule_only += r and not llvm_ok
        llvm_only += llvm_ok and not r
    print(f"32-bit sample of {len(pairs)}: rule∧LLVM {both}, rule-only {rule_only} "
          f"(must be 0), LLVM-only {llvm_only} (MSR/MRS forms synth never emits; "
          f"refused by the stricter rule)")
    return rule_only == 0 and both > 0


def strip_and_scan(obj, td):
    q = os.path.join(td, "s.o")
    subprocess.run([OC, "--remove-section=.ARM.attributes", obj, q], check=True)
    out = subprocess.run([OD, "-d", "--triple=thumbv6m-none-eabi", q],
                         capture_output=True, text=True, check=True).stdout
    bad, pc, n = [], 0, 0
    for l in out.splitlines():
        m = LINE.match(l)
        if m:
            n += 1
            if m.group(3).startswith("<unknown>"):
                bad.append(l.strip())
            if "[pc" in m.group(3):
                pc += 1
    return n, bad, pc


def objects(synth):
    files = subprocess.run(["git", "-C", str(ROOT), "ls-files"], capture_output=True,
                           text=True, check=True).stdout.split()
    files = [f for f in files if f.endswith((".wat", ".wasm"))]
    seen, ok, insns, accepted_objs, pool_loads = set(), True, 0, [], 0
    with tempfile.TemporaryDirectory() as td:
        for f in files:
            h = hashlib.sha256((ROOT / f).read_bytes()).hexdigest()
            if h in seen:
                continue
            seen.add(h)
            o = os.path.join(td, h[:16] + ".o")
            r = subprocess.run([synth, "compile", str(ROOT / f), "--target", "cortex-m0",
                                "--relocatable", "--all-exports", "--allow-skipped-exports",
                                "--embedder-data-init", "--embedder-global-init", "-o", o],
                               capture_output=True, text=True, timeout=300,
                               env={**os.environ, "RUST_LOG": "error"})
            if r.returncode != 0 or not os.path.exists(o):
                continue
            n, bad, pc = strip_and_scan(o, td)
            insns += n
            pool_loads += pc
            if n:
                accepted_objs.append(o)
            if bad:
                ok = False
                print(f"RED  {f}: {len(bad)} non-ARMv6-M instruction(s), first: {bad[0]}")
        print(f"objects: {len(seen)} unique inputs, {len(accepted_objs)} produced an object "
              f"with code, {insns} instructions decoded under thumbv6m, "
              f"{pool_loads} pc-relative loads (must be 0: synth's pool load is LDR.W)")
        ok = ok and pool_loads == 0 and insns > 0
        # PLANTED positive control: patch a v7-M MOVW over the first instruction
        # of the first accepted object's .text; the same scan must go RED.
        from elftools.elf.elffile import ELFFile
        victim = accepted_objs[0]
        with open(victim, "rb") as fh:
            off = ELFFile(fh).get_section_by_name(".text")["sh_offset"]
        blob = bytearray(Path(victim).read_bytes())
        blob[off:off + 4] = struct.pack("<HH", 0xF240, 0x002A)  # movw r0, #42
        planted = os.path.join(td, "planted.o")
        Path(planted).write_bytes(bytes(blob))
        _, bad, _ = strip_and_scan(planted, td)
        print(f"planted MOVW control: {'RED (detected)' if bad else 'GREEN — THE CHECK IS BLIND'}")
        ok = ok and bool(bad)
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--regen", action="store_true")
    ap.add_argument("--fixture-check", action="store_true")
    ap.add_argument("--wide-check", action="store_true")
    ap.add_argument("--objects", metavar="SYNTH")
    a = ap.parse_args()
    for t in (OD, OC):
        if not os.path.exists(t):
            sys.exit(f"needs {t} (set LLVM_BIN)")
    ok = True
    if a.regen or a.fixture_check:
        ok &= fixture_check(a.regen)
    if a.wide_check:
        ok &= wide_check()
    if a.objects:
        ok &= objects(a.objects)
    print("CROSSCHECK:", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
