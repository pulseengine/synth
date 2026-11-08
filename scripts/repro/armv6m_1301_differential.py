#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 624
"""RQ-91-ARMV6M (#1301) — the cortex-m0 / cortex-m0plus profile, SUPPORT LEVEL 3.

WHAT EXISTS. `--target cortex-m0` and `--target cortex-m0plus` (ARMv6-M,
triple thumbv6m-none-eabi, no FPU), on ONE shape: an ARM `--relocatable`
object. synth has NO ARMv6-M lowering — the selector and encoder are the
ARMv7-M ones — so every encoded instruction goes through the ARMv6-M byte
check (`crates/synth-backend/src/armv6m.rs`) and a function containing
anything outside ARMv6-M is REFUSED, loudly, naming the offset and the class.
The claim is exactly: what compiles on the profile is ARMv6-M (static), and
computes what wasmtime computes (execution). Nothing more.

RED BEFORE: on main 6b697bcf both targets exit 1 ("unknown target triple").
Leg A fails there.

THE LEGS
  A  profile + loud declines. The fixture compiles with BOTH targets to the
     SAME .text; the accepted set is EXACTLY `ACCEPTED`, and every other
     export declines with EXACTLY the class in `EXPECTED_DECLINES` (pinned
     both directions). Self-contained images and `-b riscv` are refused.
  B  static, over the WHOLE .text of every accepted object — not just the
     encode loop's view, so code emitted anywhere else is covered too: every
     instruction is in the frozen LLVM-derived 16-bit table
     (tests/fixtures/armv6m_legal16_1301.json) or is BL / DMB / DSB / ISB SY;
     no 16-bit LDR (literal) (the compiler refuses it too; this is the second
     check) and no pool words; every STT_FUNC symbol has the
     Thumb bit. A PLANTED v7-M MOVW in a copy must turn this leg RED.
  C  execution: every accepted function with an all-i32 signature — from the
     fixture AND from every tracked .wat/.wasm in this repo — runs under
     unicorn on a vector set and must equal wasmtime.

WHY UNICORN IS ENOUGH HERE, AND WHAT IT IS NOT. unicorn 2.1.4 does not
honour `ctl_set_cpu_model` for M-class: the model reads back as 11 (M33)
after setting M0, and TT (v8-M), SDIV and VADD.F32 all execute on "M0". So
unicorn proves NOTHING about ARMv6-M legality — leg B does. What unicorn
proves is the semantics, and that is sound for this code: leg B shows every
instruction is a 16-bit ARMv6-M encoding (or BL) and that there is no IT, and
a 16-bit ARMv6-M encoding outside an IT block means the same thing on v7-M
and v8-M as on v6-M.

Run:  SYNTH=target/debug/synth python3 scripts/repro/armv6m_1301_differential.py
"""
import hashlib
import json
import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_PC, UC_ARM_REG_R0, UC_ARM_REG_SP

ROOT = Path(__file__).resolve().parents[2]
SYNTH = os.environ.get("SYNTH", str(ROOT / "target/debug/synth"))
WAT = Path(__file__).with_name("armv6m_1301.wat")
FIXTURE = ROOT / "tests/fixtures/armv6m_legal16_1301.json"
TARGETS = ("cortex-m0", "cortex-m0plus")
BASE = ["--relocatable", "--all-exports", "--allow-skipped-exports"]

ACCEPTED = {"inc", "sub3", "ext8"}
# Each refused export -> the class its FIRST non-ARMv6-M instruction hits.
EXPECTED_DECLINES = {
    "big": "MOVW/MOVT",
    "divu": "UDIV/SDIV",
    "lt": "IT block",
    "callinc": "wide load/store multiple (PUSH/POP/LDM/STM)",
    "bits": "wide data-processing",
    "mul": "wide multiply",
    "ld": "wide load/store",
}

LEGAL = [tuple(r) for r in json.loads(FIXTURE.read_text())["legal_ranges"]]
FAILS = []


def fail(msg):
    FAILS.append(msg)
    print("FAIL", msg)


def synth(args):
    return subprocess.run([SYNTH, "compile", *args], capture_output=True, text=True,
                          env={**os.environ, "RUST_LOG": "error"}, timeout=300)


def is_prefix(h):
    return (h >> 11) in (0b11101, 0b11110, 0b11111)


def legal16(h):
    return any(lo <= h <= hi for lo, hi in LEGAL)


def legal32(a, b):
    return (a >> 11 == 0b11110 and b & 0xD000 == 0xD000) or (
        a == 0xF3BF and b in (0x8F4F, 0x8F5F, 0x8F6F))


def scan_text(text):
    """First non-ARMv6-M instruction in `text` as (offset, hex), else None."""
    i = 0
    while i + 1 < len(text):
        h = struct.unpack_from("<H", text, i)[0]
        if is_prefix(h):
            if i + 3 >= len(text):
                return i, f"{h:04x} (truncated)"
            h2 = struct.unpack_from("<H", text, i + 2)[0]
            if not legal32(h, h2):
                return i, f"{h:04x} {h2:04x}"
            i += 4
        else:
            # 0x4800-0x4FFF is LDR (literal) T1: legal ARMv6-M, but the
            # compiler's check refuses it (no pool reach — 1020 B on v6-M — is
            # checked for this profile). This is the SECOND check of that rule,
            # over the whole .text, so a literal load emitted anywhere shows.
            if not legal16(h) or 0x4800 <= h <= 0x4FFF:
                return i, f"{h:04x}"
            i += 2
    return None


def load(path):
    with open(path, "rb") as fh:
        e = ELFFile(fh)
        sec = e.get_section_by_name(".text")
        text = sec.data() if sec else b""
        syms, funcs = {}, []
        for s in e.get_section_by_name(".symtab").iter_symbols():
            if s["st_info"]["type"] == "STT_FUNC":
                funcs.append((s.name, s["st_value"], s["st_size"]))
                if s["st_info"]["bind"] == "STB_GLOBAL":
                    syms[s.name] = (s["st_value"], s["st_size"])
        relocs = []
        for rs in e.iter_sections():
            if rs["sh_type"] in ("SHT_REL", "SHT_RELA") and rs.name.endswith(".text"):
                relocs += [r["r_offset"] for r in rs.iter_relocations()]
    return text, syms, funcs, relocs


def leg_b(path, label):
    text, _, funcs, _ = load(path)
    bad = scan_text(text)
    if bad:
        fail(f"B {label}: non-ARMv6-M instruction at .text+0x{bad[0]:x}: {bad[1]}")
    for name, val, _ in funcs:
        if not val & 1:
            fail(f"B {label}: STT_FUNC {name} has no Thumb bit (value 0x{val:x})")
    return text


VECTORS = [0, 1, 2, 7, 0x7F, 0x80, 0xFF, 0x1234, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF,
           0xDEADBEEF]


def s32(v):
    return v - (1 << 32) if v >= 1 << 31 else v


def execute(path, wasm_bytes, only=None):
    """Run every executable accepted function vs wasmtime. Returns #functions."""
    text, syms, _, relocs = load(path)
    cfg = wasmtime.Config()
    cfg.consume_fuel = True
    eng = wasmtime.Engine(cfg)
    try:
        mod = wasmtime.Module(eng, wasm_bytes)
        store = wasmtime.Store(eng)
        store.set_fuel(10_000_000)
        inst = wasmtime.Instance(store, mod, [])
    except Exception:
        return 0  # imports / unsupported: not executable standalone
    exports = inst.exports(store)
    CODE, STK = 0x10000, 0x200000
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    size = (len(text) + 0x1FFF) & ~0xFFF
    mu.mem_map(CODE, size + 0x1000)
    mu.mem_write(CODE, text)
    mu.mem_map(STK, 0x10000)
    ret = CODE + size
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    ran = 0
    for name, (val, sz) in sorted(syms.items()):
        if only is not None and name not in only:
            continue
        f = exports.get(name) if hasattr(exports, "get") else None
        if f is None:
            try:
                f = exports[name]
            except Exception:
                continue
        if not isinstance(f, wasmtime.Func):
            continue
        ty = f.type(store)
        ps, rs = [str(p) for p in ty.params], [str(r) for r in ty.results]
        if any(p != "i32" for p in ps) or rs not in ([], ["i32"]) or len(ps) > 4:
            continue
        lo = val & ~1
        if any(lo <= r < lo + sz for r in relocs):
            continue  # calls something: needs a link step this leg does not do
        ran += 1
        for k, v in enumerate(VECTORS):
            args = [VECTORS[(k + j * 5) % len(VECTORS)] for j in range(len(ps))]
            try:
                store.set_fuel(10_000_000)
                exp = f(store, *[s32(a) for a in args])
                exp = None if exp is None else exp & 0xFFFFFFFF
                trapped = False
            except Exception:
                trapped, exp = True, None
            for j, a in enumerate(args):
                mu.reg_write(UC_ARM_REG_R0 + j, a)
            mu.reg_write(UC_ARM_REG_SP, STK + 0x8000)
            mu.reg_write(UC_ARM_REG_LR, ret | 1)
            try:
                mu.emu_start((CODE + lo) | 1, ret, timeout=2_000_000, count=1_000_000)
                got = mu.reg_read(UC_ARM_REG_R0) if rs else None
                faulted = mu.reg_read(UC_ARM_REG_PC) & ~1 != ret  # stopped early
            except UcError:
                got, faulted = None, True
            if trapped != faulted or (not trapped and rs and got != exp):
                fail(f"C {Path(path).name}:{name}{tuple(hex(a) for a in args)} = "
                     f"{'trap' if faulted else hex(got) if got is not None else '-'} "
                     f"expect {'trap' if trapped else hex(exp) if exp is not None else '-'}")
    return ran


def main():
    print(f"synth: {SYNTH}")
    with tempfile.TemporaryDirectory() as td:
        # ---- leg A ----------------------------------------------------------
        texts = {}
        for t in TARGETS:
            o = os.path.join(td, f"{t}.o")
            r = synth([str(WAT), "--target", t, *BASE, "-o", o])
            if r.returncode != 0:
                fail(f"A --target {t}: exit {r.returncode}: {r.stderr.strip()[-300:]}")
                continue
            declined = {}
            for line in r.stderr.splitlines():
                if line.startswith("warning: skipping function '"):
                    name = line.split("'")[1]
                    cls = line.split("not an ARMv6-M instruction — ", 1)[-1]
                    hit = [c for c in set(EXPECTED_DECLINES.values()) if cls.startswith(c + " (")]
                    declined[name] = max(hit, key=len) if hit else f"UNPARSED: {line[-160:]}"
                    if "(#1301)" not in line:
                        fail(f"A {t}: decline of {name} does not cite #1301")
            if declined != EXPECTED_DECLINES:
                fail(f"A {t}: declines {declined} != pinned {EXPECTED_DECLINES}")
            _, syms, _, _ = load(o)
            if set(syms) != ACCEPTED:
                fail(f"A {t}: accepted {sorted(syms)} != pinned {sorted(ACCEPTED)}")
            texts[t] = leg_b(o, t)
            print(f"A {t}: {len(syms)} accepted, {len(declined)} declined loudly")
        if len(texts) == 2 and texts["cortex-m0"] != texts["cortex-m0plus"]:
            fail("A: cortex-m0 and cortex-m0plus emit different .text")
        for args, needle in (
            ([str(WAT), "--target", "cortex-m0", "--all-exports"], "supports only `--relocatable`"),
            ([str(WAT), "--target", "cortex-m0", "--cortex-m", "--all-exports"],
             "supports only `--relocatable`"),
            ([str(WAT), "-b", "riscv", "--target", "cortex-m0", *BASE], "does not accept"),
        ):
            r = synth([*args, "-o", os.path.join(td, "x.out")])
            if r.returncode == 0 or needle not in r.stderr:
                fail(f"A refusal {' '.join(args[1:])}: rc={r.returncode} {r.stderr.strip()[-200:]}")
        # ---- leg B potency: a planted v7-M MOVW must be caught -------------
        if "cortex-m0" in texts:
            planted = bytearray(texts["cortex-m0"])
            planted[0:4] = struct.pack("<HH", 0xF240, 0x002A)
            if scan_text(bytes(planted)) is None:
                fail("B: planted MOVW NOT detected — the static leg is blind")
            else:
                print("B planted MOVW: detected")
        # ---- leg C: execution ------------------------------------------------
        o = os.path.join(td, "cortex-m0.o")
        fns = execute(o, WAT.read_bytes(), only=ACCEPTED) if os.path.exists(o) else 0
        if fns != len(ACCEPTED):
            fail(f"C fixture: executed {fns} of {len(ACCEPTED)} accepted functions")
        corpus_fns = corpus_objs = 0
        files = subprocess.run(["git", "-C", str(ROOT), "ls-files"], capture_output=True,
                               text=True, check=True).stdout.split()
        seen = set()
        for f in files:
            if not f.endswith((".wat", ".wasm")) or f.endswith("armv6m_1301.wat"):
                continue
            data = (ROOT / f).read_bytes()
            h = hashlib.sha256(data).hexdigest()
            if h in seen:
                continue
            seen.add(h)
            co = os.path.join(td, h[:16] + ".o")
            r = synth([str(ROOT / f), "--target", "cortex-m0", *BASE, "--embedder-data-init",
                       "--embedder-global-init", "-o", co])
            if r.returncode != 0 or not os.path.exists(co):
                continue
            if not load(co)[1]:
                continue
            corpus_objs += 1
            leg_b(co, f)
            try:
                corpus_fns += execute(co, data)
            except Exception as ex:  # a harness gap is a failure, not a skip
                fail(f"C {f}: harness error {ex!r}")
        print(f"C corpus: {corpus_objs} objects with accepted code, {corpus_fns} functions "
              f"executed vs wasmtime ({len(VECTORS)} vectors each)")
        if corpus_fns == 0:
            fail("C corpus: executed nothing")
    print("ORACLE:", "PASS" if not FAILS else f"FAIL ({len(FAILS)})")
    sys.exit(0 if not FAILS else 1)


if __name__ == "__main__":
    main()
