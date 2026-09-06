#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 36
"""#1168 (RQ-63-WASTCLOSURE) — the .wast input path must ship a COMPLETE,
LINKABLE object, proven by a real link and by execution, on every backend.

The defect: `synth compile m.wast --all-exports` skipped the #235 reachable-
callgraph closure and compiled EXPORTS ONLY. A non-exported callee was never
built, and three of four backends shipped the object with a dangling
`func_N` at exit 0 (ARM Thumb-2, A32, RV32); the self-contained `--cortex-m`
leg — the one spec_compile_census.py measures — silently flipped to an ET_REL
"link me" object because the dangling reloc counted as external. aarch64
refused only because its ELF builder refuses any unplaced relocation target
(#851/#1013), and its message named a decline warning that was never printed.

What this harness proves, per backend leg, on the .wast fixture beside it:

  1. COMPLETE   — every reachable non-exported helper (func_0/1/2) is a
                  DEFINED symbol; the unreachable `dead` (func_3) is ABSENT
                  (closure, not emit-all); NO undefined symbol at all.
  2. LINKABLE   — the object links with a REAL linker (arm-none-eabi-ld for
                  ARM/A32, ld.lld for RV32 and aarch64); a missing linker is a
                  LOUD failure, never a skip (the #757/#743 inverse-vacuity
                  lesson). The self-contained census leg must be ET_EXEC.
  3. CORRECT    — the LINKED image executes under unicorn and matches
                  wasmtime for 7 vectors (entry(x) = 7x+8 depends on the whole
                  transitive closure being compiled in AND every internal call
                  patched to the emitted callee). The self-contained leg runs
                  its OWN Reset_Handler startup on zeroed RAM.

Symbols are read from the ELF SYMBOL TABLE by section TYPE (SHT_SYMTAB) —
never by name (synth's ARM objects name their symtab with an EMPTY string) and
never from disassembly text (the #489/#850 host-dependence lesson).

NON-VACUITY (`EXPORTS_ONLY_275=1`, probe-feature binary only): the same hatch
the #275 oracle uses reverts the .wast merge to its pre-#1168 exports-only
behaviour. In that mode this harness asserts the OTHER half of the fix — the
generalized "not placed in this object" refusal (#1102 keyed on the DECLINED
set and so could not fire here): every leg must FAIL the compile cleanly with
the #1168 reason and write NO object. Two guards, one script: the closure
makes the object complete; the refusal makes an incomplete one impossible to
ship. The `ci-checks` floor above binds only the execution mode (probe mode
emulates nothing and is not routed through oracle_run.py — see ORACLE_WIRING.md
on the #275 RED step for the same shape).

Run (needs wasmtime + unicorn + pyelftools + arm-none-eabi-ld + ld.lld):
  SYNTH=./target/debug/synth python scripts/repro/wast_callgraph_closure_1168_differential.py
  EXPORTS_ONLY_275=1 SYNTH=./target-275probe/debug/synth python scripts/repro/wast_callgraph_closure_1168_differential.py
"""

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import (
    UC_ARCH_ARM,
    UC_ARCH_ARM64,
    UC_ARCH_RISCV,
    UC_MODE_ARM,
    UC_MODE_RISCV32,
    UC_MODE_THUMB,
    Uc,
    UcError,
)
from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_R0, UC_ARM_REG_SP
from unicorn.arm64_const import (
    UC_ARM64_REG_LR,
    UC_ARM64_REG_SP,
    UC_ARM64_REG_W0,
    UC_ARM64_REG_X0,
)
from unicorn.riscv_const import UC_RISCV_REG_A0, UC_RISCV_REG_RA, UC_RISCV_REG_SP

WAST = Path(__file__).with_name("wast_callgraph_closure_1168.wast")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
PROBE = bool(os.environ.get("EXPORTS_ONLY_275"))

VECTORS = [0, 1, 2, 5, 17, 100, 0x1000]
M32 = (1 << 32) - 1
# leaf/mid/add5 are the reachable closure; `dead` is unreachable.
HELPERS = ("func_0", "func_1", "func_2")
DEAD = "func_3"

# (label, synth flags, execution kind). The three census legs use EXACTLY the
# flags spec_compile_census.py uses (`--cortex-m`, `-b riscv`, `-b aarch64`);
# the two `--relocatable` ARM legs are the host-linked embedder shape.
LEGS = [
    ("cortex-m3 --relocatable",
     ["-b", "arm", "--target", "cortex-m3", "--relocatable"], "thumb"),
    ("--cortex-m self-contained (the census 'arm' leg)",
     ["--cortex-m"], "image"),
    ("cortex-r5 --relocatable (A32)",
     ["-b", "arm", "--target", "cortex-r5", "--relocatable"], "a32"),
    ("-b riscv (the census 'riscv' leg)", ["-b", "riscv"], "rv32"),
    ("-b aarch64 (the census 'aarch64' leg)", ["-b", "aarch64"], "a64"),
]

# ---------------------------------------------------------------------------
# fixture -> wasmtime ground truth
# ---------------------------------------------------------------------------


def module_text():
    """The first `(module ...)` form of the .wast, by paren matching over the
    comment-stripped text (the fixture keeps parentheses out of comments).
    Feeding wasmtime the SAME text synth compiled is what makes this a
    differential rather than a mirror."""
    src = "\n".join(l.split(";;", 1)[0] for l in WAST.read_text().splitlines())
    start = src.index("(module")
    depth = 0
    for i in range(start, len(src)):
        if src[i] == "(":
            depth += 1
        elif src[i] == ")":
            depth -= 1
            if depth == 0:
                return src[start:i + 1]
    sys.exit("fixture: unbalanced (module ...) form")


class Truth:
    def __init__(self):
        engine = wasmtime.Engine()
        module = wasmtime.Module(engine, module_text())
        self.store = wasmtime.Store(engine)
        self.inst = wasmtime.Instance(self.store, module, [])

    def entry(self, x):
        return self.inst.exports(self.store)["entry"](self.store, x) & M32


# ---------------------------------------------------------------------------
# compile / symtab / link
# ---------------------------------------------------------------------------


def compile_leg(flags, out):
    env = {"PATH": "/usr/bin:/bin"}
    if PROBE:
        env["EXPORTS_ONLY_275"] = "1"
    cmd = [SYNTH, "compile", str(WAST), "-o", out, "--all-exports", *flags]
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    return r.returncode, r.stdout + r.stderr


def symtab(path):
    """(e_type, {defined FUNC name: value}, {undefined names}) — by section
    TYPE, never by name."""
    with open(path, "rb") as fh:
        f = ELFFile(fh)
        etype = f["e_type"]
        defined, undef = {}, set()
        for s in f.iter_sections():
            if s["sh_type"] != "SHT_SYMTAB":
                continue
            for sy in s.iter_symbols():
                if not sy.name:
                    continue
                if sy["st_shndx"] == "SHN_UNDEF":
                    undef.add(sy.name)
                elif sy["st_info"]["type"] == "STT_FUNC":
                    defined[sy.name] = sy["st_value"]
        return etype, defined, undef


def text_of(path):
    with open(path, "rb") as fh:
        f = ELFFile(fh)
        t = f.get_section_by_name(".text")
        return t.data(), t["sh_addr"]


def need(tool, why):
    p = shutil.which(tool)
    if p is None:
        sys.exit(f"FAIL: {tool} not found ({why}) — install it; a skipped link "
                 "is a vacuous gate")
    return p


def link(kind, obj, out):
    """A REAL link, hard-failing on any diagnostic: an unresolved reference
    that a skipped link would hide is the whole defect class."""
    if kind in ("thumb", "a32"):
        cmd = [need("arm-none-eabi-ld", "links the ARM/A32 objects"),
               "-e", "entry", "-Ttext=0x0", obj, "-o", out]
    elif kind == "rv32":
        cmd = [need("ld.lld", "links the RV32 and aarch64 objects"),
               "-m", "elf32lriscv", "-e", "entry", "--image-base=0x10000",
               "-Ttext=0x10000", obj, "-o", out]
    elif kind == "a64":
        cmd = [need("ld.lld", "links the RV32 and aarch64 objects"),
               "-m", "aarch64elf", "-e", "entry", "--image-base=0x100000",
               "-Ttext=0x100000", obj, "-o", out]
    else:
        raise AssertionError(kind)
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0 or r.stderr.strip():
        return None, r.stderr.strip() or f"exit {r.returncode}"
    return out, ""


# ---------------------------------------------------------------------------
# execution
# ---------------------------------------------------------------------------

STK_BASE, STK_SIZE = 0x30000, 0x10000


def map_text(uc, text, base):
    page = base & ~0xFFF
    size = (len(text) + (base - page) + 0xFFF) & ~0xFFF
    uc.mem_map(page, max(size, 0x1000))
    uc.mem_write(base, text)


def run_arm(text, base, addr, x, thumb):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB if thumb else UC_MODE_ARM)
    map_text(uc, text, base)
    uc.mem_map(STK_BASE, STK_SIZE)
    ret = STK_BASE + STK_SIZE - 0x100
    uc.reg_write(UC_ARM_REG_SP, ret)
    uc.reg_write(UC_ARM_REG_LR, (ret | 1) if thumb else ret)
    uc.reg_write(UC_ARM_REG_R0, x & M32)
    try:
        uc.emu_start((addr | 1) if thumb else (addr & ~1), ret, count=100000)
    except UcError as e:
        return f"ERR:{e}"
    return uc.reg_read(UC_ARM_REG_R0) & M32


def run_rv32(text, base, addr, x):
    uc = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
    map_text(uc, text, base)
    uc.mem_map(STK_BASE, STK_SIZE)
    ret = STK_BASE + STK_SIZE - 0x100
    uc.reg_write(UC_RISCV_REG_SP, ret)
    uc.reg_write(UC_RISCV_REG_RA, ret)
    uc.reg_write(UC_RISCV_REG_A0, x & M32)
    try:
        uc.emu_start(addr, ret, count=100000)
    except UcError as e:
        return f"ERR:{e}"
    return uc.reg_read(UC_RISCV_REG_A0) & M32


def run_a64(text, base, addr, x):
    uc = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    map_text(uc, text, base)
    uc.mem_map(STK_BASE, STK_SIZE)
    ret = STK_BASE + STK_SIZE - 0x100
    uc.reg_write(UC_ARM64_REG_SP, ret)
    uc.reg_write(UC_ARM64_REG_LR, ret)
    uc.reg_write(UC_ARM64_REG_X0, x & M32)
    try:
        uc.emu_start(addr, ret, count=100000)
    except UcError as e:
        return f"ERR:{e}"
    return uc.reg_read(UC_ARM64_REG_W0) & M32


class ImageRunner:
    """The DEFAULT self-contained image, startup included (the #275 harness
    shape): one persistent unicorn instance on ZEROED RAM; the artifact's own
    Reset_Handler runs up to its `LDR r0,[pc,#4]; BLX r0` scaffold."""

    FLASH, RAM, RAM_SIZE = 0x0000_0000, 0x2000_0000, 0x40000
    RET = 0x000F_0000

    def __init__(self, code, base, syms):
        self.base, self.syms = base, syms
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        self.mu.mem_map(self.FLASH, 0x100000)
        self.mu.mem_map(self.RAM, self.RAM_SIZE)
        self.mu.mem_map(0xE000E000, 0x1000)
        self.mu.mem_write(base, code)
        self.sp = int.from_bytes(code[0:4], "little")
        reset = syms.get("Reset_Handler")
        if reset is None:
            sys.exit("FAIL: Reset_Handler missing from the self-contained image")
        stop = code.find(b"\x01\x48\x80\x47", (reset & ~1) - base)
        if stop < 0:
            sys.exit("FAIL: startup call scaffold (LDR r0/BLX r0) not found")
        self.mu.reg_write(UC_ARM_REG_SP, self.sp)
        self.mu.emu_start(reset | 1, base + stop, count=100000)

    def call(self, addr, x):
        self.mu.reg_write(UC_ARM_REG_SP, self.sp)
        self.mu.reg_write(UC_ARM_REG_LR, self.RET | 1)
        self.mu.reg_write(UC_ARM_REG_R0, x & M32)
        try:
            self.mu.emu_start(addr | 1, self.RET, count=100000)
        except UcError as e:
            return f"ERR:{e}"
        return self.mu.reg_read(UC_ARM_REG_R0) & M32


# ---------------------------------------------------------------------------
# legs
# ---------------------------------------------------------------------------


def leg_probe(label, flags, tmp):
    """EXPORTS_ONLY_275 mode: the closure is bypassed, so the object WOULD be
    incomplete — the #1168 refusal must fire, cleanly, and leave no object."""
    obj = str(Path(tmp) / "probe.o")
    rc, out = compile_leg(flags, obj)
    bugs = []
    if rc == 0:
        bugs.append("compile exited 0 — an incomplete object shipped")
    if "panicked at" in out or "RUST_BACKTRACE" in out:
        bugs.append("refusal was a PANIC, not a clean decline")
    if "#1168" not in out or "does not place" not in out:
        bugs.append("refusal is not the #1168 not-placed class")
    # The WARNING form, not the bare phrase: the #1168 refusal text itself
    # says "no 'skipping function' warning precedes it".
    if "warning: skipping function" in out:
        bugs.append("a decline fired — the probe is not exercising the "
                    "never-compiled class")
    if os.path.exists(obj) and os.path.getsize(obj) > 0:
        bugs.append("an object was written despite the refusal")
    if "func_1" not in out and "func_2" not in out:
        bugs.append("refusal does not name a dangling helper edge")
    for b in bugs:
        print(f"  [BUG] {label}: {b}")
    if not bugs:
        print(f"  [ok ] {label}: refused cleanly (#1168, no object): "
              f"{out.strip().splitlines()[-1][:110]}")
    return not bugs


def leg_execute(label, flags, kind, tmp, truth):
    obj = str(Path(tmp) / f"{kind}.o")
    rc, out = compile_leg(flags, obj)
    if rc != 0:
        print(f"  [BUG] {label}: compile failed:\n{out}")
        return False, 0
    if "warning: skipping function" in out:
        print(f"  [BUG] {label}: a function was skipped — this fixture has "
              f"no declines:\n{out}")
        return False, 0
    etype, defined, undef = symtab(obj)
    bugs = []
    if undef:
        bugs.append(f"UNDEFINED symbols in the object: {sorted(undef)}")
    missing = [h for h in HELPERS if h not in defined]
    if missing:
        bugs.append(f"reachable helper(s) ABSENT from the object: {missing}")
    if DEAD in defined:
        bugs.append(f"unreachable {DEAD} PRESENT — emit-all, not a closure")
    if "entry" not in defined:
        bugs.append("export 'entry' absent")
    if kind == "image":
        if etype != "ET_EXEC":
            bugs.append(f"self-contained image is {etype}, not ET_EXEC — the "
                        "dangling-callee silent flip to a link-me object")
        elf = obj
    else:
        elf, diag = link(kind, obj, str(Path(tmp) / f"{kind}.elf"))
        if elf is None:
            bugs.append(f"real link FAILED: {diag}")
    for b in bugs:
        print(f"  [BUG] {label}: {b}")
    if bugs:
        return False, 0
    # Execute the LINKED image (or the self-contained one) vs wasmtime.
    text, base = text_of(elf)
    _, lsyms, _ = symtab(elf)
    entry = lsyms["entry"]
    runner = ImageRunner(text, base, lsyms) if kind == "image" else None
    fails, emus = 0, (1 if runner else 0)
    for x in VECTORS:
        exp = truth.entry(x)
        if kind == "image":
            got = runner.call(entry, x)
        elif kind == "thumb":
            got = run_arm(text, base, entry, x, thumb=True)
        elif kind == "a32":
            got = run_arm(text, base, entry, x, thumb=False)
        elif kind == "rv32":
            got = run_rv32(text, base, entry, x)
        else:
            got = run_a64(text, base, entry, x)
        emus += 1
        ok = isinstance(got, int) and got == exp
        if not ok:
            fails += 1
            shown = hex(got) if isinstance(got, int) else got
            print(f"  [BUG] {label}: entry({x}) -> {shown} (wasmtime {exp:#x})")
    if fails == 0:
        print(f"  [ok ] {label}: {etype}, helpers {list(HELPERS)} defined, "
              f"{DEAD} absent, 0 UNDEF, real link clean, "
              f"{len(VECTORS)} vectors match wasmtime")
    return fails == 0, emus


def main():
    mode = ("PROBE: exports-only merge, expect the #1168 refusal" if PROBE
            else "closure + link + execute vs wasmtime")
    print(f"=== #1168 .wast reachable-callgraph closure [{mode}] ===")
    if not Path(SYNTH).is_file():
        sys.exit(f"FAIL: synth binary not found at {SYNTH}")
    tmp = tempfile.mkdtemp(prefix="wast1168_")
    ok_all, emus_total = True, 0
    truth = None if PROBE else Truth()
    for label, flags, kind in LEGS:
        if PROBE:
            ok = leg_probe(label, flags, tmp)
        else:
            ok, emus = leg_execute(label, flags, kind, tmp, truth)
            emus_total += emus
        ok_all = ok_all and ok
    if PROBE:
        print(f"\nORACLE: {'PASS' if ok_all else 'FAIL'} — {len(LEGS)} legs "
              f"{'all refused with #1168' if ok_all else 'NOT all refused'} "
              "(closure bypassed; the not-placed gate is what stood)")
    else:
        print(f"\nORACLE: {'PASS' if ok_all else 'FAIL'} — {len(LEGS)} legs, "
              f"{emus_total} emulations vs wasmtime")
    sys.exit(0 if ok_all else 1)


if __name__ == "__main__":
    main()
