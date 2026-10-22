#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 60
"""#1565 (RQ-89-RELOCSINGLE) — `--relocatable` on the ARM single-function path
must produce an object a host linker ACCEPTS, and the linked code must RUN.

The defect: `synth compile m.wat -t cortex-m4 -n a --relocatable -o a.o`
exited 0 and wrote an ET_EXEC image with its own Reset_Handler, byte-identical
to the same command without `--relocatable`. A host link then failed with
`cannot use executable file 'a.o' as input to a link` (or `multiple definition
of 'Reset_Handler'` beside a real startup). The reporter's execution-based
conformance sweep lost 75 thumb-2 assertions to it. aarch64 and RV32 already
honoured the flag; the A32 single-function builder (`-t cortex-r5`) was
ET_EXEC too.

What this harness proves, per leg (target x selector), from the ELF the
compiler wrote and from a REAL link of it:

  1. RELOCATABLE — e_type is ET_REL; no Reset_Handler; the requested export
                   is a DEFINED global FUNC; no other export ships; no symbol
                   is left undefined (a non-exported callee is pulled in by
                   the #235 closure — the `entry` leg).
  2. LINKABLE    — `arm-none-eabi-ld -e <export> -Ttext=0x0` links it with no
                   diagnostic. A missing linker is a LOUD failure, never a
                   skip (the #757/#743 inverse-vacuity lesson).
  3. CORRECT     — the LINKED image's export executes under unicorn and
                   matches wasmtime on 5 vectors (`a(41) == 42` among them).

Symbols are read from the ELF SYMBOL TABLE by section TYPE (SHT_SYMTAB), never
from disassembly text (the #489/#850 host-dependence lesson).

RED-FIRST: against the pre-fix binary every leg fails at step 1 (ET_EXEC,
Reset_Handler present) and the real link refuses the file — run with
SYNTH=<base-commit binary> to see it.

Run (needs wasmtime + unicorn + pyelftools + arm-none-eabi-ld):
  SYNTH=./target/debug/synth python3 scripts/repro/relocatable_single_function_1565_differential.py
"""

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_R0, UC_ARM_REG_SP

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
M32 = 0xFFFFFFFF

TWO_EXPORTS = """(module
  (func (export "a") (param i32) (result i32) (i32.add (local.get 0) (i32.const 1)))
  (func (export "b") (param i32) (result i32) (i32.mul (local.get 0) (i32.const 2))))
"""
# `entry` calls a NON-exported helper (function 0); `other` must not ship.
WITH_HELPER = """(module
  (func $helper (param i32) (result i32) (i32.mul (local.get 0) (i32.const 3)))
  (func (export "entry") (param i32) (result i32)
    (i32.add (call $helper (local.get 0)) (i32.const 5)))
  (func (export "other") (param i32) (result i32) (i32.sub (local.get 0) (i32.const 1))))
"""

VECTORS = [41, 0, 0xFFFFFFFF, 0x7FFFFFFF, 0x12345678]

TARGETS = [("cortex-m3", True), ("cortex-m4", True), ("cortex-m7", True),
           ("cortex-r5", False)]

# (module text key, selector flags, export expected, exports that must be absent)
SELECTIONS = [
    ("two", ["-n", "a"], "a", ["b"]),
    ("two", ["--func-index", "1"], "b", ["a"]),
    ("helper", ["-n", "entry"], "entry", ["other"]),
]


def need(tool, why):
    p = shutil.which(tool)
    if p is None:
        sys.exit(f"FAIL: {tool} not found ({why}) — install it; a skipped link "
                 "is a vacuous gate")
    return p


class Truth:
    def __init__(self, texts):
        self.engine = wasmtime.Engine()
        self.inst = {}
        for key, text in texts.items():
            store = wasmtime.Store(self.engine)
            module = wasmtime.Module(self.engine, text)
            self.inst[key] = (store, wasmtime.Instance(store, module, []))

    def call(self, key, export, x):
        store, inst = self.inst[key]
        signed = x - (1 << 32) if x & 0x80000000 else x
        return inst.exports(store)[export](store, signed) & M32


def symtab(path):
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
                else:
                    defined[sy.name] = (sy["st_value"], sy["st_info"]["bind"],
                                        sy["st_info"]["type"])
        return etype, defined, undef


def text_of(path):
    with open(path, "rb") as fh:
        t = ELFFile(fh).get_section_by_name(".text")
        return t.data(), t["sh_addr"]


STK_BASE, STK_SIZE = 0x30000, 0x10000


def run_arm(text, base, addr, x, thumb):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB if thumb else UC_MODE_ARM)
    page = base & ~0xFFF
    size = (len(text) + (base - page) + 0xFFF) & ~0xFFF
    uc.mem_map(page, max(size, 0x1000))
    uc.mem_write(base, text)
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


def leg(label, wat, target, thumb, sel, export, absent, tmp, truth, key):
    bugs, emus = [], 0
    obj = os.path.join(tmp, f"{label}.o")
    cmd = [SYNTH, "compile", wat, "-o", obj, "-t", target, *sel, "--relocatable"]
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0:
        print(f"  [BUG] {label}: compile failed:\n{r.stdout}{r.stderr}")
        return False, 0
    etype, defined, undef = symtab(obj)
    if etype != "ET_REL":
        bugs.append(f"e_type {etype}, want ET_REL (the #1565 silent ignore)")
    if "Reset_Handler" in defined:
        bugs.append("defines Reset_Handler — a synth-owned image, not an object")
    d = defined.get(export)
    if d is None or d[1] != "STB_GLOBAL" or d[2] != "STT_FUNC":
        bugs.append(f"`{export}` is not a defined global FUNC: {d}")
    for a in absent:
        if a in defined:
            bugs.append(f"`{a}` ships but was not requested")
    if undef:
        bugs.append(f"undefined symbols {sorted(undef)}")
    linked = os.path.join(tmp, f"{label}.elf")
    lr = subprocess.run([need("arm-none-eabi-ld", "links the ARM/A32 objects"),
                         "-e", export, "-Ttext=0x0", obj, "-o", linked],
                        capture_output=True, text=True)
    if lr.returncode != 0 or lr.stderr.strip():
        bugs.append(f"real link failed: {lr.stderr.strip() or lr.returncode}")
    if bugs:
        for b in bugs:
            print(f"  [BUG] {label}: {b}")
        return False, 0
    text, base = text_of(linked)
    _, ldefined, _ = symtab(linked)
    addr = ldefined[export][0]
    fails = 0
    for x in VECTORS:
        got = run_arm(text, base, addr, x, thumb)
        emus += 1
        exp = truth.call(key, export, x)
        if got != exp:
            fails += 1
            shown = got if isinstance(got, str) else f"{got:#x}"
            print(f"  [BUG] {label}: {export}({x:#x}) -> {shown} (wasmtime {exp:#x})")
    if fails == 0:
        print(f"  [ok ] {label}: ET_REL, no Reset_Handler, `{export}` defined "
              f"global, 0 UNDEF, real link clean, {len(VECTORS)} vectors match "
              "wasmtime")
    return fails == 0, emus


def main():
    print("=== #1565 single-function --relocatable: object + link + execute ===")
    if not Path(SYNTH).is_file():
        sys.exit(f"FAIL: synth binary not found at {SYNTH}")
    tmp = tempfile.mkdtemp(prefix="reloc1565_")
    texts = {"two": TWO_EXPORTS, "helper": WITH_HELPER}
    wats = {}
    for key, text in texts.items():
        wats[key] = os.path.join(tmp, f"{key}.wat")
        Path(wats[key]).write_text(text)
    truth = Truth(texts)
    ok_all, emus_total, legs = True, 0, 0
    for target, thumb in TARGETS:
        for key, sel, export, absent in SELECTIONS:
            label = f"{target} {' '.join(sel)}"
            ok, emus = leg(label.replace(" ", "_"), wats[key], target, thumb,
                           sel, export, absent, tmp, truth, key)
            legs += 1
            emus_total += emus
            ok_all = ok_all and ok
    shutil.rmtree(tmp, ignore_errors=True)
    print(f"\nORACLE: {'PASS' if ok_all else 'FAIL'} — {legs} legs, "
          f"{emus_total} emulations vs wasmtime")
    sys.exit(0 if ok_all else 1)


if __name__ == "__main__":
    main()
