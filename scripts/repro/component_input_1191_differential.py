#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 4
"""RQ-91-COMPEXPORTS (#1191) — a WebAssembly COMPONENT given to `synth compile`
is REFUSED loudly, on every backend and mode, instead of being decoded as one
flattened core module.

THE DEFECT (measured on 6b697bcf). Both decode functions in
`synth-core/src/wasm_decoder.rs` walked the input with `Parser::parse_all`,
which descends into every nested core module of a component, and had no
`Payload::Version` arm — so a component was decoded as ONE module whose
function/import/export index spaces were the CONCATENATION of its nested
modules'. Accepted at exit 0, no warning, on arm (relocatable, self-contained,
single-function), riscv and aarch64:

  shape 1 (the record's refuting toy) — defines `t:c/sched#state`, an
          interface the component does NOT export, and nothing for the
          `t:c/time#now` it does;
  shape 2 — same class, the other plug order;
  shape 3 (the gale-nano shape: the importer's core module first) —
          `U now` for internal wiring beside the one real import `read32`;
  shape 4 — two plain core modules: the export NAME `g` lands on the WRONG
          BODY. wasmtime's component runtime: g() = 101; synth's `g`,
          EXECUTED under unicorn: 2. Silent wrong code;
  shape 5 — a core module importing `env::__cabi_arena_realloc` from a
          SECOND core module: `U __cabi_arena_realloc` for a component that
          declares NO imports, and on the self-contained Cortex-M path the
          #418 arena binder rewrote the component BEFORE decode and failed
          with a misleading "#418 internal ... (bug)" error. This shape is
          what makes the CLI-level refusal (ahead of loom/arena_bind)
          observable: with only the decoder check it stays that error.

MUTANTS (measured at authoring, each restored after): the helper made
always-Ok -> this oracle RED (0 of 35 refused) and 2 of 3 synth-core unit
tests red; the check dropped from `decode_wasm_functions` only -> the unit
test `component_1191_refused_by_decode_wasm_functions` RED (this oracle
cannot reach that function in the default build: `synth verify` needs the
`verify` feature, and compile's own call sits after the CLI check); the
three CLI-level calls removed -> this oracle RED on shape 5
arm-self-contained (34 of 35).

THE ORACLE. The declared interface of each fixture is DERIVED from wasmtime's
own component type (`Component.type.exports/imports`), never hand-typed, and
mapped to the canonical-ABI core names synth's object would carry
(`iface#func` / a world-level func's own name for exports; the import's field
name for imports, which is synth's undefined-symbol convention).

  default (the shipped behaviour): every shape x every mode must exit
          non-zero, name #1191 and the `meld fuse` route, and write NO output.
  --expect-red (run against a pre-fix binary): every shape x mode must be
          ACCEPTED, shapes 1-3's symbol tables must DISAGREE with the declared
          interface, and shape 4's `g` must EXECUTE to a value != wasmtime's.

CONTROLS (both modes — the harness can pass, and the refusal does not reach
core modules):
  * the core-module TWIN of shape 4 compiles (arm --relocatable), and its
    `f`/`g` EXECUTE under unicorn to wasmtime's values (1 / 101). With
    SYNTH_BASE set, the twin's object must be BYTE-IDENTICAL between SYNTH and
    SYNTH_BASE.
  * the meld 0.9.0 FUSED core module of shape 4 (frozen fixture, sha256
    pinned; its attestation's input hash is checked against shape 4's
    assembled bytes) compiles and EXECUTES to wasmtime's values — the route
    the diagnostic names works.
"""

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
import wasmtime.component as wcomp
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

HERE = Path(__file__).resolve().parent
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
SYNTH_BASE = os.environ.get("SYNTH_BASE")

SHAPES = {
    "shape1": HERE / "component_1191_shape1.wat",
    "shape2": HERE / "component_1191_shape2.wat",
    "shape3": HERE / "component_1191_shape3.wat",
    "shape4": HERE / "component_1191_shape4.wat",
    "shape5": HERE / "component_1191_shape5_arena.wat",
}
TWIN = HERE / "component_1191_twin.wat"
FUSED = HERE / "component_1191_shape4_fused_meld090.wasm"
FUSED_SHA256 = "de1ed50acfcf27b651c66842a7ddd2d89708d9b935f54a5da6e9006b2a4eef43"
SHAPE4_SHA256 = "c64f6bd0109094b3b3dda3aeea5f309f8c72c8d631ba6441e7369887212503f3"

ARM_REL = ["-b", "arm", "-t", "cortex-m3", "--cortex-m", "--relocatable",
           "--all-exports", "--embedder-data-init", "--embedder-global-init"]
MODES = {
    "arm-relocatable": ARM_REL,
    "arm-self-contained": ["-b", "arm", "-t", "cortex-m3", "--cortex-m",
                           "--all-exports"],
    "riscv-relocatable": ["-b", "riscv", "--relocatable", "--all-exports"],
    "aarch64-relocatable": ["-b", "aarch64", "--relocatable", "--all-exports"],
    "aarch64": ["-b", "aarch64", "--all-exports"],
    # filled per shape with `-n <first declared export>`
    "arm-single-function": ["-b", "arm", "-t", "cortex-m3", "--cortex-m"],
}

CODE, STK, RET = 0x100000, 0x900000, 0x300000


def host_read32(_store, a):
    return a // 2


def _item_type(item):
    """wasmtime-py <= 48 returns the item type itself from
    `ComponentType.exports/imports`; 50.x wraps it in a `ComponentExtern`
    whose `.ty` is the type. CI's install is unpinned, so accept both."""
    ty = getattr(item, "ty", None)
    return item if ty is None else ty


def declared(wasm):
    """(exports, imports, expected values) DERIVED from wasmtime's component
    type, plus each declared export's value from the component runtime."""
    eng = wasmtime.Engine()
    comp = wcomp.Component(eng, wasm)
    ty = comp.type
    exports, imports, calls = set(), set(), []
    for name, item in ty.exports(eng).items():
        item = _item_type(item)
        if isinstance(item, wcomp.FuncType):
            exports.add(name)
            calls.append((None, name))
        else:
            for fn in item.exports(eng):
                exports.add(f"{name}#{fn}")
                calls.append((name, fn))
    for name, item in ty.imports(eng).items():
        item = _item_type(item)
        if isinstance(item, wcomp.FuncType):
            imports.add(name)
        else:
            imports.update(item.exports(eng))
    store = wasmtime.Store(eng)
    linker = wcomp.Linker(eng)
    with linker.root() as root:
        for name, item in ty.imports(eng).items():
            assert name == "t:c/mmio", f"unexpected import {name}"
            with root.add_instance(name) as inst:
                inst.add_func("read32", host_read32)
    inst = linker.instantiate(store, comp)
    values = {}
    for iface, fn in calls:
        parent = inst.get_export_index(store, iface) if iface else None
        idx = inst.get_export_index(store, fn, parent)
        values[f"{iface}#{fn}" if iface else fn] = inst.get_func(store, idx)(store)
    return exports, imports, values


def synth(binary, inp, out, args):
    r = subprocess.run([binary, "compile", str(inp), "-o", str(out)] + args,
                       capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


def symtab(obj):
    defined, undefined = set(), set()
    with open(obj, "rb") as fh:
        f = ELFFile(fh)
        st = f.get_section_by_name(".symtab")
        for s in st.iter_symbols():
            if not s.name or s["st_info"]["bind"] != "STB_GLOBAL":
                continue
            if s["st_shndx"] == "SHN_UNDEF":
                undefined.add(s.name)
            elif s["st_info"]["type"] == "STT_FUNC":
                defined.add(s.name)
    return defined, undefined


def load_rel(obj):
    """Load .text of an ARM ET_REL and resolve its R_ARM_THM_CALL relocations
    against LOCAL symbols (the harness is the linker). Returns (code, syms)."""
    with open(obj, "rb") as fh:
        f = ELFFile(fh)
        text = f.get_section_by_name(".text")
        code = bytearray(text.data())
        symsec = f.get_section_by_name(".symtab")
        allsyms = list(symsec.iter_symbols())
        funcs = {s.name: s["st_value"] for s in allsyms
                 if s.name and s["st_info"]["type"] == "STT_FUNC"
                 and s["st_shndx"] != "SHN_UNDEF"}
        rel = f.get_section_by_name(".rel.text")
        for r in (rel.iter_relocations() if rel else []):
            sym = allsyms[r["r_info_sym"]]
            if r["r_info_type"] != 10:  # R_ARM_THM_CALL
                sys.exit(f"unexpected relocation type {r['r_info_type']} in {obj}")
            if sym["st_shndx"] == "SHN_UNDEF":
                sys.exit(f"unresolved import {sym.name} in a control object {obj}")
            P, S = r["r_offset"], sym["st_value"] & ~1
            off = S - (P + 4)
            s = (off >> 24) & 1
            i1, i2 = (off >> 23) & 1, (off >> 22) & 1
            j1, j2 = (1 - i1) ^ s, (1 - i2) ^ s
            imm10, imm11 = (off >> 12) & 0x3FF, (off >> 1) & 0x7FF
            hi = 0xF000 | (s << 10) | imm10
            lo = 0xD000 | (j1 << 13) | (j2 << 11) | imm11
            code[P:P + 4] = hi.to_bytes(2, "little") + lo.to_bytes(2, "little")
    return bytes(code), funcs


def run_arm(code, faddr):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, 0x20000000)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + (faddr & ~1)) | 1, RET, count=100000)
    except UcError as e:
        return f"ERR:{e}"
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


def core_values(wasm):
    eng = wasmtime.Engine()
    store = wasmtime.Store(eng)
    inst = wasmtime.Instance(store, wasmtime.Module(eng, wasm), [])
    ex = inst.exports(store)
    return {n: ex[n](store) for n in ("f", "g")}


def control(tmp, label, inp, wasm, failures):
    """Compile a CORE module (arm --relocatable) and execute f/g vs wasmtime."""
    out = tmp / f"{label}.o"
    rc, log = synth(SYNTH, inp, out, ARM_REL)
    if rc != 0:
        failures.append(f"control {label}: compile rc={rc}: {log.strip()[-300:]}")
        return 0
    exp = core_values(wasm)
    code, funcs = load_rel(out)
    n = 0
    for fn, want in exp.items():
        got = run_arm(code, funcs[fn])
        n += 1
        ok = got == want
        print(f"  [{'ok ' if ok else 'BUG'}] control {label}: {fn}() -> {got} (wasmtime {want})")
        if not ok:
            failures.append(f"control {label}: {fn}() = {got}, wasmtime {want}")
    if SYNTH_BASE:
        bout = tmp / f"{label}.base.o"
        brc, blog = synth(SYNTH_BASE, inp, bout, ARM_REL)
        same = brc == 0 and bout.read_bytes() == out.read_bytes()
        print(f"  [{'ok ' if same else 'BUG'}] control {label}: object byte-identical "
              f"to SYNTH_BASE ({hashlib.sha256(out.read_bytes()).hexdigest()[:16]})")
        if not same:
            failures.append(f"control {label}: object differs from SYNTH_BASE")
    return n


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--expect-red", action="store_true",
                    help="assert the PRE-FIX defect (run with a pre-fix SYNTH)")
    args = ap.parse_args()

    failures = []
    refusals = accepted = mismatches = wrong_values = executions = 0
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        print("=== component inputs ===")
        for shape, wat in SHAPES.items():
            wasm = bytes(wasmtime.wat2wasm(wat.read_text()))
            comp_path = tmp / f"{shape}.wasm"
            comp_path.write_bytes(wasm)
            exports, imports, values = declared(wasm)
            print(f"{shape}: declared exports {sorted(exports)} imports "
                  f"{sorted(imports)}; wasmtime component runtime {values}")
            first = sorted(exports)[0]
            for mode, margs in MODES.items():
                margs = list(margs)
                if mode == "arm-single-function":
                    margs += ["-n", first]
                inputs = [comp_path] + ([wat] if mode == "arm-relocatable" else [])
                for inp in inputs:
                    tag = f"{shape} {mode} {inp.suffix}"
                    out = tmp / f"{shape}-{mode}{inp.suffix}.o"
                    rc, log = synth(SYNTH, inp, out, margs)
                    if not args.expect_red:
                        named = "#1191" in log and "meld fuse" in log \
                            and "WebAssembly COMPONENT" in log
                        ok = rc != 0 and named and not out.exists()
                        refusals += ok
                        print(f"  [{'ok ' if ok else 'BUG'}] {tag}: rc={rc} "
                              f"named={named} output={'present' if out.exists() else 'absent'}")
                        if not ok:
                            failures.append(f"{tag}: not refused loudly (rc={rc}, named={named})")
                        continue
                    # --expect-red: the pre-fix binary ACCEPTS, and is wrong —
                    # or, on the single-function path, cannot FIND an export
                    # the component declares (the same flattening, seen from
                    # the other side: the declared name is not in the merged
                    # export map).
                    if rc != 0:
                        missing = mode == "arm-single-function" and "#1191" not in log \
                            and f"Function '{first}' not found" in log
                        # shape 5: the arena binder rewrote the COMPONENT
                        # before decode and reported its own internal bug.
                        arena = shape == "shape5" and mode == "arm-self-contained" \
                            and "#1191" not in log and "#418 internal" in log
                        accepted += missing or arena
                        why = (f" — declared export '{first}' not found" if missing
                               else " — misleading '#418 internal' arena-bind error"
                               if arena else "")
                        print(f"  [{'red' if missing or arena else 'BUG'}] {tag}: rc={rc}{why}")
                        missing = missing or arena
                        if not missing:
                            failures.append(f"{tag}: expected the pre-fix ACCEPT, got rc={rc}")
                        continue
                    accepted += 1
                    if mode != "arm-relocatable" or inp.suffix != ".wasm":
                        print(f"  [red] {tag}: accepted rc=0")
                        continue
                    defined, undefined = symtab(out)
                    diff = defined != exports or undefined != imports
                    mismatches += diff
                    print(f"  [{'red' if diff else '---'}] {tag}: defines {sorted(defined)} "
                          f"(declared {sorted(exports)}), undefined {sorted(undefined)} "
                          f"(declared {sorted(imports)})")
                    if shape == "shape4" and "g" in defined:
                        code, funcs = load_rel(out)
                        got = run_arm(code, funcs["g"])
                        executions += 1
                        wrong = got != values["g"]
                        wrong_values += wrong
                        print(f"  [{'red' if wrong else '---'}] {tag}: EXECUTED g() -> {got} "
                              f"(wasmtime component runtime {values['g']})")

        print("=== controls (core modules) ===")
        twin_wasm = bytes(wasmtime.wat2wasm(TWIN.read_text()))
        executions += control(tmp, "twin", TWIN, twin_wasm, failures)

        fused = FUSED.read_bytes()
        fsha = hashlib.sha256(fused).hexdigest()
        if fsha != FUSED_SHA256:
            failures.append(f"fused fixture sha256 {fsha} != pinned {FUSED_SHA256}")
        att = fused[fused.index(b'{"version"'):]
        att = json.loads(att[: att.rindex(b"}") + 1])
        s4 = hashlib.sha256(bytes(wasmtime.wat2wasm(SHAPES["shape4"].read_text()))).hexdigest()
        prov = att["inputs"][0]["artifact"]["hash"] == s4 == SHAPE4_SHA256 \
            and att["tool"] == {"name": "meld", "version": "0.9.0"}
        print(f"  [{'ok ' if prov else 'BUG'}] fused fixture: sha256 {fsha[:16]}, meld "
              f"{att['tool']['version']} attestation input == shape 4 ({s4[:16]})")
        if not prov:
            failures.append("fused fixture provenance does not match shape 4")
        executions += control(tmp, "meld-fused", FUSED, fused, failures)

    nmodes = sum(1 + (m == "arm-relocatable") for m in MODES)
    if args.expect_red:
        if accepted != len(SHAPES) * nmodes:
            failures.append(f"expected every shape x mode red pre-fix, got {accepted}")
        if mismatches != len(SHAPES):
            failures.append(f"expected {len(SHAPES)} symbol-table mismatches, got {mismatches}")
        if wrong_values < 1:
            failures.append("expected shape 4's g to execute to a wrong value")
        print(f"red cases: {accepted}\nsymbol mismatches: {mismatches}\n"
              f"wrong values: {wrong_values}")
    else:
        if refusals != len(SHAPES) * nmodes:
            failures.append(f"refusals {refusals} != {len(SHAPES) * nmodes}")
        print(f"refusals: {refusals}")
    print(f"executions: {executions}")
    if executions < 4:
        failures.append(f"executions {executions} < 4 (vacuous)")
    if failures:
        print("RESULT: FAIL")
        for f in failures:
            print("  - " + f)
        sys.exit(1)
    print("RESULT: PASS" + (" (pre-fix defect reproduced)" if args.expect_red else ""))


if __name__ == "__main__":
    main()
