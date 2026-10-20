#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 136
"""RQ-88-JESSDIVERGE10 (#1436) — a float local's home register rewritten while
an operand-stack entry still READS it.

WHAT THE REPORTER'S MODULE DOES. `ekf@0.10.0#estimate` (jess, pulseengine/jess
repro/synth-1436/c.loom.wasm) computes the gravity-compensated down-axis
acceleration as one wasm expression:

    ... f32.sub  local.tee 18      ;; t18 = az - bias, LEFT ON THE STACK
    ...                            ;; t18 is still the deepest operand
    ... f32.sub  local.tee 18      ;; local 18 REDEFINED mid-expression
    ... f32.add  f32.add           ;; consumes the OLD t18 at the bottom
    f32.const 9.81  f32.add  f32.store offset=1448

The direct selector (`--relocatable` forces it) lowers `local.get`/`local.tee`
of a register-homed f32 local by pushing a REFERENCE to the home S-register,
not a copy. The second `local.tee 18` writes the home register (s6 in the
reporter's object, `vmov s6, r0` at object pc 0x708) while the first tee's
entry still names s6, so the final add reads the NEW value. For the reporter's
input (az = -9.81, identity attitude) wasm stores 0x00000000 at frame+1448 and
the ARM object stores 0x411cf5c3 (+9.81) at object pc 0x748 — the first
divergent linear-memory write of the whole tick, found by an execution
differential of every store against wasmtime. From there the uncompensated
+9.81 integrates into vel-d: 0x3c20ba20 at tick 1, 0x41221afe (+10.13 m/s) at
tick 1024, bit-identical to the reporter's QEMU trace.

The INTEGER twin of this hazard was closed as #989 (`snapshot_home_reg_aliases`
before every write of a param/promoted home). The float homes had no such
snapshot: the `try_lower_f32` LocalGet comment still said "Phase 1 never
rewrites a home while referenced (f32 local.set declines)", which stopped being
true when #719 phase 1b lowered f32 `local.set`.

THE LEGS. Every leg is executed bit-exact against wasmtime.
  tee_set / tee_tee / get_set   a non-param local, three ways to alias it
  param_get_set                 an AAPCS-VFP PARAM home (S0/D0) rewritten
  store_shape                   the reporter's shape: an i32 address below
  if_get_set / block_get_set /  the alias pushed BEFORE a structured op and the
  loop_get_set                  local rewritten INSIDE it — a copy made at the
                                write would run on one path only, so the entry
                                must be detached at the construct's entry
  *_f64                         the D-register homes (cortex-m7dp)
  none_f32 / none_f64           NEGATIVE CONTROLS: the same arithmetic with the
                                second write going to a DIFFERENT local — green
                                before and after; if they ever go red the
                                harness, not the selector, is wrong

RED before the fix, MEASURED at 0.87.0 + this tree's unfixed selector: 88 of
136 vectors wrong, 15 of 17 exports — every leg except the two negative
controls (the control-flow legs agree only on the vectors whose arm is not
taken). GREEN after: 0 of 136 -> `RESULT: PASS`.

The WAT is embedded rather than added to `scripts/repro/*.wat`, because the
corpus-wide sweeps derive pinned counts from that directory and this lane
should not move them.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=/path/to/synth python3 scripts/repro/vfp_home_alias_1436_differential.py
"""
import os
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_D0,
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R11,
    UC_ARM_REG_S0,
    UC_ARM_REG_SP,
)

try:
    from unicorn.arm_const import UC_ARM_REG_C1_C0_2, UC_ARM_REG_FPEXC
except ImportError:  # pragma: no cover - older unicorn
    UC_ARM_REG_C1_C0_2 = UC_ARM_REG_FPEXC = None

SYNTH = os.environ.get("SYNTH_BIN") or os.environ.get("SYNTH", "./target/debug/synth")

WAT = r"""
(module
  (memory 1)
  (func (export "tee_set_f32") (param f32 f32 f32) (result f32) (local f32)
    local.get 0 local.get 1 f32.sub local.tee 3
    local.get 3 local.get 2 f32.mul local.set 3
    local.get 3 f32.add)
  (func (export "tee_tee_f32") (param f32 f32 f32) (result f32) (local f32)
    local.get 0 local.get 1 f32.sub local.tee 3
    local.get 3 local.get 2 f32.mul local.tee 3
    f32.add)
  (func (export "get_set_f32") (param f32 f32 f32) (result f32) (local f32)
    local.get 0 local.get 1 f32.sub local.set 3
    local.get 3
    local.get 3 local.get 2 f32.mul local.set 3
    local.get 3 f32.add)
  (func (export "param_get_set_f32") (param f32 f32 f32) (result f32)
    local.get 0
    local.get 1 local.get 2 f32.mul local.set 0
    local.get 0 f32.sub)
  (func (export "store_shape_f32") (param f32 f32 f32) (result f32) (local f32)
    i32.const 64
    local.get 0 local.get 1 f32.sub local.tee 3
    local.get 3 local.get 2 f32.mul local.set 3
    local.get 3 f32.add
    f32.store offset=4
    i32.const 68 f32.load)
  (func (export "if_get_set_f32") (param f32 f32 f32) (result f32) (local f32)
    local.get 0 local.set 3
    local.get 3
    local.get 2 f32.const 0 f32.gt
    if
      local.get 1 local.set 3
    end
    local.get 3 f32.sub)
  (func (export "block_get_set_f32") (param f32 f32 f32) (result f32) (local f32)
    local.get 0 local.set 3
    local.get 3
    block
      local.get 2 f32.const 0 f32.gt
      br_if 0
      local.get 1 local.set 3
    end
    local.get 3 f32.sub)
  (func (export "loop_get_set_f32") (param f32 f32 f32) (result f32) (local f32 i32)
    local.get 0 local.set 3
    local.get 3
    loop
      local.get 3 local.get 1 f32.add local.set 3
      local.get 4 i32.const 1 i32.add local.tee 4
      i32.const 3 i32.lt_u
      br_if 0
    end
    local.get 3 f32.sub)
  (func (export "none_f32") (param f32 f32 f32) (result f32) (local f32 f32)
    local.get 0 local.get 1 f32.sub local.tee 3
    local.get 3 local.get 2 f32.mul local.set 4
    local.get 4 f32.add)
  (func (export "tee_set_f64") (param f64 f64 f64) (result f64) (local f64)
    local.get 0 local.get 1 f64.sub local.tee 3
    local.get 3 local.get 2 f64.mul local.set 3
    local.get 3 f64.add)
  (func (export "tee_tee_f64") (param f64 f64 f64) (result f64) (local f64)
    local.get 0 local.get 1 f64.sub local.tee 3
    local.get 3 local.get 2 f64.mul local.tee 3
    f64.add)
  (func (export "get_set_f64") (param f64 f64 f64) (result f64) (local f64)
    local.get 0 local.get 1 f64.sub local.set 3
    local.get 3
    local.get 3 local.get 2 f64.mul local.set 3
    local.get 3 f64.add)
  (func (export "param_get_set_f64") (param f64 f64 f64) (result f64)
    local.get 0
    local.get 1 local.get 2 f64.mul local.set 0
    local.get 0 f64.sub)
  (func (export "if_get_set_f64") (param f64 f64 f64) (result f64) (local f64)
    local.get 0 local.set 3
    local.get 3
    local.get 2 f64.const 0 f64.gt
    if
      local.get 1 local.set 3
    end
    local.get 3 f64.sub)
  (func (export "block_get_set_f64") (param f64 f64 f64) (result f64) (local f64)
    local.get 0 local.set 3
    local.get 3
    block
      local.get 2 f64.const 0 f64.gt
      br_if 0
      local.get 1 local.set 3
    end
    local.get 3 f64.sub)
  (func (export "loop_get_set_f64") (param f64 f64 f64) (result f64) (local f64 i32)
    local.get 0 local.set 3
    local.get 3
    loop
      local.get 3 local.get 1 f64.add local.set 3
      local.get 4 i32.const 1 i32.add local.tee 4
      i32.const 3 i32.lt_u
      br_if 0
    end
    local.get 3 f64.sub)
  (func (export "none_f64") (param f64 f64 f64) (result f64) (local f64 f64)
    local.get 0 local.get 1 f64.sub local.tee 3
    local.get 3 local.get 2 f64.mul local.set 4
    local.get 4 f64.add)
)
"""

# The reporter's own operands are in here: (-9.81, 0, 0) is az with a zero
# bias and an identity-attitude product. -0.0 is present because the cheap
# "copy" is an arithmetic identity and -0.0 + 0.0 is +0.0. The third operand's
# sign selects the taken/not-taken arm of the control-flow legs, so both arms
# execute. NaN is absent: f32/f64 arithmetic may return any NaN payload.
ARGS = (
    (5.0, 2.0, 3.0),
    (1.5, -0.25, 4.0),
    (-9.81, 0.0, 0.0),
    (2.0, 7.0, -1.0),
    (-0.0, 0.0, 2.0),
    (1e-3, -3.5, -0.5),
    (0.30, -0.15, 0.07),
    (100.0, 0.125, 1.0),
)
CONTROLS = ("none_f32", "none_f64")


def exports():
    return re.findall(r'\(export "([a-z0-9_]+)"\)', WAT)


def expected_emulations():
    """DERIVED from the export and argument tables (#1331: never a typed product)."""
    return len(exports()) * len(ARGS)


def declared_floor():
    m = re.search(r"^# ci-checks: emulations >= (\d+)$", Path(__file__).read_text(), re.M)
    if not m:
        sys.exit("REFUSE: no `# ci-checks: emulations >= N` header in this file")
    return int(m.group(1))


def compile_obj(wasm, out):
    r = subprocess.run(
        [SYNTH, "compile", wasm, "-o", out, "-t", "cortex-m7dp", "--cortex-m",
         "--relocatable", "--all-exports"],
        capture_output=True, text=True,
    )
    return r.returncode, r.stdout + r.stderr


def load(obj):
    e = ELFFile(open(obj, "rb"))
    text = e.get_section_by_name(".text").data()
    syms = {}
    for s in e.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"]
    return text, syms


CODE, LIN, STACK, RET = 0x100000, 0x20000000, 0x30000, 0x80000


def run(text, addr, wide, args):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    uc.mem_map(CODE, (len(text) + 0xFFF) & ~0xFFF)
    uc.mem_write(CODE, text)
    uc.mem_map(RET, 0x1000)
    uc.mem_map(LIN, 0x10000)
    uc.mem_map(STACK, 0x10000)
    if UC_ARM_REG_C1_C0_2 is not None:
        uc.reg_write(UC_ARM_REG_C1_C0_2, 0x00F00000)
    if UC_ARM_REG_FPEXC is not None:
        uc.reg_write(UC_ARM_REG_FPEXC, 0x40000000)
    uc.reg_write(UC_ARM_REG_SP, STACK + 0xF000)
    uc.reg_write(UC_ARM_REG_R11, LIN)
    for i, v in enumerate(args):
        if wide:
            uc.reg_write(UC_ARM_REG_D0 + i, struct.unpack("<Q", struct.pack("<d", v))[0])
        else:
            uc.reg_write(UC_ARM_REG_S0 + i, struct.unpack("<I", struct.pack("<f", v))[0])
    uc.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        uc.emu_start((CODE + (addr & ~1)) | 1, RET, count=4000)
    except UcError as ex:
        return None, f"{ex} at pc={uc.reg_read(UC_ARM_REG_PC):#x}"
    if uc.reg_read(UC_ARM_REG_PC) & ~1 != RET:
        return None, "instruction budget exhausted"
    if wide:
        return uc.reg_read(UC_ARM_REG_D0) & ((1 << 64) - 1), ""
    return uc.reg_read(UC_ARM_REG_S0) & 0xFFFFFFFF, ""


def bits(v, wide):
    return struct.unpack("<Q", struct.pack("<d", v))[0] if wide else \
        struct.unpack("<I", struct.pack("<f", v))[0]


def main():
    if expected_emulations() != declared_floor():
        sys.exit(f"REFUSE: header floor {declared_floor()} != derived "
                 f"{expected_emulations()} — update the header with the tables (#1331)")
    with tempfile.TemporaryDirectory() as td:
        wasm, obj = os.path.join(td, "m.wasm"), os.path.join(td, "m.o")
        Path(wasm).write_bytes(wasmtime.wat2wasm(WAT))
        rc, log = compile_obj(wasm, obj)
        if rc != 0:
            print(log)
            print("RESULT: FAIL (compile)")
            return 1
        declined = [ln for ln in log.splitlines() if "skipping function" in ln]
        text, syms = load(obj)
        engine = wasmtime.Engine()
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, wasmtime.Module(engine, wasmtime.wat2wasm(WAT)), [])
        emulations, fails, bad_exports = 0, [], set()
        for name in exports():
            if name not in syms:
                fails.append(f"{name}: absent from the symtab (declined): {declined}")
                continue
            wide = name.endswith("f64")
            for args in ARGS:
                a = tuple(struct.unpack("<f", struct.pack("<f", x))[0] for x in args) \
                    if not wide else args
                want = bits(inst.exports(store)[name](store, *a), wide)
                got, err = run(text, syms[name], wide, a)
                emulations += 1
                if got != want:
                    bad_exports.add(name)
                    fails.append(f"{name}{a}: got {err or hex(got)} want {want:#x}")
        for f in fails:
            print("  FAIL", f)
        controls_bad = sorted(bad_exports & set(CONTROLS))
        print(f"vfp-home-alias: {emulations} emulation(s), {len(fails)} divergent, "
              f"{len(bad_exports)} of {len(exports())} exports wrong")
        if controls_bad:
            print(f"  NEGATIVE CONTROL RED: {controls_bad} — the harness is wrong, not the fix")
        if emulations < declared_floor():
            print(f"  VACUOUS: {emulations} < floor {declared_floor()}")
            print("RESULT: FAIL")
            return 1
        print("RESULT: PASS" if not fails else "RESULT: FAIL")
        return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
