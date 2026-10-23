#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 88
"""RQ-89-INTALIAS (#1566) — an integer local rewritten on ONE path of a
structured construct while an operand-stack entry pushed BEFORE the construct
still READS its home register.

THE DEFECT. The direct selector (`--relocatable` forces it, #197) lowers
`local.get` of a register-homed integer local (a param in r0-r3) by pushing a
REFERENCE to the home register, not a copy. #989 closed the straight-line
get->set->use hazard with `snapshot_home_reg_aliases`: at the `local.set`/
`local.tee` that overwrites the home, every entry still naming it is copied
into a temp and rewritten to the temp. Inside an `if` or a `br_if`-exited
`block` that copy is emitted on the WRITING path only, so on the path that
skips the write the entry names a temp nobody filled:

    local.get 0   local.get 2 if local.get 1 local.set 0 end   local.get 0 i32.sub

lowered to `cmp r2,#0; beq; mov r3,r0; mov r0,r1; subs r4,r3,r0` — with r3
poisoned to 0xdeadbeef, `(10, 3, 0)` returned 0xdeadbee5 where wasm returns 0.
It is SILENT without poisoning, because r3 usually holds a leftover value.

THE FIX (#1566) is the integer twin of the #1436 float detach: at every
`if`/`block`/`loop` ENTRY, `detach_all_home_reg_aliases` snapshots every entry
that still names a core-register local home, so every path reads the value the
local held when the entry was pushed.

THE LEGS. Every leg is executed against wasmtime with EVERY non-argument core
register (r0-r10, r12 minus the arguments; r11 is the linear-memory base)
poisoned to 0xdeadbeef, so an unfilled temp cannot pass by accident.
  if_then_set / if_else_set     the write in either arm of an `if`
  if_then_tee                   the write is a `local.tee` whose value is dropped
  block_brif_set                the write after a `br_if` out of a `block`
  loop_set                      the write inside a `loop` body
  nested_if_in_block            the alias pushed inside a block, write in an if
  block_result_set              a value-carrying block: the write runs before
                                a `br_if` that carries a result out, so the
                                snapshot temp must not collide with the block's
                                designated result register
  if_set_p1_hi                  the alias is param 1 (r1), the write in an if
  i64_if_set                    an i64 PARAM PAIR home (r0:r1) rewritten in an if
                                — unfixed, the VCR-RA-003 validator caught this
                                one (JoinValueNotAvailable) and the export was
                                DECLINED; a declined export counts as a failure
                                here (`--allow-skipped-exports` keeps the other
                                legs measurable)
  none_other_local              NEGATIVE CONTROL: the write goes to a DIFFERENT
                                local — green before and after
  none_consumed_before          NEGATIVE CONTROL: the read is consumed into a
                                temp before the construct — green before and
                                after; if either ever goes red the harness, not
                                the selector, is wrong

The WAT is embedded rather than added to `scripts/repro/*.wat`, because the
corpus-wide sweeps derive pinned counts from that directory and this lane
should not move them.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH_BIN=/path/to/synth python3 scripts/repro/int_home_alias_1566_differential.py
"""
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R4,
    UC_ARM_REG_R5,
    UC_ARM_REG_R6,
    UC_ARM_REG_R7,
    UC_ARM_REG_R8,
    UC_ARM_REG_R9,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_R12,
    UC_ARM_REG_SP,
)

SYNTH = os.environ.get("SYNTH_BIN") or os.environ.get("SYNTH", "./target/debug/synth")
CORE = (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3, UC_ARM_REG_R4,
        UC_ARM_REG_R5, UC_ARM_REG_R6, UC_ARM_REG_R7, UC_ARM_REG_R8, UC_ARM_REG_R9,
        UC_ARM_REG_R10, UC_ARM_REG_R12)
POISON = 0xDEADBEEF

WAT = r"""
(module
  (memory 1)
  (func (export "if_then_set") (param i32 i32 i32) (result i32)
    local.get 0
    local.get 2 if local.get 1 local.set 0 end
    local.get 0 i32.sub)
  (func (export "if_else_set") (param i32 i32 i32) (result i32)
    local.get 0
    local.get 2 if nop else local.get 1 local.set 0 end
    local.get 0 i32.sub)
  (func (export "if_then_tee") (param i32 i32 i32) (result i32)
    local.get 0
    local.get 2 if local.get 1 local.tee 0 drop end
    local.get 0 i32.sub)
  (func (export "block_brif_set") (param i32 i32 i32) (result i32)
    local.get 0
    block local.get 2 br_if 0 local.get 1 local.set 0 end
    local.get 0 i32.sub)
  (func (export "loop_set") (param i32 i32 i32) (result i32) (local i32)
    local.get 0
    loop
      local.get 0 local.get 1 i32.add local.set 0
      local.get 3 i32.const 1 i32.add local.tee 3
      i32.const 3 i32.lt_u
      br_if 0
    end
    local.get 0 i32.sub)
  (func (export "nested_if_in_block") (param i32 i32 i32) (result i32)
    block (result i32)
      local.get 0
      local.get 2 if local.get 1 local.set 0 end
      local.get 0 i32.sub
    end)
  (func (export "block_result_set") (param i32 i32 i32) (result i32)
    local.get 0
    block (result i32)
      local.get 1 local.set 0
      local.get 2
      local.get 2 br_if 0
      drop
      i32.const 5
    end
    local.get 0 i32.sub
    i32.add)
  (func (export "if_set_p1_hi") (param i32 i32 i32) (result i32)
    local.get 1
    local.get 2 if local.get 0 local.set 1 end
    local.get 1 i32.sub)
  (func (export "i64_if_set") (param i64 i32) (result i64)
    local.get 0
    local.get 1 if local.get 1 i64.extend_i32_s local.set 0 end
    local.get 0 i64.sub)
  (func (export "none_other_local") (param i32 i32 i32) (result i32)
    local.get 0
    local.get 2 if local.get 1 local.set 2 end
    local.get 0 i32.sub)
  (func (export "none_consumed_before") (param i32 i32 i32) (result i32)
    local.get 0 i32.const 1 i32.add
    local.get 2 if local.get 1 local.set 0 end
    local.get 0 i32.sub)
)
"""

# The third operand selects the taken/not-taken arm (and, for the i64 leg the
# second), so both paths of every construct execute. The reporter's two calls
# from #1566 — (10, 3, 0) and (10, 3, 1) — are the first two rows.
ARGS = (
    (10, 3, 0),
    (10, 3, 1),
    (0, 0, 0),
    (5, 7, 1),
    (0x7FFFFFFF, -1, 0),
    (-8, 0x12345678, -1),
    (1, 2, 2),
    (-100, 100, 0),
)
CONTROLS = ("none_other_local", "none_consumed_before")


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
        [SYNTH, "compile", wasm, "-o", out, "-t", "cortex-m4", "--cortex-m",
         "--relocatable", "--all-exports", "--allow-skipped-exports"],
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
M32 = 0xFFFFFFFF


def run(text, addr, regs, wide):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    uc.mem_map(CODE, (len(text) + 0xFFF) & ~0xFFF)
    uc.mem_write(CODE, text)
    uc.mem_map(RET, 0x1000)
    uc.mem_map(LIN, 0x10000)
    uc.mem_map(STACK, 0x10000)
    for r in CORE:
        uc.reg_write(r, POISON)
    for i, v in enumerate(regs):
        uc.reg_write(CORE[i], v & M32)
    uc.reg_write(UC_ARM_REG_SP, STACK + 0xF000)
    uc.reg_write(UC_ARM_REG_R11, LIN)
    uc.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        uc.emu_start((CODE + (addr & ~1)) | 1, RET, count=4000)
    except UcError as ex:
        return None, f"{ex} at pc={uc.reg_read(UC_ARM_REG_PC):#x}"
    if uc.reg_read(UC_ARM_REG_PC) & ~1 != RET:
        return None, "instruction budget exhausted"
    lo = uc.reg_read(UC_ARM_REG_R0) & M32
    if wide:
        return lo | ((uc.reg_read(UC_ARM_REG_R1) & M32) << 32), ""
    return lo, ""


def s32(v):
    v &= M32
    return v - (1 << 32) if v & 0x80000000 else v


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
                bad_exports.add(name)
                continue
            wide = name.startswith("i64_")
            for a, b, c in ARGS:
                if wide:
                    # (param i64 i32): the i64 pair in r0:r1 (AAPCS), the i32 in r2.
                    x = (s32(b) << 32) | (a & M32)
                    x = x - (1 << 64) if x & (1 << 63) else x
                    wargs, regs = (x, s32(c)), (x & M32, (x >> 32) & M32, c)
                    mask = (1 << 64) - 1
                else:
                    wargs, regs = (s32(a), s32(b), s32(c)), (a, b, c)
                    mask = M32
                want = inst.exports(store)[name](store, *wargs) & mask
                got, err = run(text, syms[name], regs, wide)
                emulations += 1
                if got != want:
                    bad_exports.add(name)
                    fails.append(f"{name}{wargs}: got {err or hex(got)} want {want:#x}")
        for f in fails:
            print("  FAIL", f)
        controls_bad = sorted(bad_exports & set(CONTROLS))
        print(f"int-home-alias: {emulations} emulation(s), {len(fails)} divergent, "
              f"{len(bad_exports)} of {len(exports())} exports wrong")
        if controls_bad:
            print(f"  NEGATIVE CONTROL RED: {controls_bad} — the harness is wrong, not the fix")
        if emulations < declared_floor():
            print(f"  VACUOUS: {emulations} < floor {declared_floor()}")
            print("RESULT: FAIL")
            return 1
        print("RESULT: PASS" if not fails and not controls_bad else "RESULT: FAIL")
        return 1 if fails or controls_bad else 0


if __name__ == "__main__":
    sys.exit(main())
