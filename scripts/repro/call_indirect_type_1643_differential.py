#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 160
"""#1643 — `call_indirect` type check under WASM 3.0 (GC proposal) type rules:
iso-recursive type equivalence across `rec` groups, and declared subtyping.

# The defect

synth's `call_indirect` type check (#642 closed world, #676 runtime sidecar on
ARM, #851 on AArch64) compared STRUCTURAL signature strings. WASM 3.0 type
equality is iso-recursive: a `(func)` declared in a rec group of a different
shape, or at a different position in its group, is a DIFFERENT type; a `sub`
(non-final) `(func)` and a `final` one are different types; and §4.4.8 checks
that the callee's type is a SUBTYPE of the expected one, not that they are
equal. With structural strings every `(func)` was one class, so the six spec
directives type-rec.wast:183/192 and type-subtyping.wast:314/315/345/346
compiled with rc 0 and made the call where wasmtime traps "indirect call type
mismatch" — 12 silent wrong-code results on the #1636 runner's two legs.

# The fix this gates

The decoder canonicalises the type section with wasmparser's validator (the
canonicalisation wasmtime's own check rests on) and the class id IS the
canonical type id; the closed-world verdict is `<:` over the declared supertype
chain; and an EQUALITY compare (the ARM sidecar CMP, every AArch64 dispatch)
is refused LOUDLY for an expected type that has a strict declared subtype in
the funcref region — equality would trap a call the spec makes.

# What this oracle runs

Every case's expected outcome is wasmtime's (GC enabled), never this table's.
Six modules — the four spec modules VERBATIM plus two hand modules — on three
legs: cortex-m4 (default bounds) and cortex-m7dp `--safety-bounds software`,
the #1636 runner's two legs, as self-contained images booted through their OWN
shipped `Reset_Handler`; and AArch64 (`-b aarch64`), linked by this harness.

  hand_rec  a HETEROGENEOUS table (runtime check) of five `(func (result i32))`
            functions whose types sit in: rec group A; a group of A's exact
            shape (EQUIVALENT — the call must succeed); a group where the func
            is at position 1 (different); an explicit singleton group (equal
            to a plain `(type (func ...))`); and a two-type group (its two
            members differ from each other).
  hand_sub  `$t2 <: $t1` plus an unrelated final type in one table. Calling
            through `$t2`/`$u` is an exact equality check (no strict subtype
            of either in the table); through `$t1` equality would false-trap
            slot 0, so synth must LOUD-DECLINE it (EXPECTED_DECLINES).

Grading per (leg, module, export, index): synth's value / void return / trap
(a UDF on ARM, a BRK on AArch64 — any stop that is not the planted return
address) must equal wasmtime's. A symbol absent from the image passes ONLY if
it is an EXPECTED_DECLINES entry AND the compile's stderr names the function
as skipped (a loud refusal); the table is exact both ways — an entry that now
compiles is RED, so a decline cannot outlive its reason.

Red-first: on c20d37b2 (pre-fix) this is RED — the spec trap cases run the
call (missing-trap) on all three legs, and `hand_rec`'s cross-group cases
return values where wasmtime traps.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/repro/call_indirect_type_1643_differential.py
"""

import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_ARCH_ARM64, UC_MODE_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm64_const import UC_ARM64_REG_LR, UC_ARM64_REG_SP, UC_ARM64_REG_W0, UC_ARM64_REG_X0
from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_PC, UC_ARM_REG_R0, UC_ARM_REG_SP

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
M32 = 0xFFFFFFFF

# ---- the modules -----------------------------------------------------------

# type-rec.wast:170 / 179 / 188 and type-subtyping.wast:290 / 318, verbatim.
SPEC_REC_EQUIV = """(module
  (rec (type $f1 (func)) (type (struct)))
  (rec (type $f2 (func)) (type (struct)))
  (table funcref (elem $f1))
  (func $f1 (type $f1))
  (func (export "run") (call_indirect (type $f2) (i32.const 0)))
)"""
SPEC_REC_POS = """(module
  (rec (type $f1 (func)) (type (struct)))
  (rec (type (struct)) (type $f2 (func)))
  (table funcref (elem $f1))
  (func $f1 (type $f1))
  (func (export "run") (call_indirect (type $f2) (i32.const 0)))
)"""
SPEC_REC_SHAPE = """(module
  (rec (type $f1 (func)) (type (struct)))
  (rec (type $f2 (func)))
  (table funcref (elem $f1))
  (func $f1 (type $f1))
  (func (export "run") (call_indirect (type $f2) (i32.const 0)))
)"""
SPEC_SUB_FINAL = """(module
  (type $t1 (sub (func)))
  (type $t2 (sub final (func)))
  (func $f1 (type $t1))
  (func $f2 (type $t2))
  (table funcref (elem $f1 $f2))
  (func (export "fail1")
    (block (call_indirect (type $t1) (i32.const 1)))
  )
  (func (export "fail2")
    (block (call_indirect (type $t2) (i32.const 0)))
  )
  (func (export "fail3")
    (ref.cast (ref $t1) (table.get (i32.const 1)))
    (drop)
  )
  (func (export "fail4")
    (ref.cast (ref $t2) (table.get (i32.const 0)))
    (drop)
  )
)"""
SPEC_SUB_CHAIN = """(module
  (type $t1 (sub (func)))
  (type $t2 (sub $t1 (func)))
  (type $t3 (sub $t2 (func)))
  (type $t4 (sub final (func)))
  (func $f2 (type $t2))
  (func $f3 (type $t3))
  (table (ref null $t2) (elem $f2 $f3))
  (func (export "run")
    (call_indirect (type $t1) (i32.const 0))
    (call_indirect (type $t1) (i32.const 1))
    (call_indirect (type $t2) (i32.const 0))
    (call_indirect (type $t2) (i32.const 1))
    (call_indirect (type $t3) (i32.const 1))
  )
  (func (export "fail1")
    (call_indirect (type $t3) (i32.const 0))
  )
  (func (export "fail2")
    (call_indirect (type $t4) (i32.const 0))
  )
)"""

HAND_REC = """(module
  (rec (type $a1 (func (result i32))) (type (struct)))
  (rec (type $a2 (func (result i32))) (type (struct)))
  (rec (type (struct)) (type $b (func (result i32))))
  (rec (type $c (func (result i32))))
  (type $p (func (result i32)))
  (rec (type $d1 (func (result i32))) (type $d2 (func (result i32))))
  (func $fa (type $a1) (i32.const 11))
  (func $fb (type $b) (i32.const 22))
  (func $fc (type $c) (i32.const 33))
  (func $fd1 (type $d1) (i32.const 44))
  (func $fd2 (type $d2) (i32.const 55))
  (table funcref (elem $fa $fb $fc $fd1 $fd2))
  (func (export "via_a2") (param i32) (result i32) (call_indirect (type $a2) (local.get 0)))
  (func (export "via_b") (param i32) (result i32) (call_indirect (type $b) (local.get 0)))
  (func (export "via_p") (param i32) (result i32) (call_indirect (type $p) (local.get 0)))
  (func (export "via_d1") (param i32) (result i32) (call_indirect (type $d1) (local.get 0)))
  (func (export "via_d2") (param i32) (result i32) (call_indirect (type $d2) (local.get 0)))
)"""
HAND_SUB = """(module
  (type $t1 (sub (func (result i32))))
  (type $t2 (sub $t1 (func (result i32))))
  (type $u (func (result i32)))
  (func $f2 (type $t2) (i32.const 2))
  (func $fu (type $u) (i32.const 9))
  (table funcref (elem $f2 $fu))
  (func (export "via_t1") (param i32) (result i32) (call_indirect (type $t1) (local.get 0)))
  (func (export "via_t2") (param i32) (result i32) (call_indirect (type $t2) (local.get 0)))
  (func (export "via_u") (param i32) (result i32) (call_indirect (type $u) (local.get 0)))
)"""

# module -> (wat, {export: [args tuples]}). A void no-param export runs once.
MODULES = {
    "spec_rec_equiv": (SPEC_REC_EQUIV, {"run": [()]}),
    "spec_rec_pos": (SPEC_REC_POS, {"run": [()]}),
    "spec_rec_shape": (SPEC_REC_SHAPE, {"run": [()]}),
    "spec_sub_final": (SPEC_SUB_FINAL, {"fail1": [()], "fail2": [()]}),
    "spec_sub_chain": (SPEC_SUB_CHAIN, {"run": [()], "fail1": [()], "fail2": [()]}),
    "hand_rec": (HAND_REC, {e: [(i,) for i in range(7)]
                            for e in ("via_a2", "via_b", "via_p", "via_d1", "via_d2")}),
    "hand_sub": (HAND_SUB, {e: [(i,) for i in range(4)]
                            for e in ("via_t1", "via_t2", "via_u")}),
}

LEGS = {
    "cortex-m4": ["--target", "cortex-m4"],
    "cortex-m7dp": ["--target", "cortex-m7dp", "--safety-bounds", "software"],
    "aarch64": ["-b", "aarch64"],
}

# (leg, module, export) -> why it is a LOUD decline, not a result. Exact both
# ways. Each names the shape that cannot be checked soundly by one compare.
EXPECTED_DECLINES = {
    # A homogeneous table whose only slot's type is not `<:` the expected type:
    # the closed world fails and no runtime sidecar exists (#642 decline shape).
    ("cortex-m4", "spec_rec_pos", "run"): "closed-world reject (#642)",
    ("cortex-m4", "spec_rec_shape", "run"): "closed-world reject (#642)",
    ("cortex-m7dp", "spec_rec_pos", "run"): "closed-world reject (#642)",
    ("cortex-m7dp", "spec_rec_shape", "run"): "closed-world reject (#642)",
    # `$t2 <: $t1` sits in a mixed table: an equality CMP would false-trap.
    ("cortex-m4", "hand_sub", "via_t1"): "strict subtype in table (#1643)",
    ("cortex-m7dp", "hand_sub", "via_t1"): "strict subtype in table (#1643)",
    ("aarch64", "hand_sub", "via_t1"): "strict subtype in table (#1643)",
    ("aarch64", "spec_sub_chain", "run"): "strict subtype in table (#1643)",
}

TRAP, VOID = "trap", "void"


def wasmtime_outcome(wat, export, args):
    cfg = wasmtime.Config()
    cfg.wasm_gc = True
    cfg.wasm_function_references = True
    engine = wasmtime.Engine(cfg)
    store = wasmtime.Store(engine)
    f = wasmtime.Instance(store, wasmtime.Module(engine, wat), []).exports(store)[export]
    try:
        r = f(store, *args)
    except wasmtime.Trap as t:
        if "indirect call type mismatch" not in t.message and "undefined element" not in t.message \
                and "uninitialized element" not in t.message:
            sys.exit(f"unexpected wasmtime trap {t.message!r}")
        return TRAP
    return VOID if r is None else r & M32


def compile_leg(wat_path, leg, out):
    r = subprocess.run([SYNTH, "compile", str(wat_path), *LEGS[leg], "--all-exports",
                        "--allow-skipped-exports", "-o", str(out)],
                       capture_output=True, text=True, timeout=300)
    if r.returncode != 0 or not out.exists():
        sys.exit(f"compile failed ({leg}, {wat_path.name}): {r.stderr[-400:]}")
    return r.stdout + r.stderr


def symtab(f):
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            return sec
    sys.exit("no symtab")


class ArmImage:
    """The self-contained image, booted through its own Reset_Handler up to
    the startup's call scaffold (the #275 harness), on zeroed RAM."""
    FLASH, RAM, RAM_SIZE, RET = 0x0, 0x2000_0000, 0x40000, 0x000F_0000

    def __init__(self, path):
        f = ELFFile(open(path, "rb"))
        if f["e_type"] != "ET_EXEC":
            sys.exit(f"{path}: not a self-contained image")
        text = f.get_section_by_name(".text")
        self.code, self.base = text.data(), text["sh_addr"]
        self.syms = {s.name: s["st_value"] for s in symtab(f).iter_symbols() if s.name}
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        self.mu.mem_map(self.FLASH, 0x100000)
        self.mu.mem_map(self.RAM, self.RAM_SIZE)
        self.mu.mem_map(0xE000E000, 0x1000)
        self.mu.mem_write(self.base, self.code)
        self.sp = int.from_bytes(self.code[0:4], "little")
        reset = self.syms["Reset_Handler"]
        stop = self.code.find(b"\x01\x48\x80\x47", (reset & ~1) - self.base)
        if stop < 0:
            sys.exit("startup call scaffold not found")
        self.mu.reg_write(UC_ARM_REG_SP, self.sp)
        self.mu.emu_start(reset | 1, self.base + stop, count=100000)

    def has(self, name):
        return name in self.syms

    def call(self, name, args, void):
        self.mu.reg_write(UC_ARM_REG_SP, self.sp)
        self.mu.reg_write(UC_ARM_REG_LR, self.RET | 1)
        for i, a in enumerate(args):
            self.mu.reg_write(UC_ARM_REG_R0 + i, a & M32)
        try:
            self.mu.emu_start(self.syms[name] | 1, self.RET, count=100000)
        except UcError:
            return self._trap_kind()
        return VOID if void else self.mu.reg_read(UC_ARM_REG_R0) & M32

    def _trap_kind(self):
        pc = self.mu.reg_read(UC_ARM_REG_PC)
        lo = pc - self.base
        if 0 <= lo < len(self.code) - 1 and self.code[lo:lo + 2] == b"\x00\xde":
            return TRAP  # the deterministic §4.4.8 UDF
        return f"fault@{pc:#x}"


class A64Object:
    """`-b aarch64` object, placed and relocated by this harness (the #851
    linker)."""
    CODE, DATA, STK, RET = 0x100000, 0x400000, 0x200000, 0x300000

    def __init__(self, path):
        f = ELFFile(open(path, "rb"))
        secs = list(f.iter_sections())
        ts, ds = f.get_section_by_name(".text"), f.get_section_by_name(".data")
        self.text = bytearray(ts.data())
        self.data = bytes(ds.data()) if ds is not None else b""
        ti, di = secs.index(ts), (secs.index(ds) if ds is not None else -1)
        addr, self.syms = {}, {}
        for i, s in enumerate(symtab(f).iter_symbols()):
            if s["st_shndx"] == ti:
                a = self.CODE + s["st_value"]
            elif di >= 0 and s["st_shndx"] == di:
                a = self.DATA + s["st_value"]
            else:
                continue
            addr[i] = a
            if s.name:
                self.syms.setdefault(s.name, a)
        rela = f.get_section_by_name(".rela.text")
        for r in (rela.iter_relocations() if rela is not None else []):
            off, typ, s = r["r_offset"], r["r_info_type"], addr[r["r_info"] >> 32] + r["r_addend"]
            site, w = self.CODE + off, struct.unpack_from("<I", self.text, off)[0]
            if typ in (282, 283):  # JUMP26 / CALL26
                w = (w & 0xFC000000) | (((s - site) // 4) & 0x03FFFFFF)
            elif typ == 275:  # ADR_PREL_PG_HI21
                v = ((s >> 12) - (site >> 12)) & 0x1FFFFF
                w &= ~((0x3 << 29) | (0x7FFFF << 5))
                w |= ((v & 0x3) << 29) | (((v >> 2) & 0x7FFFF) << 5)
            elif typ == 277:  # ADD_ABS_LO12_NC
                w = (w & ~(0xFFF << 10)) | ((s & 0xFFF) << 10)
            else:
                sys.exit(f"unexpected relocation type {typ}")
            struct.pack_into("<I", self.text, off, w)

    def has(self, name):
        return name in self.syms

    def call(self, name, args, void):
        mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
        mu.mem_map(self.CODE, 0x20000)
        mu.mem_map(self.DATA, 0x10000)
        mu.mem_map(self.STK - 0x10000, 0x20000)
        mu.mem_map(self.RET & ~0xFFF, 0x1000)
        mu.mem_write(self.CODE, bytes(self.text))
        if self.data:
            mu.mem_write(self.DATA, self.data)
        mu.reg_write(UC_ARM64_REG_SP, self.STK)
        mu.reg_write(UC_ARM64_REG_LR, self.RET)
        for i, a in enumerate(args):
            mu.reg_write(UC_ARM64_REG_X0 + i, a & M32)
        try:
            mu.emu_start(self.syms[name], self.RET, count=200000)
        except UcError:
            return TRAP  # a guarded `brk`
        return VOID if void else mu.reg_read(UC_ARM64_REG_W0) & M32


def main() -> int:
    if not Path(SYNTH).is_file():
        print(f"FAIL: synth not found at {SYNTH}")
        return 1
    fails, executed, traps_ok, values_ok, seen_declines = 0, 0, 0, 0, set()
    with tempfile.TemporaryDirectory() as td:
        td = Path(td)
        for mod, (wat, exports) in MODULES.items():
            src = td / f"{mod}.wat"
            src.write_text(wat)
            want = {(e, a): wasmtime_outcome(wat, e, a) for e, al in exports.items() for a in al}
            for leg in LEGS:
                out = td / f"{mod}.{leg}.o"
                log = compile_leg(src, leg, out)
                img = A64Object(out) if leg == "aarch64" else ArmImage(out)
                for (e, a), w in sorted(want.items()):
                    key = (leg, mod, e)
                    if not img.has(e):
                        loud = f"skipping function '{e}'" in log
                        if key in EXPECTED_DECLINES and loud:
                            seen_declines.add(key)
                            continue
                        fails += 1
                        print(f"  FAIL {leg} {mod}.{e}{a}: symbol absent "
                              f"({'loud' if loud else 'SILENT'}), not an expected decline; "
                              f"wasmtime={w}")
                        continue
                    if key in EXPECTED_DECLINES and key not in seen_declines:
                        fails += 1
                        print(f"  FAIL {leg} {mod}.{e}: EXPECTED_DECLINES entry now compiles "
                              f"— remove it ({EXPECTED_DECLINES[key]})")
                        seen_declines.add(key)
                    got = img.call(e, a, w == VOID)
                    executed += 1
                    ok = got == w
                    if ok:
                        traps_ok += w == TRAP
                        values_ok += w != TRAP
                    else:
                        fails += 1
                    print(f"  {'ok  ' if ok else 'FAIL'} {leg:11} {mod}.{e}{a}: "
                          f"wasmtime={w} synth={got}")
    stale = set(EXPECTED_DECLINES) - seen_declines
    for k in sorted(stale):
        fails += 1
        print(f"  FAIL EXPECTED_DECLINES entry never observed: {k}")
    print(f"#1643 executed {executed} (traps matched {traps_ok}, values/void matched "
          f"{values_ok}), expected loud declines {len(seen_declines)}")
    if traps_ok == 0 or values_ok == 0:
        print("VACUOUS: a direction (trap or value) was never exercised")
        return 1
    if fails:
        print(f"ORACLE: FAIL — {fails} divergence(s) from wasmtime (#1643)")
        return 1
    print("ORACLE: PASS — call_indirect traps and calls exactly where wasmtime does "
          "under rec-group equivalence and declared subtyping, or declines loudly (#1643)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
