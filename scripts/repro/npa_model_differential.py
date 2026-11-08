#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 25
"""RQ-91-NPAMODEL (#1672, #1568, #1604, #1661): memory-0 address provenance
under `--relocatable --native-pointer-abi` is decided ONCE per module, and
every shape is either executed equal to wasmtime or refused loudly with a
named diagnostic — execution differential, red on eab66646, green after.

Under the ABI R11 is 0: a memory-0 access dereferences its address as a
NATIVE pointer, and a wasm static at `C` lives at `__synth_wasm_data + C`.
The module-level decision (`Provenance::memory0_plan`) names the constants to
relocate or refuses the module; the ARM backend validates the emitted stream
(`npa-addr-validate`). Rows, one per shape (EXEC = executed against wasmtime
on the hand linker of npa_const_addr_differential.py, one instance per row):

  #1672 data pointer
    datap_neg     a data word holding a wasm address, loaded and dereferenced
                  (the issue's repro): REFUSED `npa-data-pointer (#1672)`,
                  naming the function, the load site and the segment offset.
                  On eab66646 it compiled and faulted on the raw address.
    str_neg       the `&'static str` shape: segment 1 holds a pointer to a
                  string in segment 0, loaded and dereferenced byte-wise:
                  REFUSED with the same diagnostic.
    datap_near    NEAR MISS: the same pointer word loaded and RETURNED (never
                  dereferenced): EXEC.
    bump_pos      gale's bump allocator (POSITIVE CONTROL): `static mut HEAP`
                  and `static mut OFF` with a stack-pointer global;
                  `alloc(n)` returns HEAP + OFF and bumps OFF — a load from a
                  static flowing into an address as an INDEX on a static
                  base. A store through the returned pointer and a load back:
                  EXEC.
  #1568 residuals
    arith / sel   a constant static through arithmetic and through a select:
                  EXEC (eab66646 faulted on both, 1 of 4 equal).
    local_arith   a constant through a local whose definition is arithmetic:
                  EXEC.
    mmio_pos      no data segment, no stack-pointer global: `0x40000000 +` a
                  run-time offset is NATIVE (R2, the MMIO_BASE + reg shape):
                  compiles; executed on the native contract (unicorn maps the
                  peripheral page; wasmtime cannot address it).
  #1604 residuals
    straddle_neg  `i32.const 0xffe + 0` straddling the reservation into a
                  segment: REFUSED `npa-region-straddle (#1604)`.
    fill_neg      `memory.fill` with a COMPUTED constant destination and a
                  run-time length: REFUSED `npa-region-straddle (#1604)`.
    inregion      near miss: `0x1000 + 2` inside the segment: EXEC.
  shape 6 (stack-pointer init ABOVE data)
    below_sp      SP at 0x2000, data at 0x1000 and 0x3000: the positional and
                  the arithmetic constant below the SP and the static above
                  it: EXEC (eab66646 faulted on the two below it).
    below_sp_dyn  a run-time base plus an offset into the data below the SP:
                  REFUSED `npa-dynamic-static-offset (#1568)`.
  #1661
    swb_neg       `--safety-bounds software` on a module touching memory 0:
                  REFUSED `npa-software-bounds (#1661)` (eab66646 compiled
                  and trapped every in-bounds access).

Run: SYNTH=./target/debug/synth python3 scripts/repro/npa_model_differential.py
"""

import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import wasmtime  # noqa: E402
import npa_const_addr_differential as h  # noqa: E402

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

SEG = '(module (memory (export "mem") 1)\n  (data (i32.const 0x1000) "\\11\\22\\33\\44\\55\\66\\77\\88")\n'
ANCHOR = '  (func (export "anchor") (result i32) (i32.load (i32.const 0x1000)))\n'

EXEC = [
    ("datap_near",
     '(module (memory 5376 (pagesize 1))\n'
     '  (data (i32.const 0x1000) "\\11\\22\\33\\44\\55\\66\\77\\88\\04\\10\\00\\00")\n'
     + ANCHOR +
     '  (func (export "word") (result i32) (i32.load (i32.const 0x1008))))',
     [("anchor", ()), ("word", ())]),
    ("bump_pos",
     '(module (memory (export "mem") 2)\n'
     '  (global $sp (mut i32) (i32.const 0x10000))\n'
     '  (data (i32.const 0x10000) "\\de\\c0\\ad\\0b")\n'
     # HEAP: 0x10100..0x10200 (BSS), OFF: 0x10010 (BSS word)
     '  (func $alloc (export "alloc") (param i32) (result i32) (local i32)\n'
     '    (local.set 1 (i32.add (i32.const 0x10100) (i32.load (i32.const 0x10010))))\n'
     '    (i32.store (i32.const 0x10010) (i32.add (i32.load (i32.const 0x10010)) (local.get 0)))\n'
     '    (local.get 1))\n'
     '  (func (export "use") (param i32) (result i32) (local i32)\n'
     '    (local.set 1 (call $alloc (i32.const 8)))\n'
     '    (i32.store (local.get 1) (local.get 0))\n'
     '    (i32.store offset=4 (local.get 1) (i32.const 0x5a5a5a5a))\n'
     '    (i32.add (i32.load (local.get 1)) (i32.load offset=4 (local.get 1))))\n'
     '  (func (export "off") (result i32) (i32.load (i32.const 0x10010)))\n'
     '  (func (export "heap0") (result i32) (i32.load (i32.const 0x10100)))\n'
     '  (func (export "heap8") (result i32) (i32.load (i32.const 0x10108)))\n'
     '  (func (export "anchor") (result i32) (i32.load (i32.const 0x10000))))',
     [("use", (0x11111111,)), ("off", ()), ("heap0", ()), ("use", (0x22222222,)),
      ("off", ()), ("heap8", ()), ("anchor", ())]),
    # The same allocator in an image whose data DOES hold a wasm address
    # (a vtable-like word at 0x10000 naming 0x10004) that is never
    # dereferenced: it must not make the allocator refuse.
    ("bump_ptrdata",
     '(module (memory (export "mem") 2)\n'
     '  (global $sp (mut i32) (i32.const 0x10000))\n'
     '  (data (i32.const 0x10000) "\\04\\00\\01\\00\\de\\c0\\ad\\0b")\n'
     '  (func $alloc (export "alloc") (param i32) (result i32) (local i32)\n'
     '    (local.set 1 (i32.add (i32.const 0x10100) (i32.load (i32.const 0x10010))))\n'
     '    (i32.store (i32.const 0x10010) (i32.add (i32.load (i32.const 0x10010)) (local.get 0)))\n'
     '    (local.get 1))\n'
     '  (func (export "use") (param i32) (result i32) (local i32)\n'
     '    (local.set 1 (call $alloc (i32.const 8)))\n'
     '    (i32.store (local.get 1) (local.get 0))\n'
     '    (i32.load (local.get 1)))\n'
     '  (func (export "vt") (result i32) (i32.load (i32.const 0x10000))))',
     [("use", (0x33333333,)), ("use", (0x44444444,)), ("vt", ())]),
    ("arith_sel", SEG + ANCHOR +
     '  (func (export "arith") (result i32) (i32.load (i32.add (i32.const 0x1000) (i32.const 4))))\n'
     '  (func (export "sel") (param i32) (result i32)\n'
     '    (i32.load (select (i32.const 0x1000) (i32.const 0x1004) (local.get 0))))\n'
     '  (func (export "local_arith") (result i32) (local i32)\n'
     '    (local.set 0 (i32.sub (i32.const 0x1006) (i32.const 2)))\n'
     '    (i32.load (local.get 0))))',
     [("anchor", ()), ("arith", ()), ("sel", (1,)), ("sel", (0,)), ("local_arith", ())]),
    ("inregion", SEG + ANCHOR +
     '  (func (export "f") (result i32) (i32.load (i32.add (i32.const 0x1000) (i32.const 2)))))',
     [("anchor", ()), ("f", ())]),
    ("below_sp",
     '(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x2000))\n'
     '  (data (i32.const 0x1000) "\\11\\22\\33\\44\\55\\66\\77\\88")\n'
     '  (data (i32.const 0x3000) "\\aa\\bb\\cc\\dd")\n'
     '  (func (export "hi") (result i32) (i32.load (i32.const 0x3000)))\n'
     '  (func (export "lo") (result i32) (i32.load (i32.const 0x1000)))\n'
     '  (func (export "lo4") (result i32) (i32.load (i32.const 0x1004)))\n'
     '  (func (export "lo_arith") (result i32) (i32.load (i32.add (i32.const 0x1000) (i32.const 4)))))',
     [("hi", ()), ("lo", ()), ("lo4", ()), ("lo_arith", ())]),
]

REFUSE = [
    ("datap_neg",
     '(module (memory 5376 (pagesize 1))\n'
     '  (data (i32.const 0x1000) "\\11\\22\\33\\44\\55\\66\\77\\88\\04\\10\\00\\00")\n'
     + ANCHOR +
     '  (func (export "tbl") (result i32) (i32.load (i32.load (i32.const 0x1008)))))',
     [], ["npa-data-pointer (#1672)", "function 'tbl'", "load at op 1",
          "segment offset 0x8"]),
    ("str_neg",
     '(module (memory (export "mem") 1)\n'
     '  (data (i32.const 0x1000) "hello")\n'
     '  (data (i32.const 0x2000) "\\00\\10\\00\\00\\05\\00\\00\\00")\n'
     '  (func (export "first") (result i32) (i32.load8_u (i32.load (i32.const 0x2000)))))',
     [], ["npa-data-pointer (#1672)", "function 'first'", "load at op 1",
          "data segment 1", "segment offset 0x0"]),
    ("straddle_neg", SEG + ANCHOR +
     '  (func (export "f") (result i32) (i32.load (i32.add (i32.const 0xffe) (i32.const 0)))))',
     [], ["npa-region-straddle (#1604)", "function 'f'"]),
    ("fill_neg", SEG + ANCHOR +
     '  (func (export "f") (param i32)\n'
     '    (memory.fill (i32.add (i32.const 0xffc) (i32.const 0)) (i32.const 0xab) (local.get 0))))',
     [], ["npa-region-straddle (#1604)", "length computed at run time"]),
    ("below_sp_dyn",
     '(module (memory (export "mem") 1) (global $sp (mut i32) (i32.const 0x2000))\n'
     '  (data (i32.const 0x1000) "\\11\\22\\33\\44\\55\\66\\77\\88")\n'
     '  (func (export "f") (param i32) (result i32) (i32.load offset=0x1004 (local.get 0))))',
     [], ["npa-dynamic-static-offset (#1568)", "function 'f'"]),
    ("swb_neg", SEG + ANCHOR +
     '  (func (export "st0") (param i32 i32) (i32.store (local.get 0) (local.get 1))))',
     ["--safety-bounds", "software"], ["npa-software-bounds (#1661)", "function '"]),
]

MMIO = ('(module (memory 1)\n'
        '  (func (export "rd") (param i32) (result i32)\n'
        '    (i32.load (i32.add (i32.const 0x40000000) (local.get 0))))\n'
        '  (func (export "wr") (param i32 i32)\n'
        '    (i32.store (i32.add (i32.const 0x40000000) (local.get 0)) (local.get 1))))')


def compile_(wat, tmp, label, extra=()):
    src = tmp / f"{label}.wat"
    src.write_text(wat)
    obj = tmp / f"{label}.o"
    if obj.exists():
        obj.unlink()
    r = subprocess.run(
        [SYNTH, "compile", str(src), "-o", str(obj), "--target", "cortex-m3",
         "--all-exports", "--relocatable", "--native-pointer-abi", *extra],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"})
    return r.returncode, (r.stdout or "") + (r.stderr or ""), obj


def execute(tmp, label, wat, seq):
    rc, log, obj = compile_(wat, tmp, label)
    if rc != 0:
        err = [ln for ln in log.splitlines() if ln.startswith("Error")]
        print(f"  [BUG] {label}: compile rc={rc}: {(err or [log[-300:]])[0][:300]}")
        return len(seq), 0
    linked = h.Linked(obj)
    cfg = wasmtime.Config()
    cfg.wasm_custom_page_sizes = True
    eng = wasmtime.Engine(cfg)
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, wasmtime.Module(eng, wat), [])
    fails = 0
    for fn, args in seq:
        func = inst.exports(st)[fn]
        res = func(st, *args)
        got = linked.call(fn, args)
        if not func.type(st).results:
            ok, shown, exp = not isinstance(got, str), got if isinstance(got, str) else "(void)", "(void)"
        else:
            ok = not isinstance(got, str) and got[0] == res & 0xFFFFFFFF
            shown = got if isinstance(got, str) else hex(got[0])
            exp = hex(res & 0xFFFFFFFF)
        fails += not ok
        print(f"  [{'ok ' if ok else 'BUG'}] {label}.{fn}{args} -> {shown}  (wasmtime {exp})")
    return fails, len(seq)


def mmio(tmp):
    """R2: no data, no stack pointer — 0x40000000 + offset is native."""
    rc, log, obj = compile_(MMIO, tmp, "mmio_pos")
    if rc != 0:
        print(f"  [BUG] mmio_pos: compile rc={rc}: {log.strip().splitlines()[-1][:300]}")
        return 1, 0
    e = h.ELFFile(open(obj, "rb"))
    text = bytearray(e.get_section_by_name(".text").data())
    symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
    syms = {s.name: s["st_value"] for s in symtab.iter_symbols() if s.name}
    mu = h.Uc(h.UC_ARCH_ARM, h.UC_MODE_THUMB)
    mu.mem_map(h.BASES[".text"], h.MAPSZ)
    mu.mem_map(h.BASES[".bss"], h.MAPSZ)
    mu.mem_map(0x40000000, 0x1000)  # the peripheral page
    mu.mem_write(h.BASES[".text"], bytes(text))
    ret = h.BASES[".text"] + h.MAPSZ - 0x10
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    mu.mem_write(0x40000010, (0xC0FFEE11).to_bytes(4, "little"))

    def call(fn, args):
        for reg, a in zip((h.UC_ARM_REG_R0, h.UC_ARM_REG_R1), args):
            mu.reg_write(reg, a)
        mu.reg_write(h.UC_ARM_REG_R11, 0)
        mu.reg_write(h.UC_ARM_REG_SP, h.BASES[".bss"] + h.MAPSZ - 0x100)
        mu.reg_write(h.UC_ARM_REG_LR, ret | 1)
        mu.emu_start((h.BASES[".text"] + syms[fn]) | 1, ret, timeout=2_000_000)
        return mu.reg_read(h.UC_ARM_REG_R0)

    fails = 0
    try:
        got = call("rd", (0x10,))
        ok = got == 0xC0FFEE11
        print(f"  [{'ok ' if ok else 'BUG'}] mmio_pos.rd(0x10) -> {got:#x} (native 0xc0ffee11)")
        fails += not ok
        call("wr", (0x20, 0x12345678))
        got = int.from_bytes(mu.mem_read(0x40000020, 4), "little")
        ok = got == 0x12345678
        print(f"  [{'ok ' if ok else 'BUG'}] mmio_pos.wr(0x20) -> {got:#x} at 0x40000020 (native 0x12345678)")
        fails += not ok
    except h.UcError as ex:
        print(f"  [BUG] mmio_pos: {ex}")
        return 1, 2
    return fails, 2


def main():
    tmp = Path(tempfile.mkdtemp(prefix="npa_model_"))
    fails = compared = 0
    print("=== executed rows ===")
    for label, wat, seq in EXEC:
        f, c = execute(tmp, label, wat, seq)
        fails += f
        compared += c
    print("=== R2: memory-mapped I/O in a module with no data (native contract) ===")
    f, c = mmio(tmp)
    fails += f
    compared += c
    print("=== refused rows ===")
    for label, wat, extra, needles in REFUSE:
        rc, log, obj = compile_(wat, tmp, label, extra)
        missing = [n for n in needles if n not in log]
        ok = rc != 0 and not missing and "panicked" not in log and not obj.exists()
        if not ok:
            fails += 1
        print(f"  [{'ok ' if ok else 'BUG'}] refused: {label} (rc={rc}"
              + (f", missing {missing}" if missing else "") + ")")
    floor = sum(len(s) for _, _, s in EXEC) + 2
    if compared < floor:
        print(f"VACUOUS: compared {compared} of {floor}")
        return 1
    print(f"\ncompared: {compared}")
    print(f"ORACLE: {'PASS' if fails == 0 else f'FAIL ({fails})'}")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
