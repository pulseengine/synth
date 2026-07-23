#!/usr/bin/env python3
"""#494 bounds-elision × #390 guard_bool — four-way execution differential
for the ordeal-certified memory bounds-guard elision.

Builds scripts/repro/fact_spec_bounds_494.wat (the gust_poll-shaped fixture:
a 16 B task-record array at base 256, EIGHT `--safety-bounds software`
guarded accesses) WITH a schema-v1 `wsc.facts` value-range section appended
(green default: slot ∈ [0, 63] on the record index), compiles it three ways —
SPECIALIZED (SYNTH_FACT_SPEC=1 + software bounds), UNSPECIALIZED (software
bounds, no fact-spec) and the unguarded FLOOR (no --safety-bounds) — then:

  1. BYTE EVIDENCE: reports the measured poll shrink (symtab deltas; the
     guarded baseline carries 8 × 16 B of the #752 wraparound-safe
     SUB/CMP/BHS/UDF/CMP/BLS/UDF guard — the #390
     `guard_bool` instruction class; gust_poll's whole guard_bool bucket is
     108 B) and asserts the specialized `.text` is BYTE-IDENTICAL to the
     unguarded floor: under the proven premise the sandbox bounds-guard tax
     is exactly zero.
  2. IN-BOUNDS SWEEP (1024 cases = 64 slots x 16 memory seeds): specialized
     ≡ wasmtime ≡ unspecialized on BOTH the return value and the full final
     64 KiB memory image (the fixture stores ticks+1 and state=2 back).
  3. RETAINED-TRAP LEG: out-of-premise slots whose access escapes the 1-page
     memory must TRAP in wasmtime AND in the UNSPECIALIZED build (the guard
     that was NOT elided still fires; out-of-premise behavior of the
     SPECIALIZED build is outside the premise contract and not asserted).

Non-vacuity: the run FAILS unless the specialized compile admitted exactly 8
certificate-backed elisions (one per access) on stderr.

Modes:
  (default)         green run: byte evidence + in-bounds sweep + retained-trap.
  --expect-decline  facts claim slot ∈ [0, 8192] (slot 4080+ escapes): assert
                    the Sat obligation DECLINED loudly and the build is
                    byte-identical to the guarded baseline (the guard is
                    restored by the OBLIGATION, not by prudence).
  --force-admit     RED run (debug synth builds only): same wrong bound, but
                    SYNTH_FACT_SPEC_FORCE_ADMIT=1 forces the Sat admit —
                    assert poll(4096) TRAPS in wasmtime but does NOT trap in
                    the forced build (the silent OOB access an unsound admit
                    would cause, which the per-site obligation + this harness
                    exist to prevent).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/fact_spec_bounds_494_differential.py
Exits nonzero on any mismatch.
"""

import argparse
import os
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import (
    UC_ARCH_ARM,
    UC_ERR_INSN_INVALID,
    UC_HOOK_CODE,
    UC_MODE_THUMB,
    Uc,
    UcError,
)
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("fact_spec_bounds_494.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
TRAP = "<trap>"

MEM_BYTES = 0x10000  # 1 page = 64 KiB (matches the wat `(memory 1)`)
CODE, LIN, STK, RET = 0x200000, 0x400000, 0x90000, 0x300000


def seed(k):
    """Deterministic per-case memory image (the fixture reads AND writes)."""
    return bytes((i * 31 + 11 * k + 7) & 0xFF for i in range(MEM_BYTES))


# ---- schema-v1 wsc.facts encoding (docs/design/wsc-facts-encoding.md) ----

def leb_u32(v):
    out = bytearray()
    while True:
        b = v & 0x7F
        v >>= 7
        out.append(b | (0x80 if v else 0))
        if not v:
            return bytes(out)


def leb_s64(v):
    out = bytearray()
    while True:
        b = v & 0x7F
        v >>= 7
        done = (v == 0 and not (b & 0x40)) or (v == -1 and (b & 0x40))
        out.append(b | (0 if done else 0x80))
        if done:
            return bytes(out)


def with_slot_range(wasm, lo, hi):
    """Append `slot ∈ [lo, hi]` on (func 0, value_id 0 — the first local.get)."""
    body = leb_s64(lo) + leb_s64(hi)
    payload = (b"\x01" + leb_u32(1) + b"\x01" + leb_u32(0) + leb_u32(0)
               + leb_u32(len(body)) + body)
    name = b"wsc.facts"
    content = leb_u32(len(name)) + name + payload
    return wasm + b"\x00" + leb_u32(len(content)) + content


# ---- compile + load ----

def compile_elf(wasm_path, out, fact_spec, software_bounds=True,
                force_admit=False):
    env = {"PATH": "/usr/bin:/bin"}
    if fact_spec:
        env["SYNTH_FACT_SPEC"] = "1"
    if force_admit:
        env["SYNTH_FACT_SPEC_FORCE_ADMIT"] = "1"
    cmd = [SYNTH, "compile", str(wasm_path), "-o", out, "-b", "arm",
           "--target", "cortex-m4", "--all-exports"]
    if software_bounds:
        cmd += ["--safety-bounds", "software"]
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        sys.exit(f"compile failed ({out}): {r.stderr}")
    return r.stderr


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    data, base = text.data(), text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"] & ~1
    return data, base, syms


def func_size(elf, name):
    """Function size = sorted symbol-address delta (st_size unreliable)."""
    data, base, syms = load(elf)
    addrs = sorted(a for a in syms.values() if base <= a < base + len(data))
    start = syms[name]
    nxt = next((a for a in addrs if a > start), base + len(data))
    return nxt - start


def run_poll(code, base, addr, slot, mem_seed, trap_addr=None, extra_pages=0):
    """Execute poll(slot) over mem_seed; return (ret, memory image), TRAP,
    or an ERR string. `addr`/`trap_addr` are LINKED addresses; the code is
    rebased to CODE (offset `a - base`).

    The direct selector's ABI: R11 = linear-memory base, R10 = memory size in
    bytes (the software guard compares against it). The linmem mapping is
    EXACTLY one page (an access a bad elision lets through faults as ERR,
    never a silent match); `extra_pages` widens it only for the red
    force-admit leg, where the divergence IS the unguarded access succeeding.
    """
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10000)
    mu.mem_map(LIN, MEM_BYTES + extra_pages * 0x10000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, code)
    mu.mem_write(LIN, mem_seed)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, LIN)        # linear-memory base
    mu.reg_write(UC_ARM_REG_R10, MEM_BYTES)  # memory size (bytes) for bounds
    mu.reg_write(UC_ARM_REG_R0, slot & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    trapped = [False]
    if trap_addr is not None:
        trap_rebased = CODE + trap_addr - base

        def hook(uc, address, size, ud):
            if address == trap_rebased:
                trapped[0] = True
                uc.emu_stop()
        mu.hook_add(UC_HOOK_CODE, hook)
    try:
        mu.emu_start((CODE + addr - base) | 1, RET, count=200_000)
    except UcError as e:
        # The inline bounds guard is a UDF -> UC_ERR_INSN_INVALID: that IS the
        # wasm trap. Any OTHER fault (READ/WRITE_UNMAPPED) means an access
        # escaped without a guard — report as ERR, never as a match.
        if e.errno == UC_ERR_INSN_INVALID:
            return TRAP
        return f"ERR:{e}"
    if trapped[0]:
        return TRAP
    return (mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF,
            bytes(mu.mem_read(LIN, MEM_BYTES)))


def wasmtime_poll(module_bytes, slot, mem_seed):
    """Fresh instance per call; return (ret, memory image) or TRAP."""
    eng = wasmtime.Engine()
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, wasmtime.Module(eng, module_bytes), [])
    mem = inst.exports(st)["mem"]
    mem.write(st, mem_seed, 0)
    try:
        ret = inst.exports(st)["poll"](st, slot) & 0xFFFFFFFF
    except Exception:
        return TRAP
    return ret, bytes(mem.read(st, 0, MEM_BYTES))


def show(v, gt=None):
    if v == TRAP or isinstance(v, str):
        return v
    if gt is not None and gt != TRAP and not isinstance(gt, str) and v[1] != gt[1]:
        i = next(i for i in range(MEM_BYTES) if v[1][i] != gt[1][i])
        return f"ret={v[0]} (mem differs @{i})"
    return f"ret={v[0]}"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--expect-decline", action="store_true",
                    help="claim slot ∈ [0,8192]: assert Sat loud-decline + "
                         "byte-identity to the guarded baseline")
    ap.add_argument("--force-admit", action="store_true",
                    help="RED: wrong bound + SYNTH_FACT_SPEC_FORCE_ADMIT — "
                         "demonstrate the silent-OOB divergence")
    args = ap.parse_args()

    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")

    base_wasm = bytes(wasmtime.wat2wasm(WAT.read_text()))
    tmp = Path("/tmp")

    # ---------- red / decline legs: the claim admits OOB (slot 4080+) --------
    if args.expect_decline or args.force_admit:
        wasm = with_slot_range(base_wasm, 0, 8192)
        wasm_path = tmp / "fact_spec_bounds_494_wrong.wasm"
        wasm_path.write_bytes(wasm)
        spec_elf = str(tmp / "fact_spec_bounds_494_wrong_spec.elf")
        base_elf = str(tmp / "fact_spec_bounds_494_wrong_base.elf")
        stderr = compile_elf(wasm_path, spec_elf, fact_spec=True,
                             force_admit=args.force_admit)
        compile_elf(wasm_path, base_elf, fact_spec=False)
        scode, sbase, ssyms = load(spec_elf)
        bcode, _, _ = load(base_elf)

        if args.expect_decline:
            if "fact-spec: ADMIT" in stderr:
                sys.exit(f"expected DECLINE under slot ∈ [0,8192], got an "
                         f"admit:\n{stderr}")
            if "bounds-guard obligation Sat" not in stderr:
                sys.exit(f"decline must name the Sat obligation:\n{stderr}")
            if scode != bcode:
                sys.exit("declined build must be byte-identical to the "
                         "guarded baseline")
            print("ORACLE: PASS (Sat obligation declined loudly; all 8 guards "
                  "restored byte-identically)")
            return

        # --force-admit: the unsound build must silently READ PAST the bound.
        if "UNSOUND FORCED ADMIT" not in stderr:
            sys.exit("force-admit run must scream UNSOUND FORCED ADMIT "
                     "(release synth builds compile the lever out):\n" + stderr)
        slot = 4096  # base = 256 + 65536 = 65792 > 65536: every access OOB
        gt = wasmtime_poll(wasm, slot, seed(0))
        got = run_poll(scode, sbase, ssyms["poll"], slot, seed(0),
                       extra_pages=2)
        print(f"poll({slot}): wasmtime={show(gt)} forced-specialized={show(got)}")
        if gt != TRAP:
            sys.exit("wasmtime must trap on the out-of-bounds access")
        if got == TRAP or isinstance(got, str):
            sys.exit("forced build still trapped/faulted — the red lever did "
                     "not elide the guard (vacuous red run)")
        print("ORACLE: PASS (red) — the forced admit DIVERGES exactly as the "
              "certificate gate predicts: wasmtime traps, the unsound build "
              "silently accesses past the memory bound and returns a value. "
              "This is the sandbox-escape class the per-site obligation + "
              "this harness exist to prevent.")
        return

    # ---------- green leg: proven slot ∈ [0, 63] ----------
    wasm = with_slot_range(base_wasm, 0, 63)
    wasm_path = tmp / "fact_spec_bounds_494.wasm"
    wasm_path.write_bytes(wasm)
    spec_elf = str(tmp / "fact_spec_bounds_494_spec.elf")
    base_elf = str(tmp / "fact_spec_bounds_494_base.elf")
    floor_elf = str(tmp / "fact_spec_bounds_494_floor.elf")
    stderr_spec = compile_elf(wasm_path, spec_elf, fact_spec=True)
    compile_elf(wasm_path, base_elf, fact_spec=False)
    compile_elf(wasm_path, floor_elf, fact_spec=False, software_bounds=False)

    admits = stderr_spec.count("fact-spec: ADMIT")
    declines = stderr_spec.count("fact-spec: DECLINE")
    print(f"specialized compile: {admits} ADMIT, {declines} DECLINE")
    # Non-vacuity: one certificate-backed elision per guarded access.
    if admits != 8:
        sys.exit(f"expected 8 certificate-backed guard elisions, got "
                 f"{admits}:\n{stderr_spec}")
    for token in ("software bounds guard elided", "trap_mem_oob",
                  "certificate-checked"):
        if token not in stderr_spec:
            sys.exit(f"admit lines must name the obligation ('{token}' "
                     f"missing):\n{stderr_spec}")

    # ---- byte evidence (the #390 guard_bool class) ----
    b_len = func_size(base_elf, "poll")
    s_len = func_size(spec_elf, "poll")
    f_len = func_size(floor_elf, "poll")
    print(f"poll: guarded {b_len} B -> specialized {s_len} B "
          f"(-{b_len - s_len} B = 128 B guard elision [8 guards x 16 B "
          f"SUB/CMP/BHS/UDF/CMP/BLS/UDF, the #752 wraparound-safe shape; the "
          f"#390 guard_bool class, gust_poll's whole guard_bool bucket is 108 B] "
          f"+ 4 B from SYNTH_SHIFT_MASK_ELIDE, default-on since v0.50.1 (#846): "
          f"the elision trims BOTH builds but 4 B more off the specialized poll "
          f"[guarded 232->226, specialized 104->94]); unguarded floor {f_len} B")
    # 132 = 128 (guard elision) + 4 (shift-mask elision fires more on the
    # specialized build; SYNTH_SHIFT_MASK_ELIDE default-on since v0.50.1/#846).
    # With SYNTH_SHIFT_MASK_ELIDE=0 this is exactly 128 (the pre-flip win).
    if b_len - s_len != 132:
        sys.exit(f"byte win drifted: expected exactly 132 B "
                 f"(got {b_len - s_len})")
    scode, sbase, ssyms = load(spec_elf)
    fcode, _, _ = load(floor_elf)
    if scode != fcode:
        sys.exit("specialized .text must be BYTE-IDENTICAL to the unguarded "
                 "floor (the proven premise makes the bounds-guard tax "
                 "exactly zero)")
    print("specialized .text == unguarded floor .text (bounds-guard tax = 0)")

    bcode, bbase, bsyms = load(base_elf)
    trap_spec = ssyms.get("Trap_Handler")
    trap_base = bsyms.get("Trap_Handler")

    # ---- in-bounds sweep: 64 slots x 16 memory seeds = 1024 cases ----
    fails = 0
    count = 0
    for k in range(16):
        mem = seed(k)
        for slot in range(64):
            gt = wasmtime_poll(wasm, slot, mem)
            got_s = run_poll(scode, sbase, ssyms["poll"], slot, mem,
                             trap_addr=trap_spec)
            got_b = run_poll(bcode, bbase, bsyms["poll"], slot, mem,
                             trap_addr=trap_base)
            count += 1
            if not (got_s == gt == got_b):
                fails += 1
                if fails <= 10:
                    print(f"FAIL poll({slot}) seed {k}: wasmtime={show(gt)} "
                          f"specialized={show(got_s, gt)} "
                          f"unspecialized={show(got_b, gt)}")
    print(f"swept {count} in-bounds cases (64 slots x 16 memory images, "
          f"return value + full final memory image)")

    # ---- retained-trap leg: out-of-premise inputs on the UNSPECIALIZED
    # path must still trap (its guards were never elided) ----
    for slot in (4080, 4096, 8192, 1_000_000):
        gt = wasmtime_poll(wasm, slot, seed(0))
        got_b = run_poll(bcode, bbase, bsyms["poll"], slot, seed(0),
                         trap_addr=trap_base)
        count += 1
        if gt != TRAP:
            sys.exit(f"vector expectation wrong: wasmtime must trap on "
                     f"poll({slot})")
        if got_b != TRAP:
            fails += 1
            print(f"FAIL poll({slot}): unspecialized build must TRAP "
                  f"(wasmtime traps), got {show(got_b)}")
        else:
            print(f"poll({slot}): TRAP in both wasmtime and the "
                  f"unspecialized build (guard retained)")

    print("ORACLE:", "PASS" if fails == 0 else f"FAIL ({fails}/{count})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
