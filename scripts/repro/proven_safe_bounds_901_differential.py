#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 371
"""VCR-MEM-004 / #901 — execution differential for `--proven-safe`.

Compiles `scripts/repro/proven_safe_bounds_901.wat` (one function, EIGHT
`--safety-bounds software` guarded accesses: five off a provably bounded base
`(slot & 63) * 16 + 256`, three off an unconstrained i32 param `$raw`) four
ways and executes them under unicorn against wasmtime:

  GUARDED    --safety-bounds software, no verdicts (the baseline)
  ELIDED     the same + scry verdicts covering only the FIVE proven sites
  FLOOR      no --safety-bounds at all (the zero-tax reference)
  STALE      the ELIDED verdicts applied to a MUTATED module (below)

Legs
----
1. BYTE EVIDENCE — the measured `probe` shrink and the surviving guard count,
   plus non-vacuity: the run FAILS unless the compile reported exactly five
   certificate-free, scry-authorized elisions on stderr.

2. IN-BOUNDS SWEEP — for every in-bounds (slot, raw) pair over several memory
   seeds, ELIDED == GUARDED == wasmtime on BOTH the returned value and the
   FULL final 64 KiB memory image (the fixture stores through `$base` and
   `$raw`). An elision that changed a result would show up here.

3. ABSENCE IS NOT SAFETY (executable) — `$raw` driven out of the one-page
   memory must TRAP in wasmtime AND in the ELIDED build. Those three sites
   were never proven, so their guards MUST have survived the elision of the
   five that were. This is the property that makes a partial verdict list
   safe to consume at all.

4. FAIL CLOSED, and it is LOAD-BEARING — the red leg. The mutated module is
   the fixture with `i32.const 63` replaced by `i32.const -1`, so
   `slot & -1 == slot` and the five formerly-proven accesses become
   UNBOUNDED. Every (func, pc) key still validates — same operator count,
   same operator kinds, same widths — so the ONLY thing standing between the
   stale verdicts and a silent out-of-bounds access is `module_sha256`.
   Asserted: the compile REFUSES, its `.text` is byte-identical to the
   mutated module's own guarded baseline, and a large `slot` still TRAPS
   exactly like wasmtime.

   This leg is a permanent regression gate, not a one-time demo: delete or
   invert the hash comparison in `synth_core::proven_safe::ingest` and it
   goes RED with a silent OOB (verified by mutation while developing #901).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/proven_safe_bounds_901_differential.py
Exits nonzero on any mismatch; prints `#901 CHECKS=<n>/<n>` on success.
"""

import hashlib
import json
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
    UC_ARM_REG_R1,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("proven_safe_bounds_901.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
TMP = Path("/tmp/proven_safe_bounds_901_diff")
TRAP = "<trap>"

MEM_BYTES = 0x10000  # 1 page, matching `(memory 1)`
CODE, LIN, STK, RET = 0x200000, 0x400000, 0x90000, 0x300000

# The fixture's PROVEN sites (operator index, mnemonic, access width).
PROVEN = [
    (9, "i32.load8_u", 1),
    (11, "i32.load8_u", 1),
    (14, "i32.load16_u", 2),
    (17, "i32.load", 4),
    (22, "i32.store8", 1),
]

CHECKS = [0, 0]  # [passed, total]


def check(ok, what):
    CHECKS[1] += 1
    if ok:
        CHECKS[0] += 1
    else:
        print(f"FAIL: {what}")
    return ok


def seed(k):
    return bytes((i * 37 + 13 * k + 5) & 0xFF for i in range(MEM_BYTES))


# ---------------------------------------------------------------- verdicts --


def verdicts(module_bytes, sites, memory_min_bytes=65536):
    return json.dumps(
        {
            "schema": "scry/safe-accesses/v1",
            "scry_version": "3.2.4",
            "module_sha256": hashlib.sha256(module_bytes).hexdigest(),
            "memory_min_bytes": memory_min_bytes,
            "premises": {"bounded_memory": True},
            "counts": {"access_sites": 8, "proven_safe": len(sites)},
            "proven_safe": [
                {"func": 0, "pc": pc, "op": op, "width": w} for pc, op, w in sites
            ],
        },
        indent=2,
    )


# ------------------------------------------------------------ compile/load --


def compile_elf(wasm_path, out, software_bounds=True, proven_safe=None):
    # A FRESH env so an ambient SYNTH_* lever cannot perturb the measurement
    # (the #494 fact_spec_bounds lesson).
    env = {"PATH": "/usr/bin:/bin"}
    cmd = [
        SYNTH, "compile", str(wasm_path), "-o", str(out), "-b", "arm",
        "--target", "cortex-m4", "--all-exports",
    ]
    if software_bounds:
        cmd += ["--safety-bounds", "software"]
    if proven_safe is not None:
        cmd += ["--proven-safe", str(proven_safe)]
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        sys.exit(f"compile failed ({out}): {r.stderr}")
    return r.stderr


def load(elf):
    with open(elf, "rb") as fh:
        f = ELFFile(fh)
        text = f.get_section_by_name(".text")
        data, base = text.data(), text["sh_addr"]
        syms = {}
        for s in f.iter_sections():
            if s.header.sh_type == "SHT_SYMTAB":
                for sym in s.iter_symbols():
                    if sym.name:
                        syms[sym.name] = sym["st_value"] & ~1
        return data, base, syms


def func_bytes(elf, name):
    data, base, syms = load(elf)
    addrs = sorted(a for a in syms.values() if base <= a < base + len(data))
    start = syms[name]
    nxt = next((a for a in addrs if a > start), base + len(data))
    return data[start - base : nxt - base]


# ------------------------------------------------------------- executors ----


def run_probe(elf, slot, raw, mem_seed, count_insns=False):
    """probe(slot, raw) under unicorn. Returns (ret, memory) or TRAP or ERR.

    The direct selector's ABI: R11 = linear-memory base, R10 = memory size in
    bytes (what the software guard compares against). Linear memory is mapped
    as EXACTLY one page, so an access a bad elision lets through faults as ERR
    rather than silently matching.
    """
    code, base, syms = load(elf)
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10000)
    mu.mem_map(LIN, MEM_BYTES)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, code)
    mu.mem_write(LIN, mem_seed)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, LIN)
    mu.reg_write(UC_ARM_REG_R10, MEM_BYTES)
    mu.reg_write(UC_ARM_REG_R0, slot & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_R1, raw & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    n = [0]
    if count_insns:
        mu.hook_add(UC_HOOK_CODE, lambda uc, a, s, u: n.__setitem__(0, n[0] + 1))
    try:
        mu.emu_start((CODE + syms["probe"] - base) | 1, RET, count=200_000)
    except UcError as e:
        # The inline guard is a UDF -> UC_ERR_INSN_INVALID: that IS the wasm
        # trap. Any other fault means an access escaped WITHOUT a guard.
        if e.errno == UC_ERR_INSN_INVALID:
            return (TRAP, n[0]) if count_insns else TRAP
        return (f"ERR:{e}", n[0]) if count_insns else f"ERR:{e}"
    out = (mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF, bytes(mu.mem_read(LIN, MEM_BYTES)))
    return (out, n[0]) if count_insns else out


def wasmtime_probe(module_bytes, slot, raw, mem_seed):
    eng = wasmtime.Engine()
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, wasmtime.Module(eng, module_bytes), [])
    mem = inst.exports(st)["mem"]
    mem.write(st, mem_seed, 0)
    try:
        ret = inst.exports(st)["probe"](st, slot, raw) & 0xFFFFFFFF
    except Exception:
        return TRAP
    return ret, bytes(mem.read(st, 0, MEM_BYTES))


def brief(v):
    if isinstance(v, str):
        return v
    return f"ret={v[0]}"


# ------------------------------------------------------------------- main ---


def main():
    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")
    TMP.mkdir(parents=True, exist_ok=True)

    wat = WAT.read_text()
    wasm = bytes(wasmtime.wat2wasm(wat))
    w_path = TMP / "probe.wasm"
    w_path.write_bytes(wasm)

    v_path = TMP / "safe-accesses.json"
    v_path.write_text(verdicts(wasm, PROVEN))

    guarded = TMP / "guarded.elf"
    elided = TMP / "elided.elf"
    floor = TMP / "floor.elf"
    compile_elf(w_path, guarded)
    err = compile_elf(w_path, elided, proven_safe=v_path)
    compile_elf(w_path, floor, software_bounds=False)

    # ---- LEG 1: byte evidence + non-vacuity -----------------------------
    g, e, f = (func_bytes(p, "probe") for p in (guarded, elided, floor))

    def udf(b):
        return sum(1 for i in range(0, len(b) - 1, 2) if b[i : i + 2] == b"\x00\xde")

    print(f"probe: guarded={len(g)} B ({udf(g)} UDF#0)  "
          f"elided={len(e)} B ({udf(e)} UDF#0)  floor={len(f)} B ({udf(f)} UDF#0)")
    print(f"       saved {len(g) - len(e)} B of the {len(g) - len(f)} B guard tax "
          f"({100 * (len(g) - len(e)) / (len(g) - len(f)):.0f}% of it), "
          f"{100 * (len(g) - len(e)) / len(g):.1f}% of the function")
    check("proven-safe: ACCEPTED" in err, "verdicts must be ACCEPTED")
    check(
        "5 bounds guard(s) elided" in err,
        f"exactly 5 elisions must be reported (non-vacuity); stderr: {err}",
    )
    check(len(e) < len(g), "the elided build must be smaller")
    check(udf(e) == 6, f"exactly 3 unproven guards (6 UDF#0) must survive, got {udf(e)}")
    check(udf(g) == 16, "the baseline must carry all 8 guards")

    # ---- LEG 2: in-bounds sweep ------------------------------------------
    # `raw` stays where a 4 B load at +0, a 1 B load at +3 and a 4 B store at
    # +8 all fit inside the page.
    raws = [0, 4, 64, 1024, MEM_BYTES - 16, MEM_BYTES - 12]
    slots = [0, 1, 7, 31, 63, 64, 65, 127, 4096, 0xFFFFFFF0]
    rows = 0
    for k in range(3):
        m = seed(k)
        for slot in slots:
            for raw in raws:
                want = wasmtime_probe(wasm, slot, raw, m)
                got_e = run_probe(elided, slot, raw, m)
                got_g = run_probe(guarded, slot, raw, m)
                rows += 1
                if not check(
                    got_e == want and got_g == want,
                    f"in-bounds probe(slot={slot}, raw={raw}, seed={k}): "
                    f"wasmtime={brief(want)} elided={brief(got_e)} "
                    f"guarded={brief(got_g)}",
                ):
                    return 1
    print(f"in-bounds sweep: {rows} rows — elided == guarded == wasmtime "
          f"(return value AND full 64 KiB memory image)")

    # ---- LEG 3: absence is not safety, executable -------------------------
    # `$raw` was never proven, so its guards MUST have survived.
    oob_raws = [MEM_BYTES, MEM_BYTES - 4, MEM_BYTES + 4096, 0xFFFFFFF0, 0x7FFFFFFF]
    m = seed(9)
    for raw in oob_raws:
        want = wasmtime_probe(wasm, 3, raw, m)
        got = run_probe(elided, 3, raw, m)
        check(
            want == TRAP,
            f"fixture setup: probe(3, {raw}) must trap in wasmtime, got {brief(want)}",
        )
        check(
            got == TRAP,
            f"NOT-PROVEN out-of-bounds probe(3, raw={raw}) must STILL TRAP in the "
            f"ELIDED build (absence means not-proven, never unsafe) — got {brief(got)}",
        )
    print(f"absence-is-not-safety: {len(oob_raws)} out-of-bounds cases still TRAP "
          f"in the elided build, exactly like wasmtime")

    # ---- LEG 4: fail closed, and load-bearing -----------------------------
    # `slot & 63` -> `slot & -1`: the five formerly-proven accesses become
    # UNBOUNDED, but every (func, pc) key still validates (same operator
    # count, kinds and widths). Only module_sha256 differs.
    mutated_wat = wat.replace("i32.const 63           ;; op 1", "i32.const -1           ;; op 1")
    assert mutated_wat != wat, "the mutation anchor drifted — fix the differential"
    mutated = bytes(wasmtime.wat2wasm(mutated_wat))
    mw_path = TMP / "mutated.wasm"
    mw_path.write_bytes(mutated)
    check(
        hashlib.sha256(mutated).hexdigest() != hashlib.sha256(wasm).hexdigest(),
        "the mutated module must hash differently",
    )

    stale = TMP / "stale.elf"
    mutated_guarded = TMP / "mutated_guarded.elf"
    stale_err = compile_elf(mw_path, stale, proven_safe=v_path)
    compile_elf(mw_path, mutated_guarded)

    check(
        "REFUSED — module_sha256 mismatch" in stale_err,
        f"stale verdicts must be REFUSED; stderr: {stale_err}",
    )
    check(
        func_bytes(stale, "probe") == func_bytes(mutated_guarded, "probe"),
        "a refused verdict file must not move a single byte",
    )
    # The attestation must record the refusal, so sigil can tell "nothing to
    # elide" from "file rejected".
    att = json.loads((TMP / "stale.proven-safe-elisions.json").read_text())
    check(att["accepted"] is False, "the attestation must record the refusal")
    check(att["sites_elided"] == 0, "a refusal must attest ZERO elisions")
    check(
        isinstance(att.get("refusal"), str) and "module_sha256" in att["refusal"],
        "the attestation must name the refusal reason",
    )

    # And the behaviour the gate protects: a large `slot` now escapes the page.
    # Chosen so `(slot << 4) + 256` really is past 65536 WITHOUT wrapping —
    # e.g. 0x7FFFFFF0 << 4 wraps back to 0 and is in bounds, so it is not a
    # witness.
    for slot in [4096, 0x10000, 0x100000]:
        want = wasmtime_probe(mutated, slot, 0, m)
        got = run_probe(stale, slot, 0, m)
        check(
            want == TRAP,
            f"mutated fixture: probe({slot}, 0) must trap in wasmtime, got {brief(want)}",
        )
        check(
            got == TRAP,
            f"STALE-VERDICT build must still TRAP at probe({slot}, 0) — if this is "
            f"not a trap, a stale analysis elided a live bounds check (the "
            f"memory-safety hole module_sha256 exists to prevent). Got {brief(got)}",
        )
    print("fail-closed: stale verdicts REFUSED, bytes unmoved, and the "
          "now-unbounded accesses still trap")

    # ---- instruction-count evidence (the cycles axis) ---------------------
    _, n_g = run_probe(guarded, 3, 16, m, count_insns=True)
    _, n_e = run_probe(elided, 3, 16, m, count_insns=True)
    _, n_f = run_probe(floor, 3, 16, m, count_insns=True)
    print(f"executed instructions on one in-bounds call: guarded={n_g} "
          f"elided={n_e} floor={n_f} — {n_g - n_e} fewer ({100 * (n_g - n_e) / n_g:.1f}%), "
          f"{n_g - n_f} is the whole 8-site guard cost")

    ok = CHECKS[0] == CHECKS[1]
    print(f"#901 CHECKS={CHECKS[0]}/{CHECKS[1]}")
    print("RESULT: PASS" if ok else "RESULT: FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
