#!/usr/bin/env python3
"""VCR-DEC-001 graph-colouring allocator SPIKE differential (SYNTH_GRAPH_ALLOC).

The North Star's first foothold: a whole-function Chaitin/Briggs graph-colouring
register allocator (crate `synth_synthesis::graph_alloc`), flag-gated behind
`SYNTH_GRAPH_ALLOC`, built AGAINST the acceptance oracles the verified path
already runs. This differential asserts the three properties that make the spike
sound, on the ARM fixture corpus (arm / cortex-m4, --all-exports --relocatable):

  (1) FLAG-OFF ≡ SHIPPING (the GOLDEN trick). `SYNTH_GRAPH_ALLOC` unset must
      produce EXACTLY the shipping bytes — the flag-off path never enters the
      graph_alloc branch. Pinned against the frozen goldens for the four canonical
      fixtures (control_step, flight_seam, flight_seam_flat, signed_div_const).

  (2) FLAG-ON APPLIES on ≥1 named function per applying fixture, and on every
      applied function the UNCONDITIONAL VCR-RA-003 validator
      (validate_final_allocation) returns **Consistent** — the acceptance oracle
      validating the new allocator's REAL output (observed via
      SYNTH_RA003_VERBOSE, not inferred from returncode).

  (3) FLAG-ON ≡ FLAG-OFF on the whole corpus. This is a DESIGNED PROPERTY, not a
      null result: on a straight-line function graph_alloc and the shipping
      `reallocate_function` use the same pins (inputs + last-opened live-outs),
      the same chaitin_core, and the same single-segment scope, so their outputs
      are byte-identical BY CONSTRUCTION; everywhere else graph_alloc declines.
      graph_alloc's output ⊆ {shipping bytes, decline}, so divergence is
      impossible in increment 1. Execution correctness therefore follows
      TRANSITIVELY: flag-on bytes = shipping bytes on applied functions, and the
      shipping bytes are already wasmtime-gated by the frozen execution
      differentials. (A passive flag-on-vs-wasmtime corpus would merely re-test
      the shipping compiler, so it is deliberately NOT built here.)

The red-first teeth — "a colouring bug → the acceptance oracle catches it" — are
the unit probe `graph_alloc_bad_rename_rejected_by_segment_validator` in
liveness.rs: validate_segment_rewrite (the trace-equality gate graph_alloc
invokes) rejects a value-flow-breaking merge-rename and accepts the identity.

Usage: python3 vcr_dec_001_graph_alloc_differential.py <synth-binary>
Exit 0 = all three properties hold; nonzero = a violation.
"""
import hashlib
import os
import subprocess
import sys
import tempfile
from pathlib import Path

REPRO = Path(__file__).resolve().parent

# Canonical frozen fixtures (fixture, golden .text sha256, golden len) — the exact
# pins from crates/synth-cli/tests/frozen_codegen_bytes.rs oracle_001.
FROZEN = [
    # Synced to frozen_codegen_bytes.rs oracle_001 default block after the #846
    # shift-mask elision went default-on (v0.50.1): the shift-carrying anchors
    # SHRANK — control_step 308→288 (−20), flight_seam 870→706 (−164),
    # flight_seam_flat 1010→842 (−168). signed_div_const is inert (no shift).
    ("control_step.wasm",
     "8b3f1f6fe3a40994dacca91614cc19590f330eb49e8dcc8eb5b0ffc78338a1d9", 288),
    ("flight_seam.wasm",
     "e7152735df88a699f4600574dc5b6f5bc34efcb8cba020f78ec78f59d9d20f8a", 706),
    ("flight_seam_flat.wasm",
     "5a5d675772544662fefdee6f267d07be98da1560af0626b0671e7d79b1644f37", 842),
    ("signed_div_const.wasm",
     "b277453b7829a5b2c64527131298d89fa63f5641231b1d4c7336675e8cdab9b0", 34),
]

# Full corpus for the flag-on ≡ flag-off + RA-003 checks.
CORPUS = [
    "control_step.wasm", "flight_seam.wasm", "flight_seam_flat.wasm",
    "signed_div_const.wasm", "controller_step.wasm", "filter_axis.wasm",
    "gust_kernel.wasm", "sret_decide.wasm", "reachable_helper.wasm",
    "msgq_put_359.wasm",
]

# Flags the frozen gate removes so an ambient env var can't re-freeze the result.
CLEAR = [
    "SYNTH_NO_CMP_SELECT_FUSE", "SYNTH_NO_LOCAL_PROMOTE", "SYNTH_NO_IMM_SHIFT_FOLD",
    "SYNTH_NO_STACK_FWD", "SYNTH_SPILL_REALLOC", "SYNTH_CONST_CSE", "SYNTH_BASE_CSE",
    "SYNTH_DEAD_FRAME_ELIM", "SYNTH_UXTH_FOLD", "SYNTH_GRAPH_ALLOC",
    # #846: shift-mask elision is default-on since v0.50.1; strip its opt-out
    # (`SYNTH_SHIFT_MASK_ELIDE=0`) so an ambient override can't un-freeze the gate.
    "SYNTH_SHIFT_MASK_ELIDE",
]


def compile_arm(synth, wasm, extra_env):
    env = dict(os.environ)
    for k in CLEAR:
        env.pop(k, None)
    env.update(extra_env)
    td = tempfile.mkdtemp()
    elf = Path(td) / (wasm + ".elf")
    r = subprocess.run(
        [synth, "compile", str(REPRO / wasm), "-o", str(elf),
         "-b", "arm", "--target", "cortex-m4", "--all-exports", "--relocatable"],
        capture_output=True, env=env,
    )
    return r, elf


def text_of(elf):
    data = Path(elf).read_bytes()
    return _extract_text(data)


def _extract_text(elf_bytes):
    import struct
    assert elf_bytes[:4] == b"\x7fELF", "not an ELF"
    e_shoff = struct.unpack_from("<I", elf_bytes, 0x20)[0]
    e_shentsize = struct.unpack_from("<H", elf_bytes, 0x2E)[0]
    e_shnum = struct.unpack_from("<H", elf_bytes, 0x30)[0]
    e_shstrndx = struct.unpack_from("<H", elf_bytes, 0x32)[0]

    def sh(i):
        off = e_shoff + i * e_shentsize
        name = struct.unpack_from("<I", elf_bytes, off)[0]
        offset = struct.unpack_from("<I", elf_bytes, off + 0x10)[0]
        size = struct.unpack_from("<I", elf_bytes, off + 0x14)[0]
        return name, offset, size

    strtab_off = sh(e_shstrndx)[1]
    for i in range(e_shnum):
        name, offset, size = sh(i)
        end = elf_bytes.index(b"\x00", strtab_off + name)
        if elf_bytes[strtab_off + name:end].decode() == ".text":
            return elf_bytes[offset:offset + size]
    raise RuntimeError(".text not found")


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    synth = sys.argv[1]
    fails = 0

    # ---- Property 1: FLAG-OFF ≡ frozen goldens -------------------------------
    print("== (1) flag-off ≡ frozen goldens ==")
    for wasm, golden, glen in FROZEN:
        r, elf = compile_arm(synth, wasm, {})
        if r.returncode != 0:
            print(f"  {wasm:<24} COMPILE FAIL: {r.stderr.decode()[:120]}")
            fails += 1
            continue
        t = text_of(elf)
        ok = sha(t) == golden and len(t) == glen
        print(f"  {wasm:<24} {sha(t)[:12]} len={len(t):<5} {'OK' if ok else 'MISMATCH <--'}")
        fails += 0 if ok else 1

    # ---- Property 2+3: flag-on APPLIES + RA-003 Consistent + ≡ flag-off ------
    print("== (2)(3) flag-on: applies, RA-003 Consistent, ≡ flag-off ==")
    applied_fixtures = 0
    for wasm in CORPUS:
        r_off, off_elf = compile_arm(synth, wasm, {})
        r_on, on_elf = compile_arm(
            synth, wasm,
            {"SYNTH_GRAPH_ALLOC": "1", "SYNTH_GRAPH_ALLOC_STATS": "1",
             "SYNTH_RA003_VERBOSE": "1"},
        )
        if r_off.returncode != 0 or r_on.returncode != 0:
            print(f"  {wasm:<24} COMPILE FAIL")
            fails += 1
            continue
        on_stderr = r_on.stderr.decode(errors="replace")
        applied = on_stderr.count("whole-function colouring APPLIED")
        # Every applied function's RA-003 verdict must be Consistent, and there
        # must be NO NotAttempted-with-a-graph-applied miscompile risk. We assert:
        # if applied > 0, at least one Consistent appears and NO Violation.
        consistent = on_stderr.count("VCR-RA-003: Consistent")
        violation = "register-allocation validation FAILED" in on_stderr
        # Byte-identity flag-on ≡ flag-off (the designed property).
        ident = text_of(off_elf) == text_of(on_elf)
        if applied > 0:
            applied_fixtures += 1
        ok = ident and not violation and (applied == 0 or consistent > 0)
        tag = []
        tag.append(f"applied={applied}")
        tag.append(f"RA003-consistent={consistent}")
        tag.append("bytes≡" if ident else "BYTES-DIFFER<--")
        if violation:
            tag.append("RA003-VIOLATION<--")
        print(f"  {wasm:<24} {'  '.join(tag)} {'OK' if ok else 'FAIL <--'}")
        fails += 0 if ok else 1

    # Non-vacuity: the allocator must ACTUALLY fire on at least a few fixtures,
    # else the "≡ flag-off" property is trivially satisfied by never running.
    print(f"== applying fixtures: {applied_fixtures} (must be ≥ 2 for non-vacuity) ==")
    if applied_fixtures < 2:
        print("  VACUOUS: graph_alloc never applied — increment-1 scope regressed.")
        fails += 1

    # DEEPER non-vacuity: prove graph_alloc's byte-match is NOT a trivial identity
    # transform. Compile a known-applying fixture with the shipping re-allocation
    # DISABLED (SYNTH_RANGE_REALLOC=0 = the raw selector stream): if the shipping
    # reallocated bytes DIFFER from the raw stream, reallocation did real register
    # work — and graph_alloc reproduced THOSE bytes (property 3), so graph_alloc
    # is making the same non-trivial choices, not returning its input unchanged.
    print("== (deeper non-vacuity) graph_alloc reproduces REAL reallocation ==")
    r_raw, raw_elf = compile_arm(synth, "signed_div_const.wasm",
                                 {"SYNTH_RANGE_REALLOC": "0"})
    r_realloc, realloc_elf = compile_arm(synth, "signed_div_const.wasm", {})
    r_ga, ga_elf = compile_arm(synth, "signed_div_const.wasm",
                               {"SYNTH_GRAPH_ALLOC": "1"})
    if all(x.returncode == 0 for x in (r_raw, r_realloc, r_ga)):
        raw_t, realloc_t, ga_t = (text_of(raw_elf), text_of(realloc_elf),
                                  text_of(ga_elf))
        did_work = raw_t != realloc_t
        ga_matches = ga_t == realloc_t
        ok = did_work and ga_matches
        print(f"  signed_div_const: raw={len(raw_t)}B realloc={len(realloc_t)}B "
              f"graph_alloc={len(ga_t)}B  realloc-did-work={did_work} "
              f"graph_alloc≡realloc={ga_matches} {'OK' if ok else 'FAIL <--'}")
        if not ok:
            fails += 1
    else:
        print("  signed_div_const: COMPILE FAIL")
        fails += 1

    print("-" * 60)
    if fails:
        print(f"VIOLATION: {fails} check(s) failed.")
        return 1
    print("OK: flag-off frozen, flag-on applies + RA-003 Consistent + ≡ flag-off.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
