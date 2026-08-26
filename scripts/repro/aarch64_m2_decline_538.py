#!/usr/bin/env python3
# ci-status: wired
# ci-checks: stdout /^(\d+)/\d+ declined ops loud-declined/ >= 13
"""#538 milestone-2 — assert the aarch64 decline matrix stays HONEST.

Some WASM constructs are DELIBERATELY not lowered on aarch64, and the contract
is that each LOUD-declines (a non-zero exit / "skipping" / compile error) —
never silently emits wrong code.

This harness compiles a module per declined construct and asserts the compile
FAILS, so a future accidental silent-lowering of any of them is caught. The
list SHRINKS as capability lands: an entry whose gap has closed is a stale
claim and must be deleted in the same commit that closes it (this file is the
end-to-end companion of the VCR-SEL-005 `a64_extended_surface` gate, which
enforces the same both-directions contract at the selector level).

Run:  SYNTH=<target>/debug/synth python scripts/repro/aarch64_m2_decline_538.py
"""
import os
import subprocess
import sys
import tempfile

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

# Each entry: (label, wat body). All must FAIL to compile with -b aarch64.
# #851 landed div/rem (SDIV/UDIV+MSUB with the WASM ÷0 + INT_MIN/-1 trap
# guards), popcnt (SIMD CNT/ADDV) and f64<->i64 reinterpret; m3 (#787) the
# non-trapping scalar floats; m4 the #709-class trapping i32 truncations +
# FMIN/FMAX + copysign; and v0.54 L2 the last four scalar-float classes —
# rounding (FRINT{P,M,Z,N}), f32/f64 load/store (bounds-checked LDR/STR s|d),
# i64->float converts (x-form SCVTF/UCVTF) and the DOMAIN-GUARDED trapping
# i64-target truncations. Each moved off this list the day it landed; they are
# now execution-verified in aarch64_float_completion_851_differential.py.
#
# What DELIBERATELY stays declined, and why:
DECLINED = [
    # No function-table substrate + no type/null/OOB trap guards (§4.4.8).
    # v0.54 fan-in: `call_indirect` and `global.get`/`global.set` moved OFF
    # this list (lane L3 landed them) and the float rounding / trapping
    # i64-truncation entries moved off too (lane L2 landed those). Both
    # lanes' pre-merge copies of this list were stale in OPPOSITE
    # directions — asserting a decline for a capability that now ships is
    # the same doc-honesty defect as claiming one that does not.
    #
    # v0.55 L6 (VCR-A64-CF-001) moved `br_table` and the VALUE-CARRYING
    # `block (result f32)` off this list. Note what REPLACED them: not
    # nothing, but the NARROWER residuals below. A partial lowering that
    # deleted its entry outright would be claiming more than it ships.
    # v0.55 L6 (VCR-A64-CF-001): `br_table` and the VALUE-CARRYING
    # `block`/`loop`/`if` moved OFF this list — both now lower and are
    # execution-verified in aarch64_brtable_blockvals_851_differential.py. What
    # is LEFT of each is a narrower, named residual, and it stays here:
    ("br_table past the compare-chain threshold (>16 targets)",
     '(func (export "f") (param i32) (result i32) '
     # 17 TARGETS (+ a trailing default label) — one past BR_TABLE_MAX_TARGETS.
     '(block (block (br_table 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 (local.get 0))) '
     '(return (i32.const 1))) (i32.const 2))',
     "exceeds the aarch64 compare-chain threshold"),
    ("br_table with VALUE-CARRYING targets",
     '(func (export "f") (param i32) (result i32) '
     '(block (result i32) (i32.const 7) (local.get 0) '
     '(br_table 0 0 (local.get 0))))',
     "VALUE-CARRYING targets"),
    ("block with PARAMETERS (multi-value)",
     '(func (export "f") (param i32) (result i32) '
     '(local.get 0) (block (param i32) (result i32) (i32.const 1) (i32.add)))',
     "PARAMETER-taking block type"),
    ("block with MULTI-VALUE results",
     '(func (export "f") (param i32) (result i32) '
     '(block (result i32 i32) (i32.const 1) (i32.const 2)) (i32.add))',
     "MULTI-VALUE result block type"),
    # RQ-57-A64PARAM (#851) moved "local.set on a param" OFF this list: param
    # HOMING landed, so writing a param lowers (and is execution-verified in
    # aarch64_param_homing_851_differential.py). What replaced it is NOT
    # nothing — the narrower FLOAT-param residual at the bottom of this list
    # stays, because the home-slot model is single-register-file.
    ("memory.fill", '(memory 1)(func (export "f") '
                    '(memory.fill (i32.const 0) (i32.const 0) (i32.const 4)))'),
    ("f32x4.add", '(func (export "f") (param f32) (result f32) '
                  '(f32x4.extract_lane 0 (f32x4.add '
                  '(f32x4.splat (local.get 0)) (f32x4.splat (local.get 0)))))'),
    ("imported global",
     '(import "env" "g" (global i32)) '
     '(func (export "f") (result i32) (global.get 0))',
     "imports 1 global"),
    ("float global (no decoded const init)",
     '(global $f (mut f32) (f32.const 1.5)) '
     '(func (export "f") (result f32) (global.get $f))',
     "no decoded constant initializer"),
    ("v128 global",
     '(global $v (mut v128) (v128.const i32x4 1 2 3 4)) '
     '(func (export "f") (result v128) (global.get $v))',
     None),
    ("growable imported table",
     '(import "env" "t" (table 4 funcref)) '
     '(type $b (func (param i32 i32) (result i32))) '
     '(func $a (type $b) (i32.add (local.get 0) (local.get 1))) '
     '(func (export "f") (param i32) (result i32) '
     '(call_indirect (type $b) (i32.const 1) (i32.const 2) (local.get 0)))',
     "no compile-time size"),
    ("passive element segment",
     '(type $b (func (param i32 i32) (result i32))) '
     '(table 2 funcref) '
     '(elem func $a) '
     '(func $a (type $b) (i32.add (local.get 0) (local.get 1))) '
     '(func (export "f") (param i32) (result i32) '
     '(call_indirect (type $b) (i32.const 1) (i32.const 2) (local.get 0)))',
     "not statically verifiable"),
    # RQ-60-A64IMPORT (#1017): "table slot holding an IMPORTED function" moved
    # OFF this list — the slot's trampoline now emits `b <field>` against the
    # import's wasm field name as a GLOBAL/STT_FUNC/SHN_UNDEF external
    # (R_AARCH64_JUMP26), the ARM #173/#197 contract ported. Deleted because
    # the replacing capability is VERIFIED WORKING, not merely because the
    # decline stopped: aarch64_import_dispatch_1017_differential.py (CI-wired,
    # same job) executes the import-slot dispatch under unicorn against
    # wasmtime (slot 0 = import -> 42, OOB indices still trap), after checking
    # the symtab contract via pyelftools. The narrower residual that remains —
    # an import the module does not NAME still declines (never fabricate a
    # symbol) — is pinned at unit level in substrate.rs
    # (`table_slot_holding_an_unnamed_import_still_declines_1017`).
    # The reason is NOT a missing FP store — the encoder has `str s/d` since the
    # v0.54 L2 float load/store increment. It is the SLOT MODEL: `slot_resident`
    # / `local_slot_off` are register-file-agnostic, so a homed v-register param
    # would be stored and reloaded as a GP register. Loud-decline beats that
    # silent miscompile (RQ-57-A64PARAM, #851).
    ("FLOAT param in a homing function (slot model is single-register-file)",
     '(func $g (result i32) (i32.const 1)) '
     '(func (export "f") (param f32) (result f32) '
     '(drop (call $g)) (local.get 0))',
     "FLOAT parameter"),
    # The same decline reached the OTHER way (#851): a LEAF function homes its
    # params as soon as it WRITES one, so a declared float param declines even
    # with no call in the body. This entry did not exist before param homing —
    # the shape used to decline on the param write itself.
    ("FLOAT param in a LEAF function that writes a param",
     '(func (export "f") (param f32 i32) (result i32) '
     '(local.set 1 (i32.const 7)) (local.get 1))',
     "FLOAT parameter"),
]


def compiles_ok(body):
    wat = f"(module {body})"
    with tempfile.NamedTemporaryFile("w", suffix=".wat", delete=False) as tf:
        tf.write(wat)
        path = tf.name
    out = path + ".o"
    r = subprocess.run(
        [SYNTH, "compile", path, "-o", out, "-b", "aarch64", "--all-exports"],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"})
    os.unlink(path)
    if os.path.exists(out):
        os.unlink(out)
    # "compiled" = exit 0 AND not skipped.
    return r.returncode == 0 and "skipping" not in r.stderr, r.stderr


def main():
    fails = 0
    reasoned = 0
    for entry in DECLINED:
        label, body = entry[0], entry[1]
        want_reason = entry[2] if len(entry) > 2 else None
        ok, stderr = compiles_ok(body)
        if ok:
            print(f"BUG {label}: compiled — expected a LOUD decline (silent miscompile risk)")
            fails += 1
        elif want_reason is not None and want_reason not in stderr:
            print(f"BUG {label}: declined, but WITHOUT its machine reason "
                  f"({want_reason!r} absent) — got: {stderr.strip()[:180]}")
            fails += 1
        else:
            if want_reason is not None:
                reasoned += 1
            print(f"OK  {label}: loud-declined"
                  + (f" ({want_reason})" if want_reason else ""))
    if reasoned == 0:
        print("VACUOUS: no decline was checked for its machine reason")
        fails += 1
    print(f"\n{len(DECLINED) - fails}/{len(DECLINED)} declined ops loud-declined "
          f"({reasoned} with their machine reason asserted)")
    print("RESULT:", "PASS — decline matrix honest"
          if not fails else f"FAIL ({fails} silent)")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
