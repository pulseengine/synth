#!/usr/bin/env python3
"""#538 milestone-2 — assert the aarch64 decline matrix stays HONEST.

The broadening in m2 covers the full i32/i64 integer ALU, but four classes are
DELIBERATELY still declined, and the contract is that they LOUD-decline (a
non-zero exit / "skipping" / compile error) — never silently emit wrong code:

  - div/rem (i32+i64): A64 SDIV/UDIV do not trap on /0 or INT_MIN/-1; WASM must
    trap. Naive lowering = the "more-total-than-WASM" silent-miscompile class.
  - popcnt: no scalar A64 popcount pre-SVE.
  - f32/f64 scalar ops: dropped at the decoder (`_ => None`) → the backend
    refuses to emit a partial body (#369/#554).

This harness compiles a module per declined op and asserts the compile FAILS
(loud), so a future accidental silent-lowering of any of them is caught.

Run:  SYNTH=<target>/debug/synth python scripts/repro/aarch64_m2_decline_538.py
"""
import os
import subprocess
import sys
import tempfile

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

# Each entry: (label, wat body) or (label, wat body, reason_substring). All must
# FAIL to compile with -b aarch64; when a reason substring is given, the
# diagnostic must CONTAIN it — a decline with the wrong reason is a different
# bug than a decline, and "it failed somehow" is not evidence.
DECLINED = [
    # #851 landed div/rem (SDIV/UDIV+MSUB with WASM ÷0 + INT_MIN/-1 trap
    # guards), popcnt (SIMD CNT/ADDV), and f64<->i64 reinterpret — those are
    # now SUPPORTED and execution-verified (aarch64_divrem_851_differential.py
    # + the native matrix), so they moved off this honesty list. m3 (#787)
    # landed non-trapping scalar floats; m4 landed the #709-class conversions
    # (domain-guarded i32.trunc_f32/f64_s/u, FMIN/FMAX, copysign). The honesty
    # gate now covers what DELIBERATELY stays declined:
    #   - rounding (ceil/floor/trunc/nearest): f64.floor is DECODED and must
    #     loud-decline at the aarch64 SELECTOR; f32.floor is dropped at decode
    #     (both paths must stay loud, never silent).
    #   - i64<->float conversions: need i64-width FCVTZS/SCVTF forms + the
    #     64-bit boundary guards (a later increment).
    ("f64.floor", '(func (export "f") (param f64) (result f64) '
                  '(f64.floor (local.get 0)))'),
    ("f32.floor", '(func (export "f") (param f32) (result f32) '
                  '(f32.floor (local.get 0)))'),
    ("i64.trunc_f64_s", '(func (export "f") (param f64) (result i64) '
                        '(i64.trunc_f64_s (local.get 0)))'),

    # ---- #851 lane L3: globals + call_indirect LOWER, but these shapes
    #      deliberately do NOT. Each must decline with its own machine reason —
    #      the lane's rule is that an unrepresentable construct fails the
    #      compile naming what is missing, never ships a guessed region.
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
    ("table slot holding an IMPORTED function",
     '(type $b (func (param i32 i32) (result i32))) '
     '(import "env" "h" (func $h (type $b))) '
     '(table 2 funcref) (elem (i32.const 0) $h) '
     '(func (export "f") (param i32) (result i32) '
     '(call_indirect (type $b) (i32.const 1) (i32.const 2) (local.get 0)))',
     "imported function"),
    ("non-leaf FLOAT param (homing needs an FP store)",
     '(func $g (result i32) (i32.const 1)) '
     '(func (export "f") (param f32) (result f32) '
     '(drop (call $g)) (local.get 0))',
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
