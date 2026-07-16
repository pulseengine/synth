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

# Each entry: (label, wat body). All must FAIL to compile with -b aarch64.
DECLINED = [
    ("i32.div_s", '(func (export "f") (param i32 i32) (result i32) '
                  '(i32.div_s (local.get 0) (local.get 1)))'),
    ("i32.div_u", '(func (export "f") (param i32 i32) (result i32) '
                  '(i32.div_u (local.get 0) (local.get 1)))'),
    ("i32.rem_s", '(func (export "f") (param i32 i32) (result i32) '
                  '(i32.rem_s (local.get 0) (local.get 1)))'),
    ("i32.rem_u", '(func (export "f") (param i32 i32) (result i32) '
                  '(i32.rem_u (local.get 0) (local.get 1)))'),
    ("i64.div_s", '(func (export "f") (param i64 i64) (result i64) '
                  '(i64.div_s (local.get 0) (local.get 1)))'),
    ("i64.rem_u", '(func (export "f") (param i64 i64) (result i64) '
                  '(i64.rem_u (local.get 0) (local.get 1)))'),
    ("i32.popcnt", '(func (export "f") (param i32) (result i32) '
                   '(i32.popcnt (local.get 0)))'),
    ("i64.popcnt", '(func (export "f") (param i64) (result i64) '
                   '(i64.popcnt (local.get 0)))'),
    # m3 (#787) landed non-trapping scalar floats (add/sub/mul/div/cmp/convert/
    # reinterpret) — those are now SUPPORTED, so the honesty gate moves to the
    # floats that DELIBERATELY stay declined:
    #   - trapping float→int truncation: A64 FCVTZS/FCVTZU SATURATE where WASM
    #     TRAPS (the #709 more-total-than-WASM soundness class) — must NOT lower.
    #   - min/max: WASM NaN-propagation semantics differ from A64 FMIN/FMAX.
    ("i32.trunc_f32_s", '(func (export "f") (param f32) (result i32) '
                        '(i32.trunc_f32_s (local.get 0)))'),
    ("f32.min", '(func (export "f") (param f32 f32) (result f32) '
                '(f32.min (local.get 0) (local.get 1)))'),
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
    for label, body in DECLINED:
        ok, stderr = compiles_ok(body)
        if ok:
            print(f"BUG {label}: compiled — expected a LOUD decline (silent miscompile risk)")
            fails += 1
        else:
            print(f"OK  {label}: loud-declined")
    print(f"\n{len(DECLINED) - fails}/{len(DECLINED)} declined ops loud-declined")
    print("RESULT:", "PASS — decline matrix honest"
          if not fails else f"FAIL ({fails} silent)")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
