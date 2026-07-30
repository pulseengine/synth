#!/usr/bin/env python3
# ci-status: wired
"""VCR-DEC-001 increment 2 — EXECUTION differential for the join-aware
graph-colouring allocator (`SYNTH_GRAPH_ALLOC=1`, epic #242).

**Why this exists.** Increment 1 (v0.50) could claim execution correctness
TRANSITIVELY: on a whole straight-line function the spike and the shipping
`reallocate_function` share pins, `chaitin_core` and scope, so their bytes were
identical BY CONSTRUCTION and the frozen wasmtime differentials already gated
them. Increment 2 breaks that: colouring across joins uses a different colour
bias and a different pin set, so the flag-on bytes genuinely DIVERGE. A
byte-only gate would therefore certify nothing about the new bytes, and
`validate_cfg_rewrite` — the pass's own acceptance oracle — shares the CFG shape
with the pass it validates (#872 is the standing lesson that a validator can
share its pass's blind spot). So the new bytes get executed.

What is gated, per fixture function:
  (E) ENGAGEMENT — the allocator must APPLY, and the flag-on `.text` must
      actually DIFFER from flag-off. Without both, the harness would be
      re-testing the shipping compiler and would pass vacuously; it FAILS
      instead.
  (1) EXECUTION — unicorn runs the flag-ON image and its return value AND the
      compared linear-memory window must equal wasmtime's on every input.
  (2) VCR-RA-003 — `validate_final_allocation` must return Consistent for every
      applied function (observed via SYNTH_RA003_VERBOSE, not inferred from the
      exit code), and no violation may be reported.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 \\
      scripts/repro/vcr_dec_001_join_alloc_execution_differential.py
Exits nonzero on any mismatch, any missing engagement, or any RA-003 verdict
other than Consistent.
"""

import os
import subprocess
import sys
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
    UC_ARM_REG_R9,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

REPRO = Path(__file__).resolve().parent
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

LIN = 0x2000_0000
LIN_SIZE = 0x1_0000
CODE = 0x0
SP_INIT = LIN + 0x2_0000
MEM_WINDOW = 0x100
ARG_REGS = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2]

# (fixture, function, [arg tuples]). Chosen to cover every join shape the
# allocator now colours: real if/else, if-without-else, the desugared
# block+br_if form, an early (non-tail) return, counted and data-dependent
# loops, and the two-level `br_if` exit — with inputs that take BOTH sides of
# every branch (a one-sided input set would never execute the arm whose
# register the colourer moved).
CASES = [
    ("cf_shapes_500.wat", "real_ifelse", [(0,), (1,), (7,)]),
    ("cf_shapes_500.wat", "real_if", [(0,), (1,)]),
    ("cf_shapes_500.wat", "br_func", [(0,), (1,)]),
    ("cf_shapes_500.wat", "early_ret", [(0,), (1,)]),
    ("provenance_branches_396.wat", "decide", [(0, 0), (5, 3), (3, 5), (100, 1)]),
    ("aarch64_ctrlflow_851.wat", "count_sum", [(0,), (1,), (5,), (17,)]),
    ("aarch64_ctrlflow_851.wat", "countdown", [(0,), (1,), (9,)]),
    # do_while_count(0) is deliberately absent: `n` starts at 0, so the
    # bottom-test loop runs 2**32 times before wrapping back to the exit. It
    # terminates in wasmtime (JIT) but not within any emulator instruction
    # budget, so it measures the budget, not the compiler.
    ("aarch64_ctrlflow_851.wat", "do_while_count", [(1,), (6,), (23,)]),
    ("loop_param_bound_663.wat", "sum_const", [(0, 0), (3, 4)]),
    ("loop_param_bound_663.wat", "sum_below", [(0, 0), (1, 5), (4, 4), (2, 9)]),
    ("if_else_result_343.wat", "pick", [(0,), (1,), (0xFFFFFFFF,)]),
    ("if_else_result_343.wat", "pick2", [(0,), (1,)]),
    ("brif_outer_740.wat", "poll", [(7, 0), (200, 0), (200, 1), (5, 3)]),
]

CLEAR = [
    "SYNTH_NO_CMP_SELECT_FUSE", "SYNTH_NO_LOCAL_PROMOTE", "SYNTH_NO_IMM_SHIFT_FOLD",
    "SYNTH_NO_STACK_FWD", "SYNTH_SPILL_REALLOC", "SYNTH_CONST_CSE", "SYNTH_BASE_CSE",
    "SYNTH_DEAD_FRAME_ELIM", "SYNTH_UXTH_FOLD", "SYNTH_GRAPH_ALLOC",
    "SYNTH_SHIFT_MASK_ELIDE", "SYNTH_RANGE_REALLOC",
]


def compile_image(wat, out, graph_alloc):
    env = {k: v for k, v in os.environ.items()}
    for k in CLEAR:
        env.pop(k, None)
    if graph_alloc:
        env["SYNTH_GRAPH_ALLOC"] = "1"
        env["SYNTH_GRAPH_ALLOC_STATS"] = "1"
        env["SYNTH_RA003_VERBOSE"] = "1"
    r = subprocess.run(
        [SYNTH, "compile", str(REPRO / wat), "-o", out, "-b", "arm",
         "--target", "cortex-m4", "--all-exports"],
        capture_output=True, text=True, env=env,
    )
    if r.returncode != 0:
        sys.exit(f"compile failed ({wat}, graph_alloc={graph_alloc}): {r.stderr}")
    return r.stderr


def load(elf):
    with open(elf, "rb") as fh:
        f = ELFFile(fh)
        text = f.get_section_by_name(".text").data()
        lin = f.get_section_by_name(".linear_memory")
        syms, sizes = {}, {}
        for sec in f.iter_sections():
            if sec.header.sh_type == "SHT_SYMTAB":
                for s in sec.iter_symbols():
                    if s.name:
                        syms[s.name] = s["st_value"]
                        sizes[s.name] = s["st_size"]
        return text, lin.data() if lin else b"", syms, sizes


def wasmtime_call(wat, func, args):
    """(result_or_None, memory_window). A VOID export returns None — and that
    None is propagated, NOT coerced to 0: for a void function R0 is AAPCS
    scratch, so comparing it against a synthesized 0 would fail for a correct
    compiler (measured: every void `cf_shapes_500` export). Void functions are
    gated on their MEMORY effect instead."""
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, (REPRO / wat).read_bytes())
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    exports = inst.exports(st)
    r = exports[func](st, *[a - (1 << 32) if a >= (1 << 31) else a for a in args])
    mem = exports.get("memory")
    window = bytes(mem.read(st, 0, MEM_WINDOW)) if mem else b""
    return (None if r is None else r & 0xFFFFFFFF), window


def unicorn_call(text, lin_init, faddr, args):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10000)
    mu.mem_map(LIN, 0x2_0000)
    mu.mem_write(CODE, text)
    if lin_init:
        mu.mem_write(LIN, lin_init[:LIN_SIZE])
    mu.reg_write(UC_ARM_REG_R9, LIN + LIN_SIZE)
    mu.reg_write(UC_ARM_REG_R10, LIN_SIZE)
    mu.reg_write(UC_ARM_REG_R11, LIN)
    mu.reg_write(UC_ARM_REG_SP, SP_INIT)
    ret = CODE + 0xFF00
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    mu.reg_write(UC_ARM_REG_LR, ret | 1)
    for reg, val in zip(ARG_REGS, args):
        mu.reg_write(reg, val & 0xFFFFFFFF)
    try:
        mu.emu_start((faddr & ~1) | 1, ret, timeout=5_000_000, count=500_000)
    except UcError as e:
        return f"ERR:{e}", None
    # A count/timeout-limited stop leaves PC INSIDE the function and the
    # registers mid-flight. Comparing those against wasmtime's real result is
    # how a truncated run gets read as a pass (or, worse, as a miscompile —
    # measured on the 2**32-iteration `do_while_count(0)`, where the flag-off
    # build happened to leave the right value in R0 and the flag-on build did
    # not). Report it as its own failure instead.
    pc = mu.reg_read(UC_ARM_REG_PC)
    if (pc & ~1) != (ret & ~1):
        return f"DID-NOT-RETURN@0x{pc:X}", None
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF, bytes(mu.mem_read(LIN, MEM_WINDOW))


def main():
    fails = 0
    checks = 0
    engaged_functions = 0
    by_fixture = {}
    for wat, func, argsets in CASES:
        by_fixture.setdefault(wat, []).append((func, argsets))

    for wat, entries in by_fixture.items():
        off_elf = f"/tmp/ga_join_{Path(wat).stem}_off.elf"
        on_elf = f"/tmp/ga_join_{Path(wat).stem}_on.elf"
        compile_image(wat, off_elf, False)
        stderr_on = compile_image(wat, on_elf, True)

        # ---- (2) VCR-RA-003 on the REAL flag-on output --------------------
        applied = stderr_on.count("whole-function colouring APPLIED")
        consistent = stderr_on.count("VCR-RA-003: Consistent")
        if "register-allocation validation FAILED" in stderr_on:
            print(f"FAIL {wat}: VCR-RA-003 reported a violation")
            fails += 1
        if applied and consistent == 0:
            print(f"FAIL {wat}: {applied} function(s) applied but no "
                  f"'VCR-RA-003: Consistent' verdict observed")
            fails += 1
        print(f"== {wat}: applied={applied} RA003-consistent={consistent} ==")

        text_off, _, syms_off, sizes_off = load(off_elf)
        text_on, lin_init, syms_on, sizes_on = load(on_elf)

        for func, argsets in entries:
            if func not in syms_on:
                print(f"FAIL {wat}:{func} — symbol missing")
                fails += 1
                continue
            # ---- (E) ENGAGEMENT ------------------------------------------
            a_off, n_off = syms_off[func] & ~1, sizes_off.get(func, 0)
            a_on, n_on = syms_on[func] & ~1, sizes_on.get(func, 0)
            body_off = text_off[a_off:a_off + n_off]
            body_on = text_on[a_on:a_on + n_on]
            if body_off == body_on:
                print(f"FAIL {wat}:{func} — flag-on bytes IDENTICAL to flag-off: "
                      f"this case gates nothing (the allocator no longer reaches "
                      f"it). Re-pick the fixture or fix the regression.")
                fails += 1
                continue
            engaged_functions += 1

            # ---- (1) EXECUTION -------------------------------------------
            for args in argsets:
                gt_ret, gt_mem = wasmtime_call(wat, func, args)
                got_ret, got_mem = unicorn_call(text_on, lin_init, a_on, args)
                mem_ok = got_mem == gt_mem if gt_mem else True
                # A void export has no result register to compare (R0 is AAPCS
                # scratch past the return); its memory effect is the observable.
                ret_ok = gt_ret is None or got_ret == gt_ret
                ok = isinstance(got_ret, int) and ret_ok and mem_ok
                if gt_ret is None and got_mem is None:
                    ok = False  # DID-NOT-RETURN / emulation error
                checks += 1
                fails += 0 if ok else 1
                tag = f"0x{got_ret:08X}" if isinstance(got_ret, int) else got_ret
                gt_tag = "void" if gt_ret is None else f"0x{gt_ret:08X}"
                argtxt = ",".join(str(a) for a in args)
                print(f"{'OK  ' if ok else 'FAIL'} {func}({argtxt}) = {tag} "
                      f"(wasmtime {gt_tag}) "
                      f"{'mem==' if mem_ok else 'mem!=<--'}")

    # Non-vacuity: the whole harness is worthless if the allocator stopped
    # changing bytes anywhere. Require a real population.
    print(f"\nengaged functions (flag-on bytes differ): {engaged_functions}")
    if engaged_functions < 10:
        print("VACUOUS: fewer than 10 functions have divergent flag-on bytes — "
              "the join allocator's reach regressed; this gate no longer gates.")
        fails += 1

    # Machine-readable summary the CI wiring greps for a NON-ZERO count:
    # exit 0 alone is not trusted (the "0 ops accepted PASS" lesson).
    print(f"VCR-DEC-001-JOIN CHECKS={checks - fails}/{checks} "
          f"ENGAGED={engaged_functions}")
    print("RESULT:", "PASS" if not fails else f"FAIL ({fails} problem(s))")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
