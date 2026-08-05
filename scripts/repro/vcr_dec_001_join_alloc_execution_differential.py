#!/usr/bin/env python3
# ci-status: wired
"""VCR-DEC-001 increments 2+3 — EXECUTION differential for the join- and
call-aware graph-colouring allocator (`SYNTH_GRAPH_ALLOC=1`, epic #242).

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

**Increment 3 (v0.54) makes that argument SHARPER, not weaker.** Colouring
across CALLS is driven by one shared AAPCS contract (`liveness::call_effect`),
consumed by the pass AND by `validate_cfg_rewrite`. Sharing is deliberate — two
hand-maintained copies would be the VCR-ORACLE mirror-pinning failure mode — but
it means NEITHER validator can catch an error IN the contract itself. Only
execution can. So the CALL SHAPES are gated here as their own population, with
their own non-vacuity floor: a run in which no call-containing function diverges
FAILS, because the increment-3 reach would then be gating nothing (#890).

What is gated, per fixture function:
  (E) ENGAGEMENT — the allocator must APPLY, and the flag-on `.text` must
      actually DIFFER from flag-off. Without both, the harness would be
      re-testing the shipping compiler and would pass vacuously; it FAILS
      instead. A case DECLARED to be a call shape must additionally CONTAIN a
      Thumb `bl`/`blx` in its emitted body — self-declaration verified against
      bytes, so a fixture that stops containing a call (inlined away, shape
      changed) fails loudly instead of silently degrading the population.
  (1) EXECUTION — unicorn runs the flag-ON image and its return value AND the
      compared linear-memory window must equal wasmtime's on every input.
      Arguments follow AAPCS: 0-3 in R0-R3, 4+ on the stack (8-byte aligned),
      which is what makes the 5/6/7-argument call fixtures test the argument
      half of the contract and not just the clobber half.
  (2) VCR-RA-003 — `validate_final_allocation` must return Consistent for every
      applied function (observed via SYNTH_RA003_VERBOSE, not inferred from the
      exit code), and no violation may be reported.

**Increment 4 (v0.55, VCR-REACH-001) makes it a third time.** The i64
register-PAIR model (`liveness::pair_effect`) is consumed by the pass,
`validate_cfg_rewrite` AND the ABI observable contract, so no static instrument
here can catch an error IN the model. The i64-pair shapes get their own
population, their own >=4 floor, and a SECOND floor of >=2 functions containing a
real i64 SHIFT expansion — verified in the EMITTED BYTES (`contains_i64_shift`),
because the shift family is the only member whose model claims an operand is
CLOBBERED and whose distinctness constraints are path-dependent.

MUTATION MATRIX for increment 4, run against this harness. Reported in full,
including the one that does NOT go red, because a mutation matrix that only
lists its successes is not evidence:

  A. `pair_effect` drops BOTH `rm_lo` and `rm_hi` from the shift clobber set.
     -> RED. `rewrite_op`'s RMW-agreement check on `rm_lo` can no longer be
     satisfied, so every shift function DECLINES and the engagement floor fires
     (PAIRSHAPES 9 -> 3, SHIFTSHAPES 6 -> 0). Caught, but by refusal-to-emit
     rather than by a wrong value.

  B. `pair_effect` drops ONLY `rm_hi`, coherently (absent from defs AND uses, so
     pass and both validators agree the shift leaves it alone).
     -> GREEN. NOT CAUGHT, and this is an honest residual, not an oversight:
     tried against four shift fixtures including two built specifically for
     register pressure (`shl_pressure`, `shl_pressure8`, eight i32 values live
     across the shift). The churn-minimising colour bias fills R0-R3 first and
     the shift-amount pair sits in callee-saved R4-R8, so no live web is ever
     placed on the ORIGINAL `rm_hi` register and the clobber is unobservable on
     this corpus. The `rm_hi` half of the model is therefore BELT-AND-BRACES
     (sound, and cheap) rather than execution-gated. Closing it needs a fixture
     that forces a live value onto the shift amount's high-half register — a
     named follow-up, not a claim made here.

  C. The EARLY-CLOBBER interference edges are deleted (`pair_early_clobber`, the
     obligation a defs/uses pair structurally cannot express).
     -> RED, and this is the sharp one. The colourer coalesces `I64Ldr`'s `rdlo`
     onto a `base` the second `LDR` still re-reads. `validate_cfg_rewrite`
     ACCEPTS all 7 functions, VCR-RA-003 reports Consistent on all 7, and the
     ABI observable contract passes all 7 — three static instruments green — and
     only this gate fails, with 3 WRONG VALUES. A third counterexample to the
     idea that per-compilation validation is an independent check on codegen.

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
    UC_ARM_REG_R3,
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
# AAPCS core argument registers; arguments past the fourth go on the stack.
ARG_REGS = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]

# (fixture, function, [arg tuples], kind) where kind is "join" | "call" | "pair".
#
# JOIN shapes (increment 2): real if/else, if-without-else, the desugared
# block+br_if form, an early (non-tail) return, counted and data-dependent
# loops, and the two-level `br_if` exit — with inputs that take BOTH sides of
# every branch (a one-sided input set would never execute the arm whose
# register the colourer moved).
#
# CALL shapes (increment 3, `is_call_shape=True`): the AAPCS contract has two
# halves and both are covered. The CLOBBER half — a value live ACROSS a `bl`
# must not be homed in caller-saved scratch — is what `local_promote_cross_call`
# and `intra_module_callee_saved` were written for (their whole point is that a
# caller-saved home is observably wrong), plus a self-recursive `recurse` whose
# every activation re-enters the same allocation. The ARGUMENT half — the
# registers a call READS must still hold what the callee expects — is covered by
# the 5/6/7-argument fixtures, whose callees pack each argument into a distinct
# nibble, so ANY dropped, shifted or mis-assigned argument (register OR stack)
# changes the result.
CASES = [
    ("cf_shapes_500.wat", "real_ifelse", [(0,), (1,), (7,)], "join"),
    ("cf_shapes_500.wat", "real_if", [(0,), (1,)], "join"),
    ("cf_shapes_500.wat", "br_func", [(0,), (1,)], "join"),
    ("cf_shapes_500.wat", "early_ret", [(0,), (1,)], "join"),
    ("provenance_branches_396.wat", "decide", [(0, 0), (5, 3), (3, 5), (100, 1)], "join"),
    ("aarch64_ctrlflow_851.wat", "count_sum", [(0,), (1,), (5,), (17,)], "join"),
    ("aarch64_ctrlflow_851.wat", "countdown", [(0,), (1,), (9,)], "join"),
    # do_while_count(0) is deliberately absent: `n` starts at 0, so the
    # bottom-test loop runs 2**32 times before wrapping back to the exit. It
    # terminates in wasmtime (JIT) but not within any emulator instruction
    # budget, so it measures the budget, not the compiler.
    ("aarch64_ctrlflow_851.wat", "do_while_count", [(1,), (6,), (23,)], "join"),
    ("loop_param_bound_663.wat", "sum_const", [(0, 0), (3, 4)], "join"),
    ("loop_param_bound_663.wat", "sum_below", [(0, 0), (1, 5), (4, 4), (2, 9)], "join"),
    ("if_else_result_343.wat", "pick", [(0,), (1,), (0xFFFFFFFF,)], "join"),
    ("if_else_result_343.wat", "pick2", [(0,), (1,)], "join"),
    ("brif_outer_740.wat", "poll", [(7, 0), (200, 0), (200, 1), (5, 3)], "join"),
    # ---- increment 3: CALL shapes ------------------------------------------
    ("local_promote_cross_call.wat", "cross_call", [(0,), (5,), (100,), (0xFFFF,)], "call"),
    ("intra_module_callee_saved.wat", "a", [(0,), (7,), (100,)], "call"),
    ("stack_canary_687.wat", "recurse", [(0,), (1,), (5,), (12,)], "call"),
    ("call_5args.wat", "caller", [(1, 2, 3, 4, 5), (0, 0, 0, 0, 9), (15, 1, 2, 4, 8)], "call"),
    ("call_6_7args.wat", "call6", [(1, 2, 3, 4, 5, 6), (0, 0, 0, 0, 0, 7)], "call"),
    ("call_6_7args.wat", "call7", [(1, 2, 3, 4, 5, 6, 7), (0, 0, 0, 0, 0, 0, 9)], "call"),
    # ---- increment 4 (VCR-REACH-001): i64 register-PAIR shapes --------------
    # `liveness::pair_effect` is consumed by the pass AND by both dataflow
    # validators, so — exactly as for increment 3's AAPCS contract — NEITHER of
    # them can catch an error IN the model. Only execution can, so these get
    # their own population and their own non-vacuity floor.
    #
    # Shift-amount inputs straddle the expansion's internal `BPL`: `s < 32`
    # takes the small-shift arm and `s >= 32` the large one, and the
    # distinctness constraints differ between the two. 100 additionally exceeds
    # 63, so the `AND rm_lo, rm_lo, #63` in-place mask is OBSERVABLE — that is
    # what makes the "rm_lo/rm_hi are not really clobbered" mutation go red
    # instead of passing vacuously.
    ("vcr_reach_001_i64_pair.wat", "shl_amt_live",
     [(1, 0), (1, 5), (1, 31), (1, 32), (1, 45), (0x1234, 100), (0xFFFFFFFF, 63)], "pair"),
    ("vcr_reach_001_i64_pair.wat", "shl_amt_live_hi",
     [(1, 0), (1, 5), (1, 31), (1, 32), (1, 45), (0x1234, 100)], "pair"),
    ("vcr_reach_001_i64_pair.wat", "shru_amt_live",
     [(0x7FFFFFFF, 0), (0x7FFFFFFF, 5), (0x7FFFFFFF, 32), (0xFFFFFFFF, 40),
      (0x1234, 100)], "pair"),
    # `I64Ldr` early-clobber: the address is DEAD after the load, so only the
    # interference edge stops `rdlo` being coalesced onto `base`. The HIGH-word
    # variant is the one the SECOND load produces.
    ("vcr_reach_001_i64_pair.wat", "shl_pressure",
     [(1, 0), (1, 5), (1, 32), (3, 45), (0x1234, 100)], "pair"),
    ("vcr_reach_001_i64_pair.wat", "shl_pressure8",
     [(1, 0), (1, 5), (1, 32), (3, 45), (0x1234, 100)], "pair"),
    ("vcr_reach_001_i64_pair.wat", "ld_dead_base",
     [(0, 0x11223344, 0x55667788), (8, 0xFFFFFFFF, 0x0F0F0F0F),
      (0x40, 0, 0xDEADBEEF), (0xFF, 0xCAFEBABE, 0)], "pair"),
    ("vcr_reach_001_i64_pair.wat", "ld_dead_base_lo",
     [(0, 0x11223344), (8, 0xFFFFFFFF), (0x40, 0x5A5A5A5A), (0xFF, 1)], "pair"),
    ("vcr_reach_001_i64_pair.wat", "st_then_ld",
     [(0, 1), (0x10, 0x5A5A), (0x40, 0xFFFFFFFF)], "pair"),
    ("vcr_reach_001_i64_pair.wat", "cmp64",
     [(0, 0), (1, 2), (2, 1), (0xFFFFFFFF, 1), (1, 0xFFFFFFFF)], "pair"),
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


def contains_call(body):
    """True if the Thumb body contains a `bl <imm>` or `blx <reg>`.

    Used to VERIFY a case's `is_call_shape` declaration against the emitted
    bytes: a fixture whose call got inlined away (or whose shape drifted) would
    otherwise keep inflating the increment-3 population while testing nothing.
      bl  <imm>: hw1 = 11110xxxxxxxxxxx, hw2 = 11x1xxxxxxxxxxx
      blx <reg>: 010001111xxxx000
    """
    for i in range(0, len(body) - 1, 2):
        hw = int.from_bytes(body[i:i + 2], "little")
        if (hw & 0xFF87) == 0x4780:
            return True
        if (hw & 0xF800) == 0xF000 and i + 3 < len(body):
            hw2 = int.from_bytes(body[i + 2:i + 4], "little")
            if (hw2 & 0xD000) == 0xD000:
                return True
    return False


def contains_i64_shift(body):
    """True if the Thumb body contains an i64 shift expansion.

    Detected by its opening `AND.W Rd, Rn, #63` — the mask-the-shift-amount-to-6-
    bits step, which no other lowering in the backend emits:
      hw1 = 1111 0000 0000 nnnn   (0xF000 | rn, T2 AND immediate, no S bit)
      hw2 = 0000 dddd 0011 1111   (rd << 8 | 0x3F, i8:imm3 = 0)

    Used to verify the SHIFT half of the increment-4 population against the
    EMITTED BYTES rather than against the case table's own say-so. The shift
    family is where the model is load-bearing (`rm_lo`/`rm_hi` are clobbers, and
    the distinctness constraints are path-dependent), so a fixture that stopped
    emitting a shift — folded to a constant, or lowered some other way — must
    fail loudly instead of quietly leaving that class ungated. Independent of
    the pass: it reads the compiler's output, not its stats.
    """
    for i in range(0, len(body) - 3, 2):
        hw1 = int.from_bytes(body[i:i + 2], "little")
        hw2 = int.from_bytes(body[i + 2:i + 4], "little")
        if (hw1 & 0xFFF0) == 0xF000 and (hw2 & 0x80FF) == 0x003F:
            return True
    return False


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
    # AAPCS: arguments 0-3 in R0-R3, 4+ on the stack with the FIFTH at [sp,#0]
    # at the call boundary and SP 8-byte aligned. Getting this wrong would look
    # exactly like a miscompile on the 5/6/7-argument fixtures, so it is done
    # here rather than by pretending those functions take three arguments.
    stack_args = [a & 0xFFFFFFFF for a in args[len(ARG_REGS):]]
    sp = SP_INIT - ((len(stack_args) * 4 + 7) & ~7 if stack_args else 0)
    for i, val in enumerate(stack_args):
        mu.mem_write(sp + 4 * i, val.to_bytes(4, "little"))
    mu.reg_write(UC_ARM_REG_SP, sp)
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
    engaged_call_functions = 0
    engaged_pair_functions = 0
    engaged_shift_functions = 0
    by_fixture = {}
    for wat, func, argsets, kind in CASES:
        by_fixture.setdefault(wat, []).append((func, argsets, kind))

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

        for func, argsets, kind in entries:
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
            # A declared CALL shape must really contain a call in the emitted
            # body — self-declaration verified against the bytes, so an inlined
            # -away call cannot silently inflate the increment-3 population.
            if kind == "call" and not contains_call(body_on):
                print(f"FAIL {wat}:{func} — declared a CALL shape but the emitted "
                      f"body contains no bl/blx: it gates nothing about the AAPCS "
                      f"call contract.")
                fails += 1
                continue
            engaged_functions += 1
            if kind == "call":
                engaged_call_functions += 1
            if kind == "pair":
                engaged_pair_functions += 1
                if contains_i64_shift(body_on):
                    engaged_shift_functions += 1

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
    print(f"\nengaged functions (flag-on bytes differ): {engaged_functions} "
          f"(of which CALL shapes: {engaged_call_functions})")
    if engaged_functions < 10:
        print("VACUOUS: fewer than 10 functions have divergent flag-on bytes — "
              "the join allocator's reach regressed; this gate no longer gates.")
        fails += 1
    # Increment 3 gets its OWN floor. The AAPCS call contract is SHARED by the
    # pass and `validate_cfg_rewrite`, so execution is the only thing that can
    # catch an error in the contract itself — a run with no divergent
    # call-containing function would leave that class entirely ungated while
    # still reporting PASS (#890).
    if engaged_call_functions < 4:
        print("VACUOUS: fewer than 4 CALL-containing functions have divergent "
              "flag-on bytes — increment 3's reach regressed and the AAPCS call "
              "contract is no longer execution-gated.")
        fails += 1
    # Increment 4 (VCR-REACH-001) gets its own floor for the same reason: the
    # i64 register-pair model is SHARED by the pass, `validate_cfg_rewrite` and
    # the ABI observable contract, so execution is the only instrument that can
    # catch an error in the model itself.
    print(f"engaged i64-PAIR functions: {engaged_pair_functions} "
          f"(of which contain a real i64 SHIFT expansion: {engaged_shift_functions})")
    if engaged_pair_functions < 4:
        print("VACUOUS: fewer than 4 i64 register-PAIR functions have divergent "
              "flag-on bytes — increment 4's reach regressed and `pair_effect` is "
              "no longer execution-gated.")
        fails += 1
    # And the SHIFT half specifically. The shift family is the only member whose
    # model claims an operand is CLOBBERED (`rm_lo` in place, `rm_hi` as a temp)
    # and whose distinctness constraints are PATH-dependent; a population of
    # loads and compares alone would leave exactly the dangerous part ungated
    # while still reporting PASS.
    if engaged_shift_functions < 2:
        print("VACUOUS: fewer than 2 divergent functions contain an i64 SHIFT "
              "expansion (verified in the emitted bytes, not declared) — the "
              "`rm_lo`/`rm_hi` clobber model is no longer execution-gated.")
        fails += 1

    # Machine-readable summary the CI wiring greps for a NON-ZERO count:
    # exit 0 alone is not trusted (the "0 ops accepted PASS" lesson).
    print(f"VCR-DEC-001-JOIN CHECKS={checks - fails}/{checks} "
          f"ENGAGED={engaged_functions} CALLSHAPES={engaged_call_functions} "
          f"PAIRSHAPES={engaged_pair_functions} SHIFTSHAPES={engaged_shift_functions}")
    print("RESULT:", "PASS" if not fails else f"FAIL ({fails} problem(s))")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
