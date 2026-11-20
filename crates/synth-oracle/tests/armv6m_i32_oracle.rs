//! RQ-91-M0I32 (Refs #1301, #1741): the ARMv6-M (Cortex-M0/M0+) i32 lowering,
//! judged on unicorn's Cortex-M0 model against kiln.
//!
//! An embedded per-op probe set (i32 constants of every materialization
//! shape, arithmetic with register and immediate operands, bitwise, shifts and
//! rotates, all eleven compares, select) and control-flow shapes (if/else,
//! block + br_if, loop, br_table, early return, unreachable, frame locals) is
//! compiled by synth for `cortex-m0` and `cortex-m0plus` (`--relocatable`).
//!
//! 1. ACCEPTANCE, EXACT both ways: the exports that compile are exactly
//!    [`ACCEPTED`]; a second module of shapes this lane does not lower
//!    (division, bit counts, i64 arithmetic, memory, globals, stack-passed
//!    parameters; direct calls are lowered since RQ-92-WDGTHIN and have their own
//!    oracle, `armv6m_call_oracle.rs`) declines
//!    exactly [`DECLINED`], each with the ARMv6-M diagnostic. RED on the stack
//!    base, where only a handful of these compiled.
//! 2. ARMv6-M, DECODED: every halfword of every accepted function is in the
//!    frozen LLVM-derived ARMv6-M table (`tests/fixtures/armv6m_legal16_1301.json`),
//!    no 32-bit encoding but BL / DMB / DSB / ISB, no 16-bit LDR (literal), and
//!    no write to R8-R12. This is the leg that sees IT and CBZ/CBNZ, which the
//!    unicorn M0 model EXECUTES (port of leg B of
//!    `scripts/repro/armv6m_1301_differential.py`). The cortex-m0plus `.text` is
//!    byte-identical to the cortex-m0 `.text`.
//! 3. EXECUTION: every accepted probe x vector runs on kiln and on unicorn's
//!    Cortex-M0 model (`Cpu::CortexM0`, model id read back by the harness), and
//!    is required to AGREE. The vectors include the signed and carry edges of every
//!    compare. The harness also checks R4-R11 preserved (R7, the lowering
//!    scratch, and R8 included) and SP balanced on every run.
//!
//! Potency: planted IT, CBZ, MOVW and `mov r8, r0` each red the decode leg; a
//! cortex-m3 `and.w` faults as ILLEGAL on the M0 model; a planted wrong
//! reference (`le_s` for `lt_s`) disagrees exactly on the equal vectors.
//!
//! Cold review 15: the far-branch, `rd == rm` and scratch-liveness probes
//! kill the five mutants that survived the first version (far `B<cond>` not
//! inverted / off by one halfword, the commutative rule and shift-by-register
//! with `rd == rm`, scratch always dead), each measured red against a
//! mutant binary. The `d_rung_*` declines are the shapes only the selector's
//! register-pressure recovery rungs select (F1, wrong values before they were
//! declined on ARMv6-M). The two #1754 `select` shapes, pinned wrong by
//! RQ-91-M0I32, are accepted probes since the fix (`s1754_*`).
//!
//! Needs `--features exec`. `SYNTH` may name a prebuilt binary.

#![cfg(feature = "exec")]

use std::collections::BTreeSet;
use std::path::PathBuf;

use synth_oracle::armv6m::{legal16_table, v6m_violations};
use synth_oracle::compare::{EmuOutcome, RefOutcome, Verdict};
use synth_oracle::emulate::{self, Cpu, EmuConfig};
use synth_oracle::reference::Imports;
use synth_oracle::synth::{CompiledObject, compile};
use synth_oracle::value::{ValType, WasmValue, export_signature};
use synth_oracle::{Case, run_case};

const FUEL: u64 = 1_000_000;

/// Accept candidates: call-free, memory-free, float-free, at most four
/// argument words, at most one result. Loops are bounded by masking.
const PROBES_WAT: &str = r#"
(module
  ;; --- constants: one per materialization shape ---
  (func (export "c_0") (result i32) i32.const 0)
  (func (export "c_42") (result i32) i32.const 42)
  (func (export "c_255") (result i32) i32.const 255)
  (func (export "c_256") (result i32) i32.const 256)
  (func (export "c_ffff") (result i32) i32.const 0xffff)
  (func (export "c_10000") (result i32) i32.const 0x10000)
  (func (export "c_big") (result i32) i32.const 0x12345678)
  (func (export "c_neg1") (result i32) i32.const -1)
  (func (export "c_neg256") (result i32) i32.const -256)
  (func (export "c_min") (result i32) i32.const 0x80000000)
  (func (export "c_max") (result i32) i32.const 0x7fffffff)
  (func (export "c_dead") (result i32) i32.const 0xdeadbeef)
  (func (export "c_c0007fff") (result i32) i32.const 0xc0007fff)
  ;; --- add / sub with immediates on both sides of every encoding limit ---
  (func (export "add_1") (param i32) (result i32) local.get 0 i32.const 1 i32.add)
  (func (export "add_7") (param i32) (result i32) local.get 0 i32.const 7 i32.add)
  (func (export "add_8") (param i32) (result i32) local.get 0 i32.const 8 i32.add)
  (func (export "add_200") (param i32) (result i32) local.get 0 i32.const 200 i32.add)
  (func (export "add_255") (param i32) (result i32) local.get 0 i32.const 255 i32.add)
  (func (export "add_256") (param i32) (result i32) local.get 0 i32.const 256 i32.add)
  (func (export "add_1000") (param i32) (result i32) local.get 0 i32.const 1000 i32.add)
  (func (export "add_neg1") (param i32) (result i32) local.get 0 i32.const -1 i32.add)
  (func (export "add_neg300") (param i32) (result i32) local.get 0 i32.const -300 i32.add)
  (func (export "add_big") (param i32) (result i32) local.get 0 i32.const 0x12345678 i32.add)
  (func (export "sub_5") (param i32) (result i32) local.get 0 i32.const 5 i32.sub)
  (func (export "sub_300") (param i32) (result i32) local.get 0 i32.const 300 i32.sub)
  (func (export "rsub_300") (param i32) (result i32) i32.const 300 local.get 0 i32.sub)
  ;; --- register binops ---
  (func (export "add") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)
  (func (export "sub") (param i32 i32) (result i32) local.get 0 local.get 1 i32.sub)
  (func (export "sub_rev") (param i32 i32) (result i32) local.get 1 local.get 0 i32.sub)
  (func (export "mul") (param i32 i32) (result i32) local.get 0 local.get 1 i32.mul)
  (func (export "mul_10") (param i32) (result i32) local.get 0 i32.const 10 i32.mul)
  (func (export "and") (param i32 i32) (result i32) local.get 0 local.get 1 i32.and)
  (func (export "or") (param i32 i32) (result i32) local.get 0 local.get 1 i32.or)
  (func (export "xor") (param i32 i32) (result i32) local.get 0 local.get 1 i32.xor)
  (func (export "and_ff") (param i32) (result i32) local.get 0 i32.const 0xff i32.and)
  (func (export "and_ffff") (param i32) (result i32) local.get 0 i32.const 0xffff i32.and)
  (func (export "and_7fff") (param i32) (result i32) local.get 0 i32.const 0x7fff i32.and)
  (func (export "or_c0000000") (param i32) (result i32) local.get 0 i32.const 0xc0000000 i32.or)
  (func (export "xor_neg1") (param i32) (result i32) local.get 0 i32.const -1 i32.xor)
  (func (export "and_or_xor") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.and local.get 0 local.get 1 i32.or i32.xor)
  ;; --- shifts and rotates, by register and by immediate ---
  (func (export "shl") (param i32 i32) (result i32) local.get 0 local.get 1 i32.shl)
  (func (export "shr_s") (param i32 i32) (result i32) local.get 0 local.get 1 i32.shr_s)
  (func (export "shr_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.shr_u)
  (func (export "rotl") (param i32 i32) (result i32) local.get 0 local.get 1 i32.rotl)
  (func (export "rotr") (param i32 i32) (result i32) local.get 0 local.get 1 i32.rotr)
  (func (export "shl_1") (param i32) (result i32) local.get 0 i32.const 1 i32.shl)
  (func (export "shl_31") (param i32) (result i32) local.get 0 i32.const 31 i32.shl)
  (func (export "shl_32") (param i32) (result i32) local.get 0 i32.const 32 i32.shl)
  (func (export "shr_u_1") (param i32) (result i32) local.get 0 i32.const 1 i32.shr_u)
  (func (export "shr_u_31") (param i32) (result i32) local.get 0 i32.const 31 i32.shr_u)
  (func (export "shr_s_1") (param i32) (result i32) local.get 0 i32.const 1 i32.shr_s)
  (func (export "shr_s_31") (param i32) (result i32) local.get 0 i32.const 31 i32.shr_s)
  (func (export "rotl_3") (param i32) (result i32) local.get 0 i32.const 3 i32.rotl)
  (func (export "rotr_7") (param i32) (result i32) local.get 0 i32.const 7 i32.rotr)
  ;; --- unary ---
  (func (export "ext8") (param i32) (result i32) local.get 0 i32.extend8_s)
  (func (export "ext16") (param i32) (result i32) local.get 0 i32.extend16_s)
  (func (export "eqz") (param i32) (result i32) local.get 0 i32.eqz)
  ;; --- compares, register and immediate ---
  (func (export "eq") (param i32 i32) (result i32) local.get 0 local.get 1 i32.eq)
  (func (export "ne") (param i32 i32) (result i32) local.get 0 local.get 1 i32.ne)
  (func (export "lt_s") (param i32 i32) (result i32) local.get 0 local.get 1 i32.lt_s)
  (func (export "lt_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.lt_u)
  (func (export "gt_s") (param i32 i32) (result i32) local.get 0 local.get 1 i32.gt_s)
  (func (export "gt_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.gt_u)
  (func (export "le_s") (param i32 i32) (result i32) local.get 0 local.get 1 i32.le_s)
  (func (export "le_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.le_u)
  (func (export "ge_s") (param i32 i32) (result i32) local.get 0 local.get 1 i32.ge_s)
  (func (export "ge_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.ge_u)
  (func (export "lt_s_neg5") (param i32) (result i32) local.get 0 i32.const -5 i32.lt_s)
  (func (export "gt_u_1000") (param i32) (result i32) local.get 0 i32.const 1000 i32.gt_u)
  (func (export "eq_big") (param i32) (result i32) local.get 0 i32.const 0x12345678 i32.eq)
  (func (export "eq_neg1") (param i32) (result i32) local.get 0 i32.const -1 i32.eq)
  ;; --- select ---
  (func (export "select3") (param i32 i32 i32) (result i32)
    local.get 0 local.get 1 local.get 2 select)
  (func (export "select_max") (param i32 i32) (result i32)
    local.get 0 local.get 1 local.get 0 local.get 1 i32.gt_s select)
  (func (export "select_const") (param i32) (result i32)
    i32.const 10 i32.const 20 local.get 0 select)
  ;; --- control flow ---
  (func (export "if_else") (param i32 i32) (result i32)
    local.get 0 if (result i32) local.get 1 i32.const 3 i32.mul
    else local.get 1 i32.const 5 i32.sub end)
  (func (export "if_void") (param i32) (result i32) (local i32)
    local.get 0 if i32.const 5 local.set 1 end local.get 1)
  (func (export "nested_if") (param i32 i32) (result i32)
    local.get 0 if (result i32)
      local.get 1 if (result i32) i32.const 1 else i32.const 2 end
    else
      local.get 1 i32.const 7 i32.lt_u if (result i32) i32.const 3 else i32.const 4 end
    end)
  (func (export "block_br_if") (param i32) (result i32)
    block (result i32) i32.const 7 local.get 0 br_if 0 drop i32.const 9 end)
  (func (export "loop_count") (param i32) (result i32) (local i32)
    local.get 0 i32.const 31 i32.and local.set 0
    block loop
      local.get 0 i32.eqz br_if 1
      local.get 1 local.get 0 i32.add local.set 1
      local.get 0 i32.const 1 i32.sub local.set 0
      br 0
    end end
    local.get 1)
  (func (export "loop_sum") (param i32 i32) (result i32) (local i32)
    local.get 0 i32.const 15 i32.and local.set 0
    block loop
      local.get 0 i32.eqz br_if 1
      local.get 2 local.get 0 i32.add local.get 1 i32.xor local.set 2
      local.get 0 i32.const 1 i32.sub local.set 0
      br 0
    end end
    local.get 2)
  (func (export "br_table") (param i32 i32) (result i32)
    block block block block
      local.get 0 br_table 0 1 2 3
    end local.get 1 i32.const 100 i32.add return
    end local.get 1 i32.const 200 i32.add return
    end local.get 1 i32.const 300 i32.add return
    end local.get 1 i32.const 0x10000 i32.sub)
  (func (export "br_table_shift") (param i32 i32) (result i32) (local i32)
    i32.const -1 local.set 2
    block block
      local.get 1 i32.const 30 i32.shr_u
      br_table 0 1 0 1
    end
    local.get 1 i32.const 32767 i32.and i32.const 1073741824 i32.or local.set 2
    end
    local.get 2)
  (func (export "early_return") (param i32) (result i32)
    local.get 0 if i32.const 1 return end i32.const 0)
  (func (export "trap_if") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.eq if unreachable end local.get 0 local.get 1 i32.sub)
  (func (export "nop_drop") (param i32) (result i32) nop i32.const 1 drop local.get 0)
  (func (export "local_tee") (param i32) (result i32) (local i32)
    local.get 0 local.tee 1 local.get 1 i32.add)
  (func (export "many_locals") (param i32) (result i32) (local i32 i32 i32 i32 i32 i32 i32 i32)
    local.get 0 i32.const 1 i32.add local.set 1
    local.get 1 i32.const 2 i32.add local.set 2
    local.get 2 i32.const 3 i32.add local.set 3
    local.get 3 i32.const 4 i32.add local.set 4
    local.get 4 i32.const 5 i32.add local.set 5
    local.get 5 i32.const 6 i32.add local.set 6
    local.get 6 i32.const 7 i32.add local.set 7
    local.get 7 i32.const 8 i32.add local.set 8
    local.get 1 local.get 2 i32.add local.get 3 local.get 4 i32.add i32.add
    local.get 5 local.get 6 i32.add local.get 7 local.get 8 i32.add i32.add i32.add)
  (func (export "sum4") (param i32 i32 i32 i32) (result i32)
    local.get 0 local.get 1 i32.add local.get 2 i32.sub local.get 3 i32.xor)
  (func (export "void_fn") (param i32))
  ;; --- gale wdg-thin's two call-free exports, verbatim bodies ---
  (func (export "wdg_lock") (param i32) (result i32)
    local.get 0 i32.const 32767 i32.and i32.const -2147483648 i32.or
    i32.const -1
    local.get 0 i32.const -1073741824 i32.and i32.const 1073741824 i32.eq
    select)
  (func (export "wdg_is_running") (param i32) (result i32)
    local.get 0 i32.const -1073741825 i32.gt_u)
  ;; --- i64 shapes that lower entirely to the i32 rules ---
  (func (export "i64_ident") (param i64) (result i64) local.get 0)
  (func (export "i64_and") (param i64 i64) (result i64) local.get 0 local.get 1 i64.and)
  (func (export "i64_or") (param i64 i64) (result i64) local.get 0 local.get 1 i64.or)
  (func (export "i64_xor") (param i64 i64) (result i64) local.get 0 local.get 1 i64.xor)
  (func (export "i64_extend_u") (param i32) (result i64) local.get 0 i64.extend_i32_u)
  ;; --- cold review 15 F3: shapes that reach rules no other probe reaches ---
  ;; Conditional branches beyond the 16-bit B<cond> reach (+-254 B), forward
  ;; and backward: the v6-M encoder's `b<!c> +0; b.n` form.
  (func (export "far_if") (param i32 i32) (result i32)
    local.get 0 if (result i32) local.get 1 i32.const 4660 i32.xor i32.const 3 i32.mul i32.const 4757 i32.xor i32.const 5 i32.mul i32.const 4854 i32.xor i32.const 7 i32.mul i32.const 4951 i32.xor i32.const 9 i32.mul i32.const 5048 i32.xor i32.const 11 i32.mul i32.const 5145 i32.xor i32.const 13 i32.mul i32.const 5242 i32.xor i32.const 15 i32.mul i32.const 5339 i32.xor i32.const 17 i32.mul i32.const 5436 i32.xor i32.const 19 i32.mul i32.const 5533 i32.xor i32.const 21 i32.mul i32.const 5630 i32.xor i32.const 23 i32.mul i32.const 5727 i32.xor i32.const 25 i32.mul i32.const 5824 i32.xor i32.const 27 i32.mul i32.const 5921 i32.xor i32.const 29 i32.mul i32.const 6018 i32.xor i32.const 31 i32.mul i32.const 6115 i32.xor i32.const 33 i32.mul i32.const 6212 i32.xor i32.const 35 i32.mul i32.const 6309 i32.xor i32.const 37 i32.mul i32.const 6406 i32.xor i32.const 39 i32.mul i32.const 6503 i32.xor i32.const 41 i32.mul i32.const 6600 i32.xor i32.const 43 i32.mul i32.const 6697 i32.xor i32.const 45 i32.mul i32.const 6794 i32.xor i32.const 47 i32.mul i32.const 6891 i32.xor i32.const 49 i32.mul i32.const 6988 i32.xor i32.const 51 i32.mul i32.const 7085 i32.xor i32.const 53 i32.mul i32.const 7182 i32.xor i32.const 55 i32.mul i32.const 7279 i32.xor i32.const 57 i32.mul i32.const 7376 i32.xor i32.const 59 i32.mul i32.const 7473 i32.xor i32.const 61 i32.mul i32.const 7570 i32.xor i32.const 63 i32.mul i32.const 7667 i32.xor i32.const 65 i32.mul i32.const 7764 i32.xor i32.const 67 i32.mul i32.const 7861 i32.xor i32.const 69 i32.mul i32.const 7958 i32.xor i32.const 71 i32.mul i32.const 8055 i32.xor i32.const 73 i32.mul i32.const 8152 i32.xor i32.const 75 i32.mul i32.const 8249 i32.xor i32.const 77 i32.mul i32.const 8346 i32.xor i32.const 79 i32.mul i32.const 8443 i32.xor i32.const 81 i32.mul else local.get 1 i32.const 1 i32.add end)
  (func (export "far_if_lt") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.lt_s if (result i32) local.get 1 i32.const 4660 i32.xor i32.const 3 i32.mul i32.const 4757 i32.xor i32.const 5 i32.mul i32.const 4854 i32.xor i32.const 7 i32.mul i32.const 4951 i32.xor i32.const 9 i32.mul i32.const 5048 i32.xor i32.const 11 i32.mul i32.const 5145 i32.xor i32.const 13 i32.mul i32.const 5242 i32.xor i32.const 15 i32.mul i32.const 5339 i32.xor i32.const 17 i32.mul i32.const 5436 i32.xor i32.const 19 i32.mul i32.const 5533 i32.xor i32.const 21 i32.mul i32.const 5630 i32.xor i32.const 23 i32.mul i32.const 5727 i32.xor i32.const 25 i32.mul i32.const 5824 i32.xor i32.const 27 i32.mul i32.const 5921 i32.xor i32.const 29 i32.mul i32.const 6018 i32.xor i32.const 31 i32.mul i32.const 6115 i32.xor i32.const 33 i32.mul i32.const 6212 i32.xor i32.const 35 i32.mul i32.const 6309 i32.xor i32.const 37 i32.mul i32.const 6406 i32.xor i32.const 39 i32.mul i32.const 6503 i32.xor i32.const 41 i32.mul i32.const 6600 i32.xor i32.const 43 i32.mul i32.const 6697 i32.xor i32.const 45 i32.mul i32.const 6794 i32.xor i32.const 47 i32.mul i32.const 6891 i32.xor i32.const 49 i32.mul i32.const 6988 i32.xor i32.const 51 i32.mul i32.const 7085 i32.xor i32.const 53 i32.mul i32.const 7182 i32.xor i32.const 55 i32.mul i32.const 7279 i32.xor i32.const 57 i32.mul i32.const 7376 i32.xor i32.const 59 i32.mul i32.const 7473 i32.xor i32.const 61 i32.mul i32.const 7570 i32.xor i32.const 63 i32.mul i32.const 7667 i32.xor i32.const 65 i32.mul i32.const 7764 i32.xor i32.const 67 i32.mul i32.const 7861 i32.xor i32.const 69 i32.mul i32.const 7958 i32.xor i32.const 71 i32.mul i32.const 8055 i32.xor i32.const 73 i32.mul i32.const 8152 i32.xor i32.const 75 i32.mul i32.const 8249 i32.xor i32.const 77 i32.mul i32.const 8346 i32.xor i32.const 79 i32.mul i32.const 8443 i32.xor i32.const 81 i32.mul else local.get 0 end)
  (func (export "far_loop") (param i32 i32) (result i32) (local i32)
    local.get 0 i32.const 7 i32.and i32.const 1 i32.add local.set 2
    loop
      local.get 1 i32.const 4660 i32.xor i32.const 3 i32.mul i32.const 4757 i32.xor i32.const 5 i32.mul i32.const 4854 i32.xor i32.const 7 i32.mul i32.const 4951 i32.xor i32.const 9 i32.mul i32.const 5048 i32.xor i32.const 11 i32.mul i32.const 5145 i32.xor i32.const 13 i32.mul i32.const 5242 i32.xor i32.const 15 i32.mul i32.const 5339 i32.xor i32.const 17 i32.mul i32.const 5436 i32.xor i32.const 19 i32.mul i32.const 5533 i32.xor i32.const 21 i32.mul i32.const 5630 i32.xor i32.const 23 i32.mul i32.const 5727 i32.xor i32.const 25 i32.mul i32.const 5824 i32.xor i32.const 27 i32.mul i32.const 5921 i32.xor i32.const 29 i32.mul i32.const 6018 i32.xor i32.const 31 i32.mul i32.const 6115 i32.xor i32.const 33 i32.mul i32.const 6212 i32.xor i32.const 35 i32.mul i32.const 6309 i32.xor i32.const 37 i32.mul i32.const 6406 i32.xor i32.const 39 i32.mul i32.const 6503 i32.xor i32.const 41 i32.mul i32.const 6600 i32.xor i32.const 43 i32.mul i32.const 6697 i32.xor i32.const 45 i32.mul i32.const 6794 i32.xor i32.const 47 i32.mul i32.const 6891 i32.xor i32.const 49 i32.mul i32.const 6988 i32.xor i32.const 51 i32.mul i32.const 7085 i32.xor i32.const 53 i32.mul i32.const 7182 i32.xor i32.const 55 i32.mul i32.const 7279 i32.xor i32.const 57 i32.mul i32.const 7376 i32.xor i32.const 59 i32.mul i32.const 7473 i32.xor i32.const 61 i32.mul i32.const 7570 i32.xor i32.const 63 i32.mul i32.const 7667 i32.xor i32.const 65 i32.mul i32.const 7764 i32.xor i32.const 67 i32.mul i32.const 7861 i32.xor i32.const 69 i32.mul i32.const 7958 i32.xor i32.const 71 i32.mul i32.const 8055 i32.xor i32.const 73 i32.mul i32.const 8152 i32.xor i32.const 75 i32.mul i32.const 8249 i32.xor i32.const 77 i32.mul i32.const 8346 i32.xor i32.const 79 i32.mul i32.const 8443 i32.xor i32.const 81 i32.mul local.set 1
      local.get 2 i32.const 1 i32.sub local.tee 2
      br_if 0
    end
    local.get 1)
  ;; Reviewer fuzz functions (gen15.py, profile shift, seeds 7000 / 7004):
  ;; the commutative rule with rd == rm, and shift-by-register with
  ;; rd == rm != rn (the amount kept in R7).
  (func (export "fz7000_f6") (param i32 i32) (result i32) (local i32) (block $L1 (if (i32.rotl (local.get 0) (local.get 2)) (then (local.set 1 (i32.rotr (i32.shr_u (local.get 1) (local.get 0)) (i32.shr_s (i32.const 692157298) (local.get 2)))) (local.set 2 (local.get 2)) (local.set 0 (local.get 0))) (else )) (br_if $L1 (local.get 0)) (local.set 0 (local.get 1)) (local.set 1 (local.get 1))) (local.set 0 (local.get 0)) (i32.xor (i32.add (i32.add (i32.shr_s (local.tee 2 (local.get 0)) (i32.shl (local.get 2) (local.get 1))) (local.get 2)) (local.get 1)) (local.get 0)))
  (func (export "fz7004_f3") (param i32) (result i32)  (local.set 0 (i32.rotr (i32.shr_u (local.tee 0 (local.get 0)) (i32.shr_s (local.get 0) (local.get 0))) (i32.rotl (i32.shr_u (local.get 0) (i32.const -5)) (i32.shl (local.get 0) (local.get 0))))) (local.set 0 (local.get 0)) (i32.add (i32.rotr (i32.rotl (local.get 0) (local.tee 0 (local.get 0))) (i32.rotr (local.get 0) (i32.rotl (local.get 0) (i32.const 74)))) (local.get 0)))
  (func (export "fz7004_f4") (param i32 i32 i32 i32) (result i32) (local i32 i32 i32) (local.set 1 (i32.rotl (i32.rotl (local.get 2) (local.get 0)) (i32.shr_u (local.get 2) (local.get 5)))) (local.set 2 (local.get 5)) (i32.rotr (i32.rotr (i32.shl (local.get 4) (local.get 4)) (if (result i32) (local.get 3) (then (i32.const -129)) (else (i32.const 1020)))) (select (i32.rotl (local.get 2) (local.get 6)) (select (local.get 3) (i32.const 65536) (local.get 4)) (i32.const -6145))))
  (func (export "fz7004_f5") (param i32 i32) (result i32) (local i32 i32 i32 i32 i32) (nop) (if (i32.rotr (local.get 4) (local.get 3)) (then (local.set 0 (i32.rotr (i32.shr_s (i32.const 7405568) (local.get 1)) (i32.rotl (local.get 4) (local.get 3))))) (else )) (i32.xor (i32.shr_u (i32.rotr (select (local.get 5) (local.get 0) (local.get 3)) (local.tee 2 (local.get 3))) (i32.const 4096)) (local.get 5)))
  ;; #1754: `select` wrote a parameter's home register while that parameter
  ;; was still on the operand stack. Pinned wrong here by RQ-91-M0I32 (75 and
  ;; 150 of 216 vectors); fixed in the direct selector by v0.92 batch 1, and
  ;; re-measured on that fix at 0 of 216 each, so both are ordinary accepted
  ;; probes now and every vector is required to agree.
  (func (export "s1754_b1") (param i32 i32 i32) (result i32) (i32.gt_s (local.get 0) (select (local.get 2) (local.get 0) (local.get 1))))
  (func (export "s1754_b1b") (param i32 i32 i32) (result i32) (i32.add (local.get 0) (select (local.get 2) (local.get 0) (local.get 1))))
  (func (export "fz7004_f7") (param i32) (result i32) (local i32 i32 i32) (local.set 2 (if (result i32) (i32.const -256) (then (local.get 3)) (else (local.get 0)))) (if (i32.shr_u (i32.rotl (local.get 2) (local.get 0)) (i32.rotr (local.get 1) (local.get 1))) (then (local.set 0 (i32.const 16777215)) (local.set 0 (local.get 0)) (local.set 1 (local.get 3))) (else (local.set 2 (local.get 3)))) (i32.shr_s (i32.shl (i32.shl (local.get 0) (i32.const 147)) (i32.rotr (local.get 2) (local.get 0))) (i32.const 1024)))
)
"#;

/// Shapes this lane leaves to later lanes. Compiled only for the decline pin.
const DECLINE_WAT: &str = r#"
(module
  (import "env" "ext" (func $ext (param i32) (result i32)))
  (memory 1)
  (global $g (mut i32) (i32.const 3))
  (func (export "d_div_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.div_u)
  (func (export "d_rem_s") (param i32 i32) (result i32) local.get 0 local.get 1 i32.rem_s)
  (func (export "d_clz") (param i32) (result i32) local.get 0 i32.clz)
  (func (export "d_ctz") (param i32) (result i32) local.get 0 i32.ctz)
  (func (export "d_popcnt") (param i32) (result i32) local.get 0 i32.popcnt)
  (func (export "d_i64_add") (param i64 i64) (result i64) local.get 0 local.get 1 i64.add)
  (func (export "d_i64_lt_s") (param i64 i64) (result i32) local.get 0 local.get 1 i64.lt_s)
  (func (export "d_load") (param i32) (result i32) local.get 0 i32.load)
  (func (export "d_store") (param i32 i32) local.get 0 local.get 1 i32.store)
  (func (export "d_global_get") (result i32) global.get $g)
  (func (export "d_memory_size") (result i32) memory.size)
  (func (export "d_params5") (param i32 i32 i32 i32 i32) (result i32)
    local.get 0 local.get 4 i32.add)
  ;; cold review 15 F1: shapes only the exhaustion-recovery rungs select
  ;; (repro/r1.wat .. r4.wat, the spill rung; gen15 pressure 7018 f4, pool-grow).
  ;; Each returned a wrong value on ARMv6-M before the rungs were declined.
  (func (export "d_rung_r1") (param i32 i32 i32 i32) (result i32) (local i32 i32 i32 i32 i32) (if (i32.le_u (i32.const 1) (select (i32.extend16_s (local.get 4)) (i32.const 128) (i32.const 31))) (then (return (local.get 2)))) (i32.add (i32.eq (local.get 0) (local.get 1)) (local.get 3)))
  (func (export "d_rung_r2") (param i32 i32) (result i32) (local i32 i32 i32 i32 i32) (if (select (local.get 5) (i32.const 1738883442) (select (i32.const 1738883442) (i32.mul (local.get 0) (if (result i32) (local.get 0) (then (local.get 3)) (else (local.get 4)))) (if (result i32) (local.get 0) (then (local.get 1)) (else (local.get 6))))) (then (return (local.get 4)))) (local.get 0))
  (func (export "d_rung_r3") (param i32 i32) (result i32) (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32) (local.set 6 (i32.le_u (i32.const 0) (i32.le_s (i32.const 0) (i32.mul (local.get 7) (i32.ge_u (local.get 8) (if (result i32) (local.get 0) (then (i32.const 0)) (else (i32.const -2147483648)))))))) (i32.sub (select (local.get 0) (local.get 1) (i32.const 257)) (local.get 6)))
  (func (export "d_rung_r4") (param i32 i32 i32 i32) (result i32) (local i32 i32 i32 i32 i32) (local.set 3 (i32.rotr (i32.const 1) (select (i32.rotl (local.get 7) (local.get 2)) (i32.const 219) (i32.const 51)))) (i32.xor (i32.xor (i32.sub (local.get 2) (local.get 1)) (local.get 3)) (local.get 0)))
  (func (export "d_rung_poolgrow") (param i32 i32 i32 i32) (result i32) (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32) (if (i32.shr_u (local.get 13) (i32.le_u (i32.const 297795584) (i32.lt_s (i32.const -2147483648) (i32.const 16711935)))) (then (block $L1 (local.set 6 (i32.xor (select (local.get 2) (local.get 4) (local.get 11)) (i32.add (i32.rotl (local.get 1) (i32.gt_u (local.get 13) (i32.shr_u (i32.const 305419896) (local.get 12)))) (i32.or (local.get 3) (i32.shr_s (i32.const 1000) (i32.const 1000)))))) (local.set 11 (i32.ge_u (local.get 10) (i32.mul (select (local.get 11) (local.get 5) (local.get 10)) (i32.rotl (i32.sub (i32.const -945194356) (i32.le_s (i32.eqz (local.get 6)) (i32.and (local.get 1) (i32.add (local.get 12) (i32.xor (i32.rotl (local.get 5) (i32.shr_s (local.get 5) (i32.lt_s (local.get 10) (i32.shr_s (i32.rotr (local.get 12) (i32.and (local.get 3) (i32.lt_s (local.get 0) (i32.rotl (i32.const -129) (i32.rotl (local.get 3) (i32.ge_u (local.get 8) (local.get 7))))))) (i32.mul (local.get 8) (i32.xor (local.get 4) (local.get 11))))))) (local.get 0)))))) (i32.mul (i32.const 283) (local.get 8)))))) (br_if $L1 (i32.extend8_s (if (result i32) (local.get 12) (then (local.get 1)) (else (local.get 5))))) (local.set 3 (local.get 8)) (local.set 6 (local.tee 13 (i32.le_u (i32.ge_u (local.get 12) (local.get 4)) (i32.or (local.get 3) (i32.shr_u (local.get 11) (i32.sub (local.get 8) (i32.eq (i32.const -65536) (local.get 0)))))))))) (else (block $L2  (br_if $L2 (select (select (local.get 5) (i32.const -1073709057) (local.get 12)) (local.get 7) (local.get 9))) (local.set 3 (local.get 13)) (local.set 9 (i32.const -199229441))))) (local.set 12 (local.get 3)) (local.set 9 (local.get 2)) (local.set 2 (local.get 6)) (i32.add (i32.sub (i32.sub (i32.xor (i32.sub (i32.add (i32.xor (i32.add (i32.xor (i32.add (i32.add (local.get 13) (local.get 2)) (local.get 11)) (local.get 5)) (local.get 8)) (local.get 0)) (local.get 12)) (local.get 10)) (local.get 1)) (local.get 7)) (local.get 3)) (local.get 4)))
  ;; F3: the scratch R7 is live where a rule needs it (gen15 shift 7005 f6).
  (func (export "d_scratch_live") (param i32 i32 i32 i32) (result i32) (local i32 i32 i32 i32) (local.set 5 (if (result i32) (local.get 3) (then (local.get 6)) (else (i32.const -1)))) (local.set 3 (if (result i32) (i32.rotr (block $L1 (result i32) (drop (br_if $L1 (local.get 4) (i32.const 1020))) (local.get 3)) (i32.rotr (local.get 4) (local.get 6))) (then (i32.const 71785337)) (else (local.get 7)))) (i32.add (i32.sub (i32.xor (i32.xor (i32.add (i32.add (i32.xor (i32.shl (i32.rotl (i32.shl (local.get 2) (local.get 3)) (i32.shr_s (local.get 4) (i32.const 65280))) (i32.rotr (block $L2 (result i32) (drop (br_if $L2 (local.get 0) (i32.const -1615162075))) (local.get 4)) (local.get 3))) (local.get 0)) (local.get 4)) (local.get 2)) (local.get 3)) (local.get 5)) (local.get 7)) (local.get 1)))
)
"#;

/// The exports of [`PROBES_WAT`] that compile for cortex-m0 / cortex-m0plus.
/// EXACT both ways: a probe moving in either direction reds.
const ACCEPTED: &[&str] = &[
    "c_0",
    "c_42",
    "c_255",
    "c_256",
    "c_ffff",
    "c_10000",
    "c_big",
    "c_neg1",
    "c_neg256",
    "c_min",
    "c_max",
    "c_dead",
    "c_c0007fff",
    "add_1",
    "add_7",
    "add_8",
    "add_200",
    "add_255",
    "add_256",
    "add_1000",
    "add_neg1",
    "add_neg300",
    "add_big",
    "sub_5",
    "sub_300",
    "rsub_300",
    "add",
    "sub",
    "sub_rev",
    "mul",
    "mul_10",
    "and",
    "or",
    "xor",
    "and_ff",
    "and_ffff",
    "and_7fff",
    "or_c0000000",
    "xor_neg1",
    "and_or_xor",
    "shl",
    "shr_s",
    "shr_u",
    "rotl",
    "rotr",
    "shl_1",
    "shl_31",
    "shl_32",
    "shr_u_1",
    "shr_u_31",
    "shr_s_1",
    "shr_s_31",
    "rotl_3",
    "rotr_7",
    "ext8",
    "ext16",
    "eqz",
    "eq",
    "ne",
    "lt_s",
    "lt_u",
    "gt_s",
    "gt_u",
    "le_s",
    "le_u",
    "ge_s",
    "ge_u",
    "lt_s_neg5",
    "gt_u_1000",
    "eq_big",
    "eq_neg1",
    "select3",
    "select_max",
    "select_const",
    "if_else",
    "if_void",
    "nested_if",
    "block_br_if",
    "loop_count",
    "loop_sum",
    "br_table",
    "br_table_shift",
    "early_return",
    "trap_if",
    "nop_drop",
    "local_tee",
    "many_locals",
    "sum4",
    "void_fn",
    "wdg_lock",
    "wdg_is_running",
    "i64_ident",
    "i64_and",
    "i64_or",
    "i64_xor",
    "i64_extend_u",
    "far_if",
    "far_if_lt",
    "far_loop",
    "fz7000_f6",
    "fz7004_f3",
    "fz7004_f4",
    "fz7004_f5",
    "s1754_b1",
    "s1754_b1b",
    "fz7004_f7",
];

/// The exports of [`DECLINE_WAT`] that must decline with the ARMv6-M
/// diagnostic. EXACT both ways.
const DECLINED: &[&str] = &[
    "d_div_u",
    "d_rem_s",
    "d_clz",
    "d_ctz",
    "d_popcnt",
    "d_i64_add",
    "d_i64_lt_s",
    "d_load",
    "d_store",
    "d_global_get",
    "d_memory_size",
    "d_params5",
    "d_rung_r1",
    "d_rung_r2",
    "d_rung_r3",
    "d_rung_r4",
    "d_rung_poolgrow",
    "d_scratch_live",
];

/// Declines whose diagnostic must name a specific cause, not only ARMv6-M.
const DECLINE_CAUSE: &[(&str, &str)] = &[
    ("d_rung_r1", "`spill` register-pressure recovery rung"),
    ("d_rung_r2", "`spill` register-pressure recovery rung"),
    ("d_rung_r3", "`spill` register-pressure recovery rung"),
    ("d_rung_r4", "`spill` register-pressure recovery rung"),
    (
        "d_rung_poolgrow",
        "`pool-grow` register-pressure recovery rung",
    ),
    ("d_scratch_live", "R7 is live there"),
    ("d_params5", "incoming stack argument"),
];

/// Integer vectors: the kiln oracle's twelve plus the signed and carry edges
/// of the compares (INT_MIN+1, INT_MAX-1, -2, 255, 256, 0x3F, 0x21, 2^30, 3 * 2^30).
const VECTORS: &[u32] = &[
    0,
    1,
    2,
    7,
    31,
    32,
    0x7F,
    0x8000,
    0x7FFF_FFFF,
    0x8000_0000,
    0xFFFF_FFFF,
    0xDEAD_BEEF,
    0x8000_0001,
    0x7FFF_FFFE,
    0xFFFF_FFFE,
    0xFF,
    0x100,
    0x3F,
    0x21,
    0x4000_0000,
    0xC000_0000,
];

const TARGETS: &[&str] = &["cortex-m0", "cortex-m0plus"];

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("synth-oracle-m0i32-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn compile_wat(wat_src: &str, flags: &[&str], tag: &str) -> (Option<CompiledObject>, String) {
    let dir = scratch();
    let input = dir.join(format!("{tag}.wasm"));
    std::fs::write(&input, wat::parse_str(wat_src).expect("WAT parses")).unwrap();
    let out = dir.join(format!("{tag}.o"));
    let run = compile(&input, flags, &out).expect("synth runs");
    (run.object, run.stderr)
}

fn v6m_flags(target: &str) -> Vec<&str> {
    vec![
        "--target",
        target,
        "--relocatable",
        "--all-exports",
        "--allow-skipped-exports",
    ]
}

fn compile_probes(target: &str) -> CompiledObject {
    let (obj, stderr) = compile_wat(PROBES_WAT, &v6m_flags(target), &format!("probes-{target}"));
    obj.unwrap_or_else(|| panic!("{target}: no object: {stderr}"))
}

fn exports(wat_src: &str) -> Vec<String> {
    let w = wat::parse_str(wat_src).unwrap();
    let mut v = Vec::new();
    for p in wasmparser::Parser::new(0).parse_all(&w) {
        if let Ok(wasmparser::Payload::ExportSection(s)) = p {
            for e in s {
                let e = e.unwrap();
                if e.kind == wasmparser::ExternalKind::Func {
                    v.push(e.name.to_string());
                }
            }
        }
    }
    v
}

// ---------------------------------------------------------------- gates --

#[test]
fn accepted_and_declined_sets_are_pinned() {
    let all = exports(PROBES_WAT);
    for target in TARGETS {
        let obj = compile_probes(target);
        let got: BTreeSet<&str> = all
            .iter()
            .filter(|e| obj.func(e).is_some())
            .map(|s| s.as_str())
            .collect();
        let want: BTreeSet<&str> = ACCEPTED.iter().copied().collect();
        assert_eq!(
            got,
            want,
            "{target}: accepted set moved (gained {:?}, lost {:?})",
            got.difference(&want).collect::<Vec<_>>(),
            want.difference(&got).collect::<Vec<_>>()
        );
        let (dobj, stderr) = compile_wat(
            DECLINE_WAT,
            &v6m_flags(target),
            &format!("declines-{target}"),
        );
        let dall = exports(DECLINE_WAT);
        let declined: BTreeSet<&str> = dall
            .iter()
            .filter(|e| dobj.as_ref().is_none_or(|o| o.func(e).is_none()))
            .map(|s| s.as_str())
            .collect();
        let want: BTreeSet<&str> = DECLINED.iter().copied().collect();
        assert_eq!(declined, want, "{target}: declined set moved");
        for d in &declined {
            let line = stderr
                .lines()
                .find(|l| l.contains(&format!("skipping function '{d}'")))
                .unwrap_or_else(|| panic!("{target}: no skip diagnostic for {d}:\n{stderr}"));
            assert!(
                line.contains("ARMv6-M"),
                "{target}: {d} declined without the ARMv6-M diagnostic: {line}"
            );
            if let Some((_, cause)) = DECLINE_CAUSE.iter().find(|(n, _)| n == d) {
                assert!(
                    line.contains(cause),
                    "{target}: {d} declined, but not for `{cause}`: {line}"
                );
            }
        }
    }
    eprintln!(
        "ORACLE armv6m-i32: {} of {} probes accepted, {} of {} decline probes declined, on {} targets",
        ACCEPTED.len(),
        all.len(),
        DECLINED.len(),
        exports(DECLINE_WAT).len(),
        TARGETS.len()
    );
}

#[test]
fn accepted_code_decodes_as_armv6m() {
    let table = legal16_table();
    let m0 = compile_probes("cortex-m0");
    let m0p = compile_probes("cortex-m0plus");
    assert_eq!(
        m0.text, m0p.text,
        "cortex-m0plus .text differs from cortex-m0"
    );
    let mut halfwords = 0usize;
    for p in ACCEPTED {
        let f = m0.func(p).unwrap_or_else(|| panic!("{p} missing"));
        assert!(f.thumb, "{p}: no Thumb bit");
        let b = m0.function_bytes(p).unwrap();
        assert!(!b.is_empty(), "{p}: empty");
        let bad = v6m_violations(b, &table);
        assert!(bad.is_empty(), "{p}: not ARMv6-M: {bad:?}");
        halfwords += b.len() / 2;
    }
    // The whole .text too, so code between symbols is covered.
    let bad = v6m_violations(&m0.text, &table);
    assert!(bad.is_empty(), ".text: {bad:?}");
    eprintln!(
        "decode: {halfwords} halfwords in {} functions, all ARMv6-M",
        ACCEPTED.len()
    );
}

fn vectors_for(arity: usize) -> Vec<Vec<WasmValue>> {
    let v = |x: u32| WasmValue::I32(x);
    match arity {
        0 => vec![vec![]],
        1 => VECTORS.iter().map(|&a| vec![v(a)]).collect(),
        2 => VECTORS
            .iter()
            .flat_map(|&a| VECTORS.iter().map(move |&b| vec![v(a), v(b)]))
            .collect(),
        3 => {
            let s = [0u32, 1, 0x8000_0000, 0xFFFF_FFFF, 7, 0xDEAD_BEEF];
            let mut out = Vec::new();
            for &a in &s {
                for &b in &s {
                    for &c in &s {
                        out.push(vec![v(a), v(b), v(c)]);
                    }
                }
            }
            out
        }
        4 => {
            let s = [0u32, 1, 0x8000_0000, 0xFFFF_FFFF, 0xDEAD_BEEF];
            let mut out = Vec::new();
            for &a in &s {
                for &b in &s {
                    for &c in &s {
                        for &d in &s {
                            out.push(vec![v(a), v(b), v(c), v(d)]);
                        }
                    }
                }
            }
            out
        }
        n => panic!("no vectors for arity {n}"),
    }
}

/// i64 params take the i32 vectors pairwise (low, high).
fn args_for(params: &[ValType]) -> Vec<Vec<WasmValue>> {
    if params.iter().all(|t| *t == ValType::I32) {
        return vectors_for(params.len());
    }
    let wide: Vec<u64> = VECTORS
        .iter()
        .step_by(2)
        .flat_map(|&lo| {
            VECTORS
                .iter()
                .step_by(3)
                .map(move |&hi| (u64::from(hi) << 32) | u64::from(lo))
        })
        .collect();
    match params {
        [ValType::I64] => wide.iter().map(|&x| vec![WasmValue::I64(x)]).collect(),
        [ValType::I64, ValType::I64] => wide
            .iter()
            .step_by(4)
            .flat_map(|&a| {
                wide.iter()
                    .step_by(5)
                    .map(move |&b| vec![WasmValue::I64(a), WasmValue::I64(b)])
            })
            .collect(),
        other => panic!("no vectors for {other:?}"),
    }
}

/// Every probe x vector, in probe order. The probes are spread over a few
/// threads (each case builds its own engines; the harness is concurrency-safe,
/// see the kiln oracle's stress test), and the cases are returned in order.
fn sweep(wasm: &[u8], obj: &CompiledObject, probes: &[&str]) -> Vec<Case> {
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get().min(8));
    let chunk = probes.len().div_ceil(threads).max(1);
    std::thread::scope(|sc| {
        let handles: Vec<_> = probes
            .chunks(chunk)
            .map(|ps| {
                sc.spawn(move || {
                    let cfg = EmuConfig::new(Cpu::CortexM0);
                    let mut cases = Vec::new();
                    for p in ps {
                        let sig = export_signature(wasm, p).unwrap();
                        for args in args_for(&sig.params) {
                            let c = run_case(wasm, obj, p, &args, FUEL, &Imports::new(), &cfg)
                                .unwrap_or_else(|e| panic!("{p}{args:?}: harness error {e:?}"));
                            cases.push(c);
                        }
                    }
                    cases
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().expect("sweep thread"))
            .collect()
    })
}

#[test]
fn accepted_probes_agree_with_kiln_on_the_m0_model() {
    let w = wat::parse_str(PROBES_WAT).unwrap();
    let obj = compile_probes("cortex-m0");
    for p in ACCEPTED {
        assert_eq!(obj.relocs_in(p), 0, "{p} carries relocations");
    }
    let cases = sweep(&w, &obj, ACCEPTED);
    let bad: Vec<&Case> = cases.iter().filter(|c| !c.verdict.is_agree()).collect();
    for c in bad.iter().take(30) {
        eprintln!(
            "{}{:?}: {:?} (ref {:?}, emu {:?})",
            c.export, c.args, c.verdict, c.reference, c.emulator
        );
    }
    assert!(
        bad.is_empty(),
        "{} of {} cases disagree",
        bad.len(),
        cases.len()
    );
    let traps = cases
        .iter()
        .filter(|c| {
            matches!(c.reference, RefOutcome::Trap { .. })
                && matches!(c.emulator, EmuOutcome::Trap { .. })
        })
        .count();
    let values = cases
        .iter()
        .filter(|c| matches!(c.emulator, EmuOutcome::Values(ref v) if !v.is_empty()))
        .count();
    eprintln!(
        "ORACLE armv6m-i32: {} cases agree on the Cortex-M0 model, {values} value \
         comparisons, {traps} trap/trap",
        cases.len()
    );
    // EXACT literals: a shrunk probe set or vector list reds here.
    assert_eq!(cases.len(), 19412, "case count moved");
    assert_eq!(values, 19370, "value-comparison count moved");
    assert_eq!(traps, 21, "trap/trap count moved");
}

// --------------------------------------------------------------- potency --

#[test]
fn potency_decode_leg_sees_it_cbz_movw_and_r8() {
    let table = legal16_table();
    let obj = compile_probes("cortex-m0");
    let base = obj.function_bytes("lt_s").expect("lt_s").to_vec();
    assert!(v6m_violations(&base, &table).is_empty());
    for (what, plant) in [
        ("IT eq", vec![0x08u8, 0xBF]),
        ("CBZ r0", vec![0x00, 0xB1]),
        ("MOVW r0,#42", vec![0x40, 0xF2, 0x2A, 0x00]),
        ("mov r8, r0", vec![0x80, 0x46]),
        ("mov r12, r0", vec![0x84, 0x46]),
        ("ldr r0, [pc]", vec![0x00, 0x48]),
    ] {
        let mut b = base.clone();
        b[2..2 + plant.len()].copy_from_slice(&plant);
        let bad = v6m_violations(&b, &table);
        assert!(!bad.is_empty(), "planted {what} was not seen");
        eprintln!("planted {what}: {bad:?}");
    }
}

#[test]
fn potency_v7m_code_faults_on_the_m0_model() {
    // The same `and` probe compiled for cortex-m3 is `and.w`: illegal on the
    // M0 model (this is what makes the execution leg an ARMv6-M check), and
    // correct on the M3 model (control).
    let w = wat::parse_str(PROBES_WAT).unwrap();
    let (obj, e) = compile_wat(
        PROBES_WAT,
        &["--target", "cortex-m3", "--relocatable", "--all-exports"],
        "probes-m3",
    );
    let obj = obj.unwrap_or_else(|| panic!("cortex-m3: {e}"));
    let sig = export_signature(&w, "and").unwrap();
    let args = [WasmValue::I32(0xF0F0), WasmValue::I32(0xFF00)];
    let m0 = emulate::run(&obj, "and", &sig, &args, &EmuConfig::new(Cpu::CortexM0)).unwrap();
    assert!(
        matches!(m0.outcome, EmuOutcome::Illegal { .. }),
        "v7-M and.w on the M0 model: {:?}",
        m0.outcome
    );
    let m3 = emulate::run(&obj, "and", &sig, &args, &EmuConfig::new(Cpu::CortexM3)).unwrap();
    assert_eq!(m3.outcome, EmuOutcome::Values(vec![WasmValue::I32(0xF000)]));
}

#[test]
fn potency_planted_wrong_reference_reds() {
    // kiln runs `lt_s` as `le_s`: they differ exactly when a == b.
    let planted = PROBES_WAT.replacen(
        "local.get 0 local.get 1 i32.lt_s)",
        "local.get 0 local.get 1 i32.le_s)",
        1,
    );
    assert_ne!(planted, PROBES_WAT);
    let w = wat::parse_str(&planted).unwrap();
    let obj = compile_probes("cortex-m0");
    let cfg = EmuConfig::new(Cpu::CortexM0);
    let disagree = vectors_for(2)
        .iter()
        .filter(|a| {
            matches!(
                run_case(&w, &obj, "lt_s", a, FUEL, &Imports::new(), &cfg)
                    .unwrap()
                    .verdict,
                Verdict::Disagree(_)
            )
        })
        .count();
    assert_eq!(disagree, VECTORS.len(), "planted le_s-for-lt_s");
}
