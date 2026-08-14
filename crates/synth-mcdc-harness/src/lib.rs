//! RQ-57-MCDC (#912) — MC/DC row drivers for synth's OWN decision logic.
//!
//! # Why this crate exists
//!
//! #912 asked for MC/DC structural coverage and sat N/A for six releases on a
//! surface argument: `witness` measures MC/DC on a **Wasm** artifact, synth
//! **emits ARM/RV32/A64 machine code**, so "run witness on synth's output" is a
//! category error. That argument is correct about synth's *output* and wrong
//! about synth's *input*: the decisions that ship a miscompile are the ones in
//! synth's own Rust — the decline predicates, the guard-emission conditions,
//! the validator accept/reject tests. Those compile to Wasm perfectly well.
//!
//! So this crate is a thin **row driver**: it builds for `wasm32-wasip1`,
//! links the REAL synth crates, and calls the REAL `pub fn`s with inputs that
//! arrive through Wasm parameters (never constant-folded). `witness` then
//! reconstructs the MC/DC truth table and attributes every decision to synth's
//! own source line. Nothing here re-implements a predicate — a mirror would be
//! exactly the vacuous-gate class this measurement is meant to catch.
//!
//! # Why not the other two surfaces
//!
//! * **Native LLVM MC/DC via `-Zcoverage-options=mcdc`** — REMOVED from rustc
//!   in rust-lang/rust#144999 (merged 2025-08-08, Rust 1.91). Every installed
//!   nightly rejects the value; `condition` (what replaced it in the accepted
//!   set) emits zero MC/DC intrinsics and zero `mcdc_records`. Not a
//!   preference — the capability is gone from the compiler.
//! * **`witness` over the Wasm fixtures synth COMPILES** — measures the
//!   fixture, not synth. gale's run on a real dissolved module named its gap
//!   rows `core::fmt::Formatter::pad_integral`, `core::str::count::
//!   do_count_chars`, `<u64 as Display>::fmt`, `pad_integral::write_prefix`,
//!   `wit_bindgen::rt::cabi_realloc` — five stdlib/bindgen frames and zero
//!   synth functions. A surface whose gap rows cannot name a synth decision
//!   cannot notice a missing condition in one.
//!
//! # Reading the numbers
//!
//! The module-wide percentage is meaningless here: a `wasm32-wasip1` link
//! pulls in wasi-libc (`malloc.c`, `stpcpy.c`, …) and Rust `std`
//! (`panicking.rs`, `mod.rs`, …), which contribute hundreds of never-evaluated
//! conditions. `scripts/mcdc_gate.py` therefore scores ONLY synth's own source
//! files and reports per-file counts, not a ratio. See that script for the
//! declared floor.
//!
//! Every export takes its varying inputs as Wasm parameters and returns an
//! `i32` so `witness run --invoke-with-args` can drive one truth-table row per
//! invocation.

use synth_backend_riscv::alloc_validator::{RaFinalVerdict, validate_final_allocation_rv32};
use synth_backend_riscv::backend::RiscVBackend;
use synth_backend_riscv::register::Reg;
use synth_backend_riscv::riscv_op::RiscVOp;
use synth_core::backend::{Backend, CompileConfig, SafetyBounds};
use synth_core::static_data_addr::{
    DataSegment, ImageVerdict, PackedInit, RelocResolution, Verdict, resolve_owner,
    validate_reloc_resolutions_spanned, validate_served_image,
};
use synth_core::target::TargetSpec;
use synth_core::wasm_op::WasmOp;

// ════════════════════════════════════════════════════════════════════════
// Class 1 — VALIDATOR ACCEPT/REJECT: `synth_core::static_data_addr`
//   VCR-VER-003 (#777), the validator that hard-errors the #757 wrong-segment
//   miscompile. A missed condition here green-washes a silent miscompile.
// ════════════════════════════════════════════════════════════════════════

/// Two overlapping active segments at the same linear-memory offset — the #757
/// shape. `1` is declared later, so later-wins makes it the owner.
fn overlapping_segments() -> Vec<DataSegment> {
    vec![
        DataSegment {
            linmem_off: 0x100,
            bytes: vec![0x11, 0x22, 0x33, 0x44],
        },
        DataSegment {
            linmem_off: 0x100,
            bytes: vec![0xAA, 0xBB, 0xCC, 0xDD],
        },
    ]
}

/// Drives `static_data_addr::resolve_owner`'s membership decision
/// `c >= off && c < off + len` (the `.rposition()` / `.position()` tie-break
/// that IS the #757 fix). `c` arrives through a Wasm parameter, so the
/// comparison is evaluated at run time.
///
/// Rows: `c` below the segment (c0=F), inside it (c0=T,c1=T), above it
/// (c0=T,c1=F). `last_wins` selects which of the two search call sites runs.
///
/// `nseg` matters for the MEASUREMENT, not for the predicate: `witness` records
/// ONE truth-table row per invocation, so a decision evaluated once per
/// iteration of a loop collapses to whichever evaluation the row captures.
/// With `nseg == 1` the membership test runs EXACTLY ONCE per call, which is
/// what makes distinct condition vectors observable. `nseg == 2` is the #757
/// overlapping shape and is driven for behaviour, not for vectors.
#[unsafe(no_mangle)]
pub extern "C" fn sd_resolve_owner(c: i32, last_wins: i32, nseg: i32) -> i32 {
    let mut segs = overlapping_segments();
    if nseg <= 1 {
        segs.truncate(1);
    }
    match resolve_owner(&segs, c as u32, last_wins != 0) {
        Some(r) => (r.seg_index as i32) * 1000 + r.addend as i32,
        None => -1,
    }
}

/// Drives `validate_reloc_resolutions_spanned`'s span-tolerance decision
/// `j == 0 && seg.bytes.get(addend) != Some(&runtime_byte)` (phase 2 of #777:
/// the multi-byte access straddle).
///
/// `seg_index` picks the emitted owner K — `0` is the #757 miscompile (the
/// stale earlier segment), `1` is the correct later-wins owner. `addend`
/// walks the span. Together they reach both the `j == 0` short-circuit
/// (c0=F on every `j > 0` iteration) and both outcomes of the byte compare.
#[unsafe(no_mangle)]
pub extern "C" fn sd_validate_spanned(seg_index: i32, addend: i32) -> i32 {
    let segs = overlapping_segments();
    let packed_off = [0u32, 4u32];
    let blob: Vec<u8> = vec![0x11, 0x22, 0x33, 0x44, 0xAA, 0xBB, 0xCC, 0xDD];
    let packed = PackedInit {
        seg_packed_off: &packed_off,
        bytes: &blob,
    };
    let res = vec![RelocResolution {
        seg_index: seg_index as usize,
        addend: addend as u32,
        label: "row".to_string(),
    }];
    match validate_reloc_resolutions_spanned(&segs, &res, &packed) {
        Verdict::Consistent => 0,
        Verdict::Mismatch(m) => m.len() as i32,
    }
}

/// Drives `validate_served_image`'s beyond-image decision
/// `addr >= image.len() && owed != 0` — the #798 gate that caught the silent
/// initializer drop on the pre-#798 RV32 path.
///
/// `image_len` truncates the served blob (0 = "ships no initializer bytes at
/// all"); `trailing_zero` appends a runtime byte whose value IS zero past the
/// image, which is the only way to reach `c0=T, c1=F`.
#[unsafe(no_mangle)]
pub extern "C" fn sd_validate_served(image_len: i32, trailing_zero: i32) -> i32 {
    let mut segs = vec![DataSegment {
        linmem_off: 0,
        bytes: vec![0x01, 0x02, 0x03, 0x04],
    }];
    if trailing_zero != 0 {
        // A runtime-covered byte beyond the image whose owed value is 0.
        segs.push(DataSegment {
            linmem_off: 8,
            bytes: vec![0x00, 0x00],
        });
    }
    let full = [0x01u8, 0x02, 0x03, 0x04];
    let n = (image_len.max(0) as usize).min(full.len());
    match validate_served_image(&segs, &full[..n]) {
        ImageVerdict::Consistent => 0,
        ImageVerdict::Mismatch(m) => m.len() as i32,
    }
}

// ════════════════════════════════════════════════════════════════════════
// Class 2 — VALIDATOR ACCEPT/REJECT: RV32 register-allocation validator
//   VCR-RA-003 (#815). #871 shipped an unsaved-`ra` miscompile: a non-leaf
//   function returning into its own call site. The fix is literally a
//   CONDITION added to this validator's save-set predicate, which is exactly
//   what MC/DC is for.
// ════════════════════════════════════════════════════════════════════════

/// Build one RV32 instruction stream per `shape`, chosen so the whole set
/// covers every condition of the validator's compound decisions:
/// `sp_slot_store(ins) && (is_saved_by_pass(rs2) || rs2 == RA)`,
/// `op_dest(ins) && is_saved_by_pass(rd)`,
/// the epilogue reload guard `is_saved_by_pass(rd) || rd == RA`,
/// the segment walk `i < len && is_straight_line(instrs[i])`,
/// and `is_saved_by_pass`'s own `n == 9 || (18..=26).contains(&n)`.
fn ra_shape(shape: i32) -> Vec<RiscVOp> {
    let ret = RiscVOp::Jalr {
        rd: Reg::ZERO,
        rs1: Reg::RA,
        imm: 0,
    };
    match shape {
        // Leaf, writes only a temp: no save needed, no violation.
        // is_saved_by_pass(t0=5): c0=F, c1=F.
        0 => vec![
            RiscVOp::Addi {
                rd: Reg::T0,
                rs1: Reg::ZERO,
                imm: 1,
            },
            ret,
        ],
        // Saves + writes + restores s1 (reg 9): is_saved_by_pass c0=T.
        1 => vec![
            RiscVOp::Addi {
                rd: Reg::SP,
                rs1: Reg::SP,
                imm: -16,
            },
            RiscVOp::Sw {
                rs1: Reg::SP,
                rs2: Reg::S1,
                imm: 0,
            },
            RiscVOp::Addi {
                rd: Reg::S1,
                rs1: Reg::ZERO,
                imm: 7,
            },
            RiscVOp::Lw {
                rd: Reg::S1,
                rs1: Reg::SP,
                imm: 0,
            },
            RiscVOp::Addi {
                rd: Reg::SP,
                rs1: Reg::SP,
                imm: 16,
            },
            ret,
        ],
        // Writes s1 with NO save — the #490 callee-saved clobber.
        2 => vec![
            RiscVOp::Addi {
                rd: Reg::S1,
                rs1: Reg::ZERO,
                imm: 7,
            },
            ret,
        ],
        // Non-leaf with `ra` saved and restored — #871 green.
        // Exercises `rs2 == RA` (the `||` right arm) on both halves.
        3 => vec![
            RiscVOp::Addi {
                rd: Reg::SP,
                rs1: Reg::SP,
                imm: -16,
            },
            RiscVOp::Sw {
                rs1: Reg::SP,
                rs2: Reg::RA,
                imm: 12,
            },
            RiscVOp::Call {
                label: "func_1".to_string(),
            },
            RiscVOp::Lw {
                rd: Reg::RA,
                rs1: Reg::SP,
                imm: 12,
            },
            RiscVOp::Addi {
                rd: Reg::SP,
                rs1: Reg::SP,
                imm: 16,
            },
            ret,
        ],
        // Non-leaf that never saves `ra` — the #871 miscompile itself.
        4 => vec![
            RiscVOp::Call {
                label: "func_1".to_string(),
            },
            ret,
        ],
        // Frame store of a NON-callee-saved register (t0): the store-side
        // decision takes c0=T with both `||` arms false.
        5 => vec![
            RiscVOp::Sw {
                rs1: Reg::SP,
                rs2: Reg::T0,
                imm: 4,
            },
            ret,
        ],
        // Store whose base is NOT sp: `sp_slot_store` is None, so the
        // let-chain's first condition is false and the `||` never evaluates.
        6 => vec![
            RiscVOp::Sw {
                rs1: Reg::T0,
                rs2: Reg::S1,
                imm: 0,
            },
            RiscVOp::Addi {
                rd: Reg::SP,
                rs1: Reg::SP,
                imm: -16,
            },
            RiscVOp::Sw {
                rs1: Reg::SP,
                rs2: Reg::S1,
                imm: 0,
            },
            RiscVOp::Lw {
                rd: Reg::S1,
                rs1: Reg::SP,
                imm: 0,
            },
            ret,
        ],
        // Saves s2 (reg 18) — the range arm of `n == 9 || (18..=26)`.
        7 => vec![
            RiscVOp::Sw {
                rs1: Reg::SP,
                rs2: Reg::X18,
                imm: 0,
            },
            RiscVOp::Addi {
                rd: Reg::X18,
                rs1: Reg::ZERO,
                imm: 1,
            },
            RiscVOp::Lw {
                rd: Reg::X18,
                rs1: Reg::SP,
                imm: 0,
            },
            ret,
        ],
        // A barrier mid-stream: the straight-line segment walk terminates on
        // `is_straight_line == false` rather than on the length bound.
        8 => vec![
            RiscVOp::Addi {
                rd: Reg::T0,
                rs1: Reg::ZERO,
                imm: 1,
            },
            RiscVOp::Label {
                name: "L0".to_string(),
            },
            RiscVOp::Addi {
                rd: Reg::T0,
                rs1: Reg::ZERO,
                imm: 2,
            },
            ret,
        ],
        // Straight-line to the very end: the walk terminates on the LENGTH
        // bound (`i < instrs.len()` false) with no barrier — the other
        // unique-cause row for that decision.
        9 => vec![
            RiscVOp::Addi {
                rd: Reg::T0,
                rs1: Reg::ZERO,
                imm: 1,
            },
            RiscVOp::Addi {
                rd: Reg::T0,
                rs1: Reg::T0,
                imm: 2,
            },
        ],
        // Spill-slot shadowing: two stores to one slot with no intervening
        // reload, then a reload — the aliasing violation.
        10 => vec![
            RiscVOp::Sw {
                rs1: Reg::SP,
                rs2: Reg::T0,
                imm: 8,
            },
            RiscVOp::Sw {
                rs1: Reg::SP,
                rs2: Reg::X6,
                imm: 8,
            },
            RiscVOp::Lw {
                rd: Reg::T0,
                rs1: Reg::SP,
                imm: 8,
            },
            ret,
        ],
        // `is_ret` unique-cause rows: a `Jalr` that differs from `ret` in
        // EXACTLY ONE field. `is_ret` is `matches!(op, Jalr{rd: ZERO, rs1: RA,
        // imm: 0})`, which lowers to a 4-condition `br_if` chain — a shape
        // source-level MC/DC cannot see at all, and one where a single wrong
        // field silently reclassifies a terminator.
        11 => vec![RiscVOp::Jalr {
            rd: Reg::T0, // link register written — NOT a return
            rs1: Reg::RA,
            imm: 0,
        }],
        12 => vec![RiscVOp::Jalr {
            rd: Reg::ZERO,
            rs1: Reg::T0, // indirect through a temp — NOT a return
            imm: 0,
        }],
        13 => vec![RiscVOp::Jalr {
            rd: Reg::ZERO,
            rs1: Reg::RA,
            imm: 4, // offset return — NOT the canonical `ret`
        }],
        // `sp_slot_load` with a non-sp base: a linear-memory load, not a
        // frame reload. Pairs with the sp-relative loads above.
        14 => vec![
            RiscVOp::Lw {
                rd: Reg::T0,
                rs1: Reg::X8,
                imm: 0,
            },
            ret,
        ],
        // Every SEGMENT BARRIER `is_straight_line` knows about, so the match
        // arms that are otherwise DEAD are evaluated. A dead condition is a
        // condition the measurement cannot speak about at all.
        15 => vec![
            RiscVOp::Jal {
                rd: Reg::ZERO,
                label: "L0".to_string(),
            },
            RiscVOp::Ecall,
            RiscVOp::Ebreak,
            RiscVOp::Mret,
            RiscVOp::Wfi,
            RiscVOp::Fence,
            RiscVOp::Label {
                name: "L0".to_string(),
            },
            ret,
        ],
        // A saved register OUTSIDE the pass's save set on both sides of the
        // range (`n == 9 || (18..=26)`): s0 (8) below, s11 (27) above.
        16 => vec![
            RiscVOp::Sw {
                rs1: Reg::SP,
                rs2: Reg::X8,
                imm: 0,
            },
            RiscVOp::Sw {
                rs1: Reg::SP,
                rs2: Reg::X27,
                imm: 4,
            },
            RiscVOp::Addi {
                rd: Reg::X8,
                rs1: Reg::ZERO,
                imm: 1,
            },
            RiscVOp::Addi {
                rd: Reg::X27,
                rs1: Reg::ZERO,
                imm: 1,
            },
            ret,
        ],
        // Top of the save range (s10 = 26) plus a write, saved and restored.
        17 => vec![
            RiscVOp::Sw {
                rs1: Reg::SP,
                rs2: Reg::X26,
                imm: 0,
            },
            RiscVOp::Addi {
                rd: Reg::X26,
                rs1: Reg::ZERO,
                imm: 1,
            },
            RiscVOp::Lw {
                rd: Reg::X26,
                rs1: Reg::SP,
                imm: 0,
            },
            ret,
        ],
        // Saved but NEVER restored before `ret` — the epilogue half of the
        // callee-saved invariant (a different violation from shape 2).
        18 => vec![
            RiscVOp::Sw {
                rs1: Reg::SP,
                rs2: Reg::S1,
                imm: 0,
            },
            RiscVOp::Addi {
                rd: Reg::T0,
                rs1: Reg::ZERO,
                imm: 1,
            },
            ret,
        ],
        // `is_ret` is only reached from the epilogue scan, which runs ONLY when
        // the save set is non-empty. 19–21 therefore carry a real save and end
        // on a near-`ret` that differs in exactly ONE field, so the LAST
        // `is_ret` evaluation of the invocation carries the unique-cause
        // vector. (Shapes 11–13 reach the same variants through the store/def
        // scans instead.)
        19..=21 => {
            let near = match shape {
                19 => RiscVOp::Jalr {
                    rd: Reg::T0,
                    rs1: Reg::RA,
                    imm: 0,
                },
                20 => RiscVOp::Jalr {
                    rd: Reg::ZERO,
                    rs1: Reg::T0,
                    imm: 0,
                },
                _ => RiscVOp::Jalr {
                    rd: Reg::ZERO,
                    rs1: Reg::RA,
                    imm: 4,
                },
            };
            vec![
                RiscVOp::Sw {
                    rs1: Reg::SP,
                    rs2: Reg::S1,
                    imm: 0,
                },
                RiscVOp::Lw {
                    rd: Reg::S1,
                    rs1: Reg::SP,
                    imm: 0,
                },
                near,
            ]
        }
        // Empty stream.
        _ => vec![],
    }
}

/// Drives `validate_final_allocation_rv32` over one shape. Returns
/// `0` = Ok, `1` = Violation, `2` = NotAttempted.
#[unsafe(no_mangle)]
pub extern "C" fn ra_validate(shape: i32) -> i32 {
    match validate_final_allocation_rv32(&ra_shape(shape)) {
        RaFinalVerdict::Consistent => 0,
        RaFinalVerdict::Violation(_) => 1,
        RaFinalVerdict::NotAttempted { .. } => 2,
    }
}

// ════════════════════════════════════════════════════════════════════════
// Class 3 — GUARD EMISSION: the RV32 `--safety-bounds mask` size gate
//   The #953/#959 sentinel-vs-value class, three consecutive releases. The
//   shipped defect was a MISSING CONDITION in exactly this decision: `bytes
//   == 0` was exempt from the power-of-two gate, so `(memory 0)` emitted an
//   IDENTITY mask (0 - 1 = 0xFFFF_FFFF) and every access ran unmasked.
// ════════════════════════════════════════════════════════════════════════

/// Drives `synth_backend_riscv::backend::build_options`' bounds-mode gate
/// `mem_size == 0 || !mem_size.is_power_of_two()` through the public
/// `Backend::compile_function` entry point.
///
/// Rows: `bytes = 0` (c0=T — the #959 identity-mask case, must refuse),
/// `bytes = 65536` (c0=F, c1=F — accept), `bytes = 196608` (c0=F, c1=T — the
/// #651 non-power-of-two refusal).
/// `mode = 3` swaps in a Cortex-M target so `ensure_supported_target`'s
/// family/ISA conjunction is evaluated with its conditions flipped — otherwise
/// every row shares one vector and those conditions stay gap.
#[unsafe(no_mangle)]
pub extern "C" fn rv_bounds_gate(mode: i32, bytes: i32) -> i32 {
    let mut config = CompileConfig {
        target: if mode == 3 {
            TargetSpec::cortex_m4()
        } else {
            TargetSpec::riscv32imac()
        },
        ..Default::default()
    };
    config.safety_bounds = match mode {
        0 => SafetyBounds::None,
        1 => SafetyBounds::Software,
        _ => SafetyBounds::Mask,
    };
    config.linear_memory_bytes = bytes.max(0) as u32;
    let ops = [WasmOp::I32Const(1), WasmOp::End];
    match RiscVBackend::new().compile_function("f", &ops, &config) {
        Ok(_) => 0,
        Err(_) => 1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The row drivers must reach the outcomes their doc comments claim; a
    /// driver that silently returns the same verdict for every row would make
    /// the whole MC/DC run vacuous. Runs on the HOST (the wasm build is the
    /// measured artifact, this is the sanity gate).
    #[test]
    fn rows_reach_distinct_outcomes() {
        // resolve_owner: below / inside / above.
        assert_eq!(sd_resolve_owner(0x50, 1, 2), -1);
        assert_eq!(sd_resolve_owner(0x100, 1, 2), 1000); // later-wins owner = seg 1
        assert_eq!(sd_resolve_owner(0x100, 0, 2), 0); // first-match = seg 0 (#757)
        assert_eq!(sd_resolve_owner(0x200, 1, 2), -1);
        // Single-segment form: one membership evaluation per invocation.
        assert_eq!(sd_resolve_owner(0x102, 1, 1), 2);
        assert_eq!(sd_resolve_owner(0x104, 1, 1), -1);

        // spanned: correct owner is consistent, the #757 owner is not.
        assert_eq!(sd_validate_spanned(1, 0), 0);
        assert!(sd_validate_spanned(0, 0) > 0);

        // served image: full blob consistent, truncated blob drops bytes.
        assert_eq!(sd_validate_served(4, 0), 0);
        assert!(sd_validate_served(0, 0) > 0);
        assert_eq!(sd_validate_served(4, 1), 0);

        // allocation validator: green and violating shapes both reachable.
        assert_eq!(ra_validate(1), 0);
        assert_eq!(ra_validate(2), 1);
        // A `Call` puts the stream past the RV32 whole-function frontier, so a
        // clean non-leaf is `NotAttempted` — the straight-line invariants still
        // ran and held. An unsaved `ra` is still a hard Violation (#871).
        assert_eq!(ra_validate(3), 2);
        assert_eq!(ra_validate(4), 1, "#871: unsaved ra must be a violation");

        // bounds gate: 0 bytes refused, power-of-two accepted, other refused.
        assert_eq!(
            rv_bounds_gate(2, 0),
            1,
            "#959: (memory 0) + mask must refuse"
        );
        assert_eq!(rv_bounds_gate(2, 65536), 0);
        assert_eq!(rv_bounds_gate(2, 196608), 1, "#651: non-power-of-two");
        assert_eq!(rv_bounds_gate(3, 65536), 1, "non-RISC-V target must refuse");

        // Every added shape must be reachable and classified.
        for shape in 0..=21 {
            let v = ra_validate(shape);
            assert!((0..=2).contains(&v), "shape {shape} -> {v}");
        }
        assert_eq!(
            ra_validate(18),
            1,
            "saved but never restored is a violation"
        );
    }
}
