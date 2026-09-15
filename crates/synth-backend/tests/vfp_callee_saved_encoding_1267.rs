//! RQ-67-VFPREACH (#1267): the AAPCS callee-saved VFP save/restore.
//!
//! WHY THESE OPS EXIST. synth has always allocated inside S0-S15 / D0-D7 —
//! `vfp_home: &[bool; 16]` in the selector — because the other half of the
//! register file is AAPCS CALLEE-saved and nothing could save it: `VPUSH` and
//! `VPOP` did not exist in the encoder at all. So
//! "VFP register file exhausted (S0..S15 all live)" fires with HALF the
//! hardware unused, on every FPU target synth supports (FPv4-SP-D16 on M4F and
//! FPv5-D16 on M7 both have D0-D15 = S0-S31). #1267 is a real user hitting
//! that on a flight-control tick: 21 of 22 functions lower, one declines.
//!
//! WHY THE EXPECTED BYTES ARE NOT HAND-DERIVED. They come from llvm-mc:
//!
//!   llvm-mc -triple=thumbv7em-none-eabi -mattr=+vfp4 -show-encoding
//!     vpush {d8-d15}   ->  [0x2d,0xed,0x10,0x8b]
//!     vpop  {d8-d15}   ->  [0xbd,0xec,0x10,0x8b]
//!     vpush {d8}       ->  [0x2d,0xed,0x02,0x8b]
//!
//! The third line is the control that confirms the size field rather than
//! assuming it: `imm8` is TWICE the double-register count (0x10 = 16 = 2 x 8,
//! 0x02 = 2 = 2 x 1), and the `8B` nibble selects the 64-bit form.
//!
//! WHY THIS TEST IS LOAD-BEARING AND NOT CEREMONY. `encode_thumb` ends in a
//! catch-all that returns `Ok(NOP)` for any unhandled op (#1272). Both of these
//! compiled clean BEFORE their arms existed and would have emitted a save that
//! saves nothing — silently, on the default target. An assertion on the exact
//! bytes is the only thing that distinguishes "encoded" from "swallowed".

use synth_backend::ArmEncoder;
use synth_core::target::FPUPrecision;
use synth_synthesis::ArmOp;

fn thumb() -> ArmEncoder {
    ArmEncoder::new_thumb2_with_fpu(Some(FPUPrecision::Double))
}

#[test]
fn vpush_callee_saved_matches_llvm_mc_1267() {
    let got = thumb()
        .encode(&ArmOp::VPushCalleeSavedVfp)
        .expect("VPUSH {d8-d15} must encode");
    assert_eq!(
        got,
        vec![0x2d, 0xed, 0x10, 0x8b],
        "VPUSH {{d8-d15}} must equal llvm-mc's encoding, not a NOP (#1272)"
    );
}

#[test]
fn vpop_callee_saved_matches_llvm_mc_1267() {
    let got = thumb()
        .encode(&ArmOp::VPopCalleeSavedVfp)
        .expect("VPOP {d8-d15} must encode");
    assert_eq!(
        got,
        vec![0xbd, 0xec, 0x10, 0x8b],
        "VPOP {{d8-d15}} must equal llvm-mc's encoding, not a NOP (#1272)"
    );
}

#[test]
fn neither_is_the_catch_all_nop_1267() {
    // The catch-all emits the 16-bit `NOP` 0xBF00 as two bytes. Both of these
    // are 32-bit VFP instructions, so a length of 2 — or those bytes — means
    // the arm was removed and the op is being swallowed again.
    for op in [ArmOp::VPushCalleeSavedVfp, ArmOp::VPopCalleeSavedVfp] {
        let got = thumb().encode(&op).expect("must encode");
        assert_eq!(got.len(), 4, "{op:?} must be a 32-bit instruction");
        assert_ne!(
            got,
            vec![0x00, 0xbf],
            "{op:?} fell through to the NOP catch-all"
        );
    }
}

#[test]
fn a32_refuses_loudly_rather_than_encoding_something_plausible_1267() {
    // #615's rule: expand or loud-reject, never a silent NOP. This lane's rung
    // is Thumb-2 only, so the A32 path must REFUSE rather than invent bytes.
    for op in [ArmOp::VPushCalleeSavedVfp, ArmOp::VPopCalleeSavedVfp] {
        let err = ArmEncoder::new_arm32().encode(&op);
        assert!(
            err.is_err(),
            "{op:?} must be refused on the A32 path, got {err:?}"
        );
    }
}
