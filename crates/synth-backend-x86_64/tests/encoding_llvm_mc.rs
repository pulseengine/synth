//! E1: every instruction FORM the x86-64 encoder can produce, byte-equal to
//! `llvm-mc --triple=x86_64 -show-encoding`. RQ-91-X86SKEL (#1741).
//!
//! The test enumerates the whole operand space of every form the selector can
//! emit (`movl r32, r32` and `addl r32, r32` over all 16×16 register pairs,
//! and `retq`: 513 encodings), prints each with the backend's AT&T printer,
//! feeds the text to `llvm-mc` in one batch, and requires the encoding LLVM
//! reports to equal the encoder's bytes, form by form. The expected bytes come
//! from LLVM's tables, never from a byte string written here.
//!
//! The form count is a FLOOR (REVIEW_2 X4): an enumeration that silently
//! shrank would let E1 pass over fewer forms, so fewer than 513 is a failure.
//!
//! WHERE llvm-mc COMES FROM: `$LLVM_MC`, else Homebrew's
//! `/opt/homebrew/opt/llvm/bin/llvm-mc`, else `llvm-mc` on `PATH`. When none
//! runs, the test SKIPS LOUDLY (prints why and passes) — unless
//! `SYNTH_REQUIRE_LLVM_MC=1`, which the `x86_64-oracle` workflow sets, so
//! there the absence is a failure, never a skip. The decode oracle
//! (`encoding_iced.rs`) needs no tool and always runs.

use std::io::Write as _;
use std::process::{Command, Stdio};

use synth_backend_x86_64::encoder::encode;
use synth_backend_x86_64::inst::{Inst, Reg};

const FORM_FLOOR: usize = 513;

fn forms() -> Vec<Inst> {
    let mut v = Vec::new();
    for &d in &Reg::ALL {
        for &s in &Reg::ALL {
            v.push(Inst::MovRR32 { dst: d, src: s });
            v.push(Inst::AddRR32 { dst: d, src: s });
        }
    }
    v.push(Inst::Ret);
    v
}

fn llvm_mc() -> Option<String> {
    let mut candidates = Vec::new();
    if let Some(p) = std::env::var_os("LLVM_MC") {
        candidates.push(p.to_string_lossy().into_owned());
    }
    candidates.push("/opt/homebrew/opt/llvm/bin/llvm-mc".into());
    candidates.push("llvm-mc".into());
    candidates.into_iter().find(|c| {
        Command::new(c)
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_ok_and(|s| s.success())
    })
}

/// `llvm-mc -show-encoding` over `lines`: one encoding per line, in order.
fn assemble(mc: &str, lines: &[String]) -> Vec<Vec<u8>> {
    let mut child = Command::new(mc)
        .args(["--triple=x86_64", "-show-encoding"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn llvm-mc");
    {
        let mut stdin = child.stdin.take().unwrap();
        for l in lines {
            writeln!(stdin, "{l}").unwrap();
        }
    }
    let out = child.wait_with_output().expect("llvm-mc output");
    assert!(
        out.status.success(),
        "llvm-mc failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8(out.stdout).unwrap();
    stdout
        .lines()
        .filter_map(|l| l.split_once("encoding: [").map(|(_, r)| r))
        .map(|r| {
            let inner = r.split(']').next().unwrap();
            inner
                .split(',')
                .map(|b| {
                    let b = b.trim().trim_start_matches("0x");
                    u8::from_str_radix(b, 16)
                        .unwrap_or_else(|_| panic!("llvm-mc printed a non-byte `{b}` (a fixup?)"))
                })
                .collect()
        })
        .collect()
}

fn mc_or_skip(test: &str) -> Option<String> {
    let mc = llvm_mc();
    if mc.is_none() {
        if std::env::var_os("SYNTH_REQUIRE_LLVM_MC").is_some() {
            panic!("{test}: SYNTH_REQUIRE_LLVM_MC is set and no llvm-mc runs");
        }
        eprintln!(
            "SKIPPED {test}: no llvm-mc found ($LLVM_MC, \
             /opt/homebrew/opt/llvm/bin/llvm-mc, PATH). E1 did NOT run; \
             the iced-x86 decode oracle (encoding_iced.rs) still did."
        );
    }
    mc
}

#[test]
fn every_encoder_form_is_byte_equal_to_llvm_mc_e1() {
    let Some(mc) = mc_or_skip("every_encoder_form_is_byte_equal_to_llvm_mc_e1") else {
        return;
    };
    let forms = forms();
    assert!(
        forms.len() >= FORM_FLOOR,
        "E1 enumerates {} forms, below the floor {FORM_FLOOR}",
        forms.len()
    );
    let text: Vec<String> = forms.iter().map(Inst::att).collect();
    let got = assemble(&mc, &text);
    assert_eq!(got.len(), forms.len(), "llvm-mc gave one encoding per line");
    let mut bad = Vec::new();
    for ((f, t), want) in forms.iter().zip(&text).zip(&got) {
        let ours = encode(f);
        if &ours != want {
            bad.push(format!("{t}: synth {ours:02x?} llvm-mc {want:02x?}"));
        }
    }
    assert!(
        bad.is_empty(),
        "{} of {} forms differ from llvm-mc:\n{}",
        bad.len(),
        forms.len(),
        bad.join("\n")
    );
    eprintln!("E1: {} forms byte-equal to {mc}", forms.len());
}

/// Potency: the same comparison over bytes with REX.B dropped must disagree on
/// EVERY form whose destination is r8–r15, and on no other.
#[test]
fn a_dropped_rex_b_disagrees_with_llvm_mc() {
    let Some(mc) = mc_or_skip("a_dropped_rex_b_disagrees_with_llvm_mc") else {
        return;
    };
    let forms = forms();
    let text: Vec<String> = forms.iter().map(Inst::att).collect();
    let got = assemble(&mc, &text);
    let mut mutated = 0;
    let mut caught = 0;
    for (f, want) in forms.iter().zip(&got) {
        let mut b = encode(f);
        let high_dst =
            matches!(f, Inst::MovRR32 { dst, .. } | Inst::AddRR32 { dst, .. } if dst.num() >= 8);
        if high_dst {
            b[0] &= !1;
            mutated += 1;
        }
        if &b != want {
            caught += 1;
            assert!(high_dst, "{f}: an unmutated form disagrees");
        }
    }
    assert_eq!(mutated, 2 * 8 * 16);
    assert_eq!(caught, mutated);
}
