//! E1: every instruction FORM the x86-64 encoder can produce, byte-equal to
//! `llvm-mc --triple=x86_64`. RQ-91-X86SKEL, RQ-91-X86ALU, RQ-91-X86FRAME
//! (#1741).
//!
//! The test enumerates the whole operand space of every form (`forms/mod.rs`:
//! all 16 x 16 register pairs at both operand sizes, every condition, boundary
//! immediates, and from lane X3 every memory base at boundary displacements —
//! 24,308 encodings), prints each with the backend's AT&T printer, feeds the
//! text to `llvm-mc` in one batch, and requires the encoding LLVM reports to
//! equal the encoder's bytes, form by form. The expected bytes come from
//! LLVM's tables, never from a byte string written here.
//!
//! BRANCHES take a second route. `-show-encoding` prints a `jCC` with a FIXUP
//! in place of its displacement bytes, so the 80 branch forms are assembled
//! to an OBJECT (`-filetype=obj`) and `.text` is read back: the displacement
//! bytes are then LLVM's too. The object must carry no relocation.
//!
//! The form count is EXACT (REVIEW_2 X4): an enumeration that silently shrank
//! would let E1 pass over fewer forms.
//!
//! WHERE llvm-mc COMES FROM: `$LLVM_MC`, else Homebrew's
//! `/opt/homebrew/opt/llvm/bin/llvm-mc`, else `llvm-mc` on `PATH`. When none
//! runs, the test SKIPS LOUDLY (prints why and passes) — unless
//! `SYNTH_REQUIRE_LLVM_MC=1`, which the `x86_64-oracle` workflow sets, so
//! there the absence is a failure, never a skip. The decode oracle
//! (`encoding_iced.rs`) needs no tool and always runs.

use std::io::Write as _;
use std::process::{Command, Stdio};

use object::{Object as _, ObjectSection as _};

use synth_backend_x86_64::encoder::encode;
use synth_backend_x86_64::inst::Inst;

mod forms;
use forms::{FORM_COUNT, all_forms, is_branch};

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

/// `llvm-mc -filetype=obj` over `lines`: the bytes of `.text`, which must
/// carry no relocation (every branch target is a fixed distance away).
fn assemble_object(mc: &str, lines: &[String]) -> Vec<u8> {
    // A path of its OWN for every call. Three tests in this binary assemble
    // the branches, on three threads; with one shared name a thread could
    // delete or half-overwrite the object another was about to read (cold
    // review of f0277592, B1: 2 failures in 60 runs under load).
    static CALL: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let call = CALL.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let out = std::path::PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("e1-branches-{}-{call}.o", std::process::id()));
    let mut child = Command::new(mc)
        .args(["--triple=x86_64", "-filetype=obj", "-o"])
        .arg(&out)
        .stdin(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn llvm-mc");
    {
        let mut stdin = child.stdin.take().unwrap();
        for l in lines {
            writeln!(stdin, "{l}").unwrap();
        }
    }
    let done = child.wait_with_output().expect("llvm-mc output");
    assert!(
        done.status.success(),
        "llvm-mc failed: {}",
        String::from_utf8_lossy(&done.stderr)
    );
    let bytes = std::fs::read(&out).expect("read the assembled object");
    let _ = std::fs::remove_file(&out);
    let f = object::File::parse(&*bytes).expect("llvm-mc's object parses");
    let text = f.section_by_name(".text").expect(".text");
    assert_eq!(
        text.relocations().count(),
        0,
        "llvm-mc left a relocation on a branch"
    );
    text.data().expect("text data").to_vec()
}

/// What LLVM encodes each form as, in order: `-show-encoding` for everything
/// but the branches, the object's `.text` for those.
fn llvm_encodings(mc: &str, forms: &[Inst]) -> Vec<Vec<u8>> {
    let (branches, plain): (Vec<&Inst>, Vec<&Inst>) = forms.iter().partition(|f| is_branch(f));
    let plain_text: Vec<String> = plain.iter().map(|f| f.att()).collect();
    let mut plain_bytes = assemble(mc, &plain_text).into_iter();
    assert_eq!(
        plain_bytes.len(),
        plain.len(),
        "llvm-mc gave one encoding per line"
    );
    let branch_text: Vec<String> = branches.iter().map(|f| f.att()).collect();
    let obj = assemble_object(mc, &branch_text);
    // Every branch form is 6 bytes in synth's encoding; if LLVM chose another
    // length the object is not 6 bytes per form, and the comparison below
    // disagrees from the first such form on.
    assert_eq!(
        obj.len(),
        6 * branches.len(),
        "llvm-mc did not assemble every branch to 6 bytes"
    );
    let mut branch_bytes = obj.chunks(6).map(<[u8]>::to_vec);
    forms
        .iter()
        .map(|f| {
            if is_branch(f) {
                branch_bytes.next().unwrap()
            } else {
                plain_bytes.next().unwrap()
            }
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
    let forms = all_forms();
    assert_eq!(forms.len(), FORM_COUNT, "the E1 form count moved");
    let text: Vec<String> = forms.iter().map(Inst::att).collect();
    let got = llvm_encodings(&mc, &forms);
    assert_eq!(got.len(), forms.len());
    assert_eq!(forms.iter().filter(|f| is_branch(f)).count(), 80);
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
/// EVERY form whose encoding sets REX.B (the r/m or opcode register is
/// r8-r15), and on no other.
#[test]
fn a_dropped_rex_b_disagrees_with_llvm_mc() {
    let Some(mc) = mc_or_skip("a_dropped_rex_b_disagrees_with_llvm_mc") else {
        return;
    };
    let forms = all_forms();
    let got = llvm_encodings(&mc, &forms);
    let mut mutated = 0;
    let mut caught = 0;
    for (f, want) in forms.iter().zip(&got) {
        let mut b = encode(f);
        let has_rex_b = b[0] & 0xF1 == 0x41;
        if has_rex_b {
            b[0] &= !1;
            mutated += 1;
        }
        if &b != want {
            caught += 1;
            assert!(has_rex_b, "{f}: an unmutated form disagrees");
        }
    }
    // Lanes X1-X2 (5,984): Alu 2048 + Imul 256 + ShiftCl 80 + SetCc 80 + Cmov
    // 2560 + Movx 768 + the three immediate moves 64 each.
    // Lanes X3-X4 (6,128), half of each register-in-r/m population: Load and
    // Store 4608 (the BASE is r8-r15) + BitScan 512 + AluImm 960 + Div 32 +
    // Push and Pop 16. A branch has no register and no REX.
    assert_eq!(mutated, 5984 + 6128);
    assert_eq!(caught, mutated);
}

/// Potency of the OBJECT route the branches take: a displacement one byte
/// off, and a neighbouring condition, each disagree with LLVM on every one of
/// the 80 branch forms. (The REX.B control above cannot reach a branch: it
/// has no register.)
#[test]
fn a_wrong_branch_displacement_or_condition_disagrees_with_llvm_mc() {
    use synth_backend_x86_64::inst::Cond;
    let Some(mc) = mc_or_skip("a_wrong_branch_displacement_or_condition_disagrees_with_llvm_mc")
    else {
        return;
    };
    let branches: Vec<Inst> = all_forms().into_iter().filter(is_branch).collect();
    assert_eq!(branches.len(), 80);
    let got = llvm_encodings(&mc, &branches);
    for (f, want) in branches.iter().zip(&got) {
        let Inst::Jcc { cond, rel } = *f else {
            unreachable!("is_branch admits only Jcc");
        };
        assert_eq!(&encode(f), want, "{f}: the unmutated branch disagrees");
        let off_by_one = Inst::Jcc {
            cond,
            rel: rel.wrapping_add(1),
        };
        assert_ne!(
            &encode(&off_by_one),
            want,
            "{f}: a wrong displacement agrees"
        );
        let k = Cond::ALL.iter().position(|c| *c == cond).unwrap();
        let other = Inst::Jcc {
            cond: Cond::ALL[(k + 1) % Cond::ALL.len()],
            rel,
        };
        assert_ne!(&encode(&other), want, "{f}: a wrong condition agrees");
    }
}
