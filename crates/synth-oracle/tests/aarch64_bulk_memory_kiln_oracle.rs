//! v0.92 plan B (steps 0+1): `memory.copy` and `memory.fill` on AArch64,
//! against kiln, with linear memory compared after EVERY step.
//!
//! The probe module is compiled by synth with `-b aarch64 --all-exports`
//! (the default `--safety-bounds software`) and run, as the bytes synth
//! emitted, on unicorn AArch64 (cortex-a53): linear memory 0 mapped at
//! `MEM_BASE` with exactly its declared size rounded to a page, `x28`
//! pointing at it (the backend's register contract,
//! `docs/embedder-abi-relocatable-aarch64.md`), every other caller-saved
//! register poisoned, x19-x29 and d8-d15 checked preserved. Each probe is a
//! SEQUENCE of calls: kiln runs it on one instance, the emulator carries each
//! step's final memory into the next step's image
//! (`synth_oracle::run_sequence_env`). A step agrees only when the outcomes
//! agree (a trap is `brk #0` inside the function on the emulator side) AND the
//! whole 64 KiB memory is byte-equal — after a trap too, so a bulk op that
//! wrote part of its range before trapping disagrees.
//!
//! WHAT IS ASKED BEYOND AGREEMENT: for every bulk step the test computes,
//! from the operands alone, whether wasm traps (`s + n > size` or
//! `d + n > size` in 64-bit arithmetic for copy, `d + n > size` for fill).
//! Both engines are held to that, and kiln's trap class must be
//! `MemoryOutOfBounds`. The step, probe and trap counts are exact literals.
//!
//! POTENCY, two tests:
//! - `forward_only_copy_is_caught`: the object's `b.hi` (the downward-copy
//!   branch) is overwritten with a `nop`, so every copy runs upward; the
//!   overlapping `d > s` probes must DISAGREE on memory.
//! - `a_write_before_the_trap_is_caught`: kiln runs a variant of the module
//!   whose `copy` and `fill` store one byte at address 0 before the bulk op;
//!   every trapping bulk step must DISAGREE on memory, which is what shows
//!   the after-trap memory comparison is live.
//!
//! Needs `--features exec`. `SYNTH` may name a prebuilt binary.

#![cfg(feature = "exec")]

use std::path::PathBuf;

use synth_oracle::compare::{EmuOutcome, RefOutcome, TrapClass};
use synth_oracle::emulate::{Cpu, EmuConfig};
use synth_oracle::reference::Imports;
use synth_oracle::synth::{CompiledObject, Machine, compile};
use synth_oracle::value::WasmValue;
use synth_oracle::{Case, run_sequence_env};

const FUEL: u64 = 10_000_000;
const FLAGS: &[&str] = &["-b", "aarch64", "--all-exports"];
const SIZE: u64 = 65536;

/// Every export, its body, and nothing the backend would refuse at module
/// level (no data segment, no import, no table).
fn module_wat(write_before_bulk: bool) -> String {
    // The potency variant: a store before the bulk op, at address 0, which is
    // always in bounds. kiln keeps it after the bulk op traps.
    let pre = if write_before_bulk {
        "i32.const 0 i32.const 0xEE i32.store8"
    } else {
        ""
    };
    format!(
        r#"(module
  (memory 1)
  (func (export "copy") (param $d i32) (param $s i32) (param $n i32)
    {pre}
    local.get $d local.get $s local.get $n memory.copy)
  (func (export "fill") (param $d i32) (param $v i32) (param $n i32)
    {pre}
    local.get $d local.get $v local.get $n memory.fill)
  ;; The operands are params that stay register-resident; reading them
  ;; after the op shows the lowering did not write them.
  (func (export "copy_sum") (param $d i32) (param $s i32) (param $n i32) (result i32)
    local.get $d local.get $s local.get $n memory.copy
    local.get $d local.get $s i32.add local.get $n i32.xor)
  (func (export "fill_sum") (param $d i32) (param $v i32) (param $n i32) (result i32)
    local.get $d local.get $v local.get $n memory.fill
    local.get $d local.get $v i32.add local.get $n i32.xor)
  ;; Two values live BELOW the bulk op's operands must survive it.
  (func (export "copy_live") (param $d i32) (param $s i32) (param $n i32) (result i32)
    i32.const 1000
    local.get $s i32.load8_u
    local.get $d local.get $s local.get $n memory.copy
    i32.add)
  ;; Seeds [base, base+len) with a byte pattern that differs per address.
  (func (export "seed") (param $base i32) (param $len i32) (local $i i32)
    block
      loop
        local.get $i local.get $len i32.ge_u br_if 1
        local.get $base local.get $i i32.add
        local.get $i i32.const 7 i32.mul i32.const 3 i32.add
        local.get $base i32.xor
        i32.store8
        local.get $i i32.const 1 i32.add local.set $i
        br 0
      end
    end)
  (func (export "add") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)
  (func (export "store32") (param i32 i32) local.get 0 local.get 1 i32.store)
  (func (export "load32") (param i32) (result i32) local.get 0 i32.load)
  (func (export "load8") (param i32) (result i32) local.get 0 i32.load8_u)
)"#
    )
}

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("synth-oracle-a64-bulk-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn wasm(write_before_bulk: bool) -> Vec<u8> {
    wat::parse_str(module_wat(write_before_bulk)).expect("probe WAT parses")
}

const EXPORTS: &[&str] = &[
    "copy",
    "fill",
    "copy_sum",
    "fill_sum",
    "copy_live",
    "seed",
    "add",
    "store32",
    "load32",
    "load8",
];

fn compile_a64() -> CompiledObject {
    let dir = scratch();
    let input = dir.join("bulk.wasm");
    std::fs::write(&input, wasm(false)).unwrap();
    let out = dir.join("bulk-aarch64.o");
    let run = compile(&input, FLAGS, &out).expect("synth runs");
    assert!(
        run.status.success(),
        "aarch64: synth compile failed: {}",
        run.stderr
    );
    assert!(
        !run.stderr.contains("skipping function"),
        "aarch64: synth skipped a probe function:\n{}",
        run.stderr
    );
    let obj = run.object.expect("object parsed");
    assert_eq!(obj.machine, Machine::AArch64);
    for e in EXPORTS {
        assert!(
            obj.function_bytes(e).is_some_and(|b| !b.is_empty()),
            "no bytes for `{e}` in the symtab:\n{}",
            run.stderr
        );
    }
    assert!(
        obj.relocs.is_empty(),
        "the probe object carries relocations"
    );
    obj
}

fn cfg() -> EmuConfig {
    EmuConfig::new(Cpu::CortexA53)
}

/// One call of a probe sequence and what wasm does with it, computed here.
#[derive(Clone, Debug)]
struct Step {
    export: &'static str,
    args: Vec<u32>,
    /// `Some(true)`: wasm traps (out of bounds); `Some(false)`: it returns;
    /// `None`: not a bulk step, kiln's word is taken.
    traps: Option<bool>,
}

fn copy_traps(d: u32, s: u32, n: u32) -> bool {
    u64::from(s) + u64::from(n) > SIZE || u64::from(d) + u64::from(n) > SIZE
}

fn fill_traps(d: u32, n: u32) -> bool {
    u64::from(d) + u64::from(n) > SIZE
}

fn copy(export: &'static str, d: u32, s: u32, n: u32) -> Step {
    Step {
        export,
        args: vec![d, s, n],
        traps: Some(copy_traps(d, s, n)),
    }
}

fn fill(export: &'static str, d: u32, v: u32, n: u32) -> Step {
    Step {
        export,
        args: vec![d, v, n],
        traps: Some(fill_traps(d, n)),
    }
}

fn call(export: &'static str, args: &[u32]) -> Step {
    Step {
        export,
        args: args.to_vec(),
        traps: None,
    }
}

/// A probe: a name and its steps. Every probe starts from a fresh instance
/// and seeds both ends of memory first, so a copy moves distinguishable
/// bytes and a stray write anywhere in the seeded windows shows.
struct Probe {
    name: &'static str,
    steps: Vec<Step>,
}

fn probe(name: &'static str, body: Vec<Step>) -> Probe {
    let top = (SIZE - 512) as u32;
    let mut steps = vec![call("seed", &[0, 512]), call("seed", &[top, 512])];
    steps.extend(body);
    Probe { name, steps }
}

const END: u32 = SIZE as u32;

fn probes() -> Vec<Probe> {
    vec![
        // --- harness smoke: no bulk op ---
        probe(
            "smoke",
            vec![
                call("add", &[7, 0xFFFF_FFFF]),
                call("store32", &[100, 0xDEAD_BEEF]),
                call("load32", &[100]),
                call("load8", &[101]),
                call("load32", &[END - 4]),
                call("store32", &[END - 4, 0x0102_0304]),
                call("load8", &[END - 1]),
            ],
        ),
        probe("smoke-load-oob", vec![call("load32", &[END - 3])]),
        probe(
            "smoke-store-oob",
            vec![call("store32", &[END - 2, 0x1111_1111])],
        ),
        // --- memory.copy ---
        probe(
            "copy-forward-overlap",
            vec![copy("copy", 10, 20, 100), call("load32", &[10])],
        ),
        probe(
            "copy-backward-overlap",
            vec![copy("copy", 30, 10, 100), call("load32", &[126])],
        ),
        probe(
            "copy-backward-overlap-by-one",
            vec![copy("copy", 11, 10, 200)],
        ),
        probe(
            "copy-forward-overlap-by-one",
            vec![copy("copy", 10, 11, 200)],
        ),
        probe("copy-disjoint", vec![copy("copy", 300, 0, 64)]),
        probe("copy-disjoint-down", vec![copy("copy", 0, 300, 64)]),
        probe("copy-identity", vec![copy("copy", 50, 50, 40)]),
        probe(
            "copy-n0-in-bounds",
            vec![copy("copy", 5, 6, 0), copy("copy", END, END, 0)],
        ),
        probe("copy-n0-dst-oob", vec![copy("copy", END + 1, 0, 0)]),
        probe("copy-n0-src-oob", vec![copy("copy", 0, END + 1, 0)]),
        probe("copy-dst-oob-at-end", vec![copy("copy", END - 10, 0, 11)]),
        probe("copy-src-oob-at-end", vec![copy("copy", 0, END - 10, 11)]),
        probe(
            "copy-overlap-oob-at-end",
            vec![copy("copy", END - 60, END - 100, 61)],
        ),
        probe(
            "copy-exact-fit",
            vec![
                copy("copy", END - 100, 0, 100),
                copy("copy", 0, END - 100, 100),
                copy("copy", END - 60, END - 100, 60),
                call("load8", &[END - 1]),
            ],
        ),
        probe(
            "copy-whole-memory-up",
            vec![copy("copy", 0, 1, END - 1), call("load8", &[END - 2])],
        ),
        probe(
            "copy-whole-memory-down",
            vec![copy("copy", 1, 0, END - 1), call("load8", &[END - 1])],
        ),
        probe("copy-n-max", vec![copy("copy", 0, 0, u32::MAX)]),
        probe("copy-dst-max", vec![copy("copy", u32::MAX, 0, 1)]),
        // A 32-bit `d + n` wraps to 0x100, inside the memory.
        probe("copy-dst-wrap32", vec![copy("copy", 0xFFFF_FF00, 0, 0x200)]),
        probe("copy-src-wrap32", vec![copy("copy", 0, 0xFFFF_FF00, 0x200)]),
        probe(
            "copy-sum-keeps-operands",
            vec![copy("copy_sum", 40, 7, 33), copy("copy_sum", 7, 40, 33)],
        ),
        probe(
            "copy-live-below",
            vec![copy("copy_live", 3, 1, 20), copy("copy_live", 1, 3, 20)],
        ),
        // --- memory.fill ---
        probe(
            "fill-value-over-255",
            vec![fill("fill", 100, 0x1234_56AB, 50), call("load32", &[100])],
        ),
        probe("fill-all-ones", vec![fill("fill", 100, u32::MAX, 1)]),
        probe(
            "fill-n0-in-bounds",
            vec![fill("fill", 9, 7, 0), fill("fill", END, 7, 0)],
        ),
        probe("fill-n0-oob", vec![fill("fill", END + 1, 7, 0)]),
        probe("fill-oob-at-end", vec![fill("fill", END - 10, 9, 11)]),
        probe(
            "fill-exact-fit",
            vec![fill("fill", END - 10, 0x1FF, 10), call("load8", &[END - 1])],
        ),
        probe("fill-whole-memory", vec![fill("fill", 0, 0x5A, END)]),
        probe("fill-n-max", vec![fill("fill", 0, 1, u32::MAX)]),
        probe("fill-wrap32", vec![fill("fill", 0xFFFF_FF00, 1, 0x200)]),
        probe(
            "fill-sum-keeps-operands",
            vec![fill("fill_sum", 20, 0x3C3, 9)],
        ),
    ]
}

/// Run one probe on `obj` against `reference_wasm`.
fn run_probe(reference_wasm: &[u8], obj: &CompiledObject, p: &Probe) -> Vec<Case> {
    let args: Vec<Vec<WasmValue>> = p
        .steps
        .iter()
        .map(|s| s.args.iter().map(|&a| WasmValue::I32(a)).collect())
        .collect();
    let steps: Vec<(&str, &[WasmValue])> = p
        .steps
        .iter()
        .zip(&args)
        .map(|(s, a)| (s.export, a.as_slice()))
        .collect();
    run_sequence_env(reference_wasm, obj, &steps, FUEL, &Imports::new(), &cfg())
        .unwrap_or_else(|e| panic!("{}: harness error {e:?}", p.name))
}

fn is_oob_trap(r: &RefOutcome) -> bool {
    matches!(
        r,
        RefOutcome::Trap {
            class: TrapClass::MemoryOutOfBounds,
            ..
        }
    )
}

#[test]
fn bulk_memory_agrees_with_kiln_on_aarch64() {
    let w = wasm(false);
    let obj = compile_a64();
    let mut failures = Vec::new();
    let (mut steps, mut traps) = (0usize, 0usize);
    let all = probes();
    for p in &all {
        let cases = run_probe(&w, &obj, p);
        if cases.len() != p.steps.len() {
            failures.push(format!(
                "{}: ran {} of {} steps (last: {:?})",
                p.name,
                cases.len(),
                p.steps.len(),
                cases.last().map(|c| (&c.reference, &c.emulator))
            ));
        }
        for (c, s) in cases.iter().zip(&p.steps) {
            steps += 1;
            if !c.verdict.is_agree() {
                failures.push(format!(
                    "{} {}{:x?}: {:?} (ref {:?}, emu {:?})",
                    p.name, s.export, s.args, c.verdict, c.reference, c.emulator
                ));
                continue;
            }
            let trapped = matches!(c.emulator, EmuOutcome::Trap { .. });
            if trapped {
                traps += 1;
                if !is_oob_trap(&c.reference) {
                    failures.push(format!(
                        "{} {}{:x?}: kiln trap is not MemoryOutOfBounds: {:?}",
                        p.name, s.export, s.args, c.reference
                    ));
                }
            }
            if let Some(want) = s.traps
                && want != trapped
            {
                failures.push(format!(
                    "{} {}{:x?}: wasm {} here, both engines {}",
                    p.name,
                    s.export,
                    s.args,
                    if want { "traps" } else { "returns" },
                    if trapped { "trapped" } else { "returned" }
                ));
            }
        }
    }
    for f in failures.iter().take(30) {
        eprintln!("aarch64 bulk-memory: {f}");
    }
    assert!(
        failures.is_empty(),
        "aarch64 bulk-memory: {} failures",
        failures.len()
    );
    // Exact literals: a probe that silently stopped running moves them.
    assert_eq!(all.len(), 35, "probe count moved");
    assert_eq!(steps, 124, "step count moved");
    assert_eq!(traps, 15, "trap count moved");
    eprintln!(
        "ORACLE aarch64-kiln bulk-memory: {steps} steps agree across {} probes, {traps} traps",
        all.len()
    );
}

/// The A64 `b.cond` encoding with condition HI (`0x54xxxxx8`).
fn is_bhi(word: u32) -> bool {
    word & 0xFF00_001F == 0x5400_0008
}

#[test]
fn forward_only_copy_is_caught() {
    let w = wasm(false);
    let mut obj = compile_a64();
    // Overwrite the downward-copy branch of `copy` with a `nop`.
    let f = obj.funcs["copy"].clone();
    let (lo, hi) = (f.offset as usize, (f.offset + f.size) as usize);
    let at: Vec<usize> = (lo..hi)
        .step_by(4)
        .filter(|&o| {
            is_bhi(u32::from_le_bytes([
                obj.text[o],
                obj.text[o + 1],
                obj.text[o + 2],
                obj.text[o + 3],
            ]))
        })
        .collect();
    assert_eq!(at.len(), 1, "expected exactly one b.hi in `copy`");
    obj.text[at[0]..at[0] + 4].copy_from_slice(&0xD503_201Fu32.to_le_bytes());

    let mut disagree = Vec::new();
    for p in probes().iter().filter(|p| p.name.starts_with("copy-")) {
        let cases = run_probe(&w, &obj, p);
        if cases.iter().any(|c| !c.verdict.is_agree()) {
            disagree.push(p.name);
        }
    }
    // Exactly the probes whose copy has d > s with overlapping ranges. A
    // forward copy is right for d <= s and for disjoint ranges.
    assert_eq!(
        disagree,
        [
            "copy-backward-overlap",
            "copy-backward-overlap-by-one",
            "copy-exact-fit",
            "copy-whole-memory-down",
        ],
        "a forward-only copy must disagree exactly on the overlapping d > s probes"
    );
}

#[test]
fn a_write_before_the_trap_is_caught() {
    // kiln runs a module that stores 0xEE at address 0 before each bulk op;
    // the emulator runs synth's object for the real module. A trapping bulk
    // step then differs ONLY in memory (both trap), so its disagreement is
    // the after-trap memory comparison firing.
    let reference = wasm(true);
    let obj = compile_a64();
    let (mut trapping, mut caught) = (0usize, 0usize);
    for p in probes() {
        let cases = run_probe(&reference, &obj, &p);
        for (c, s) in cases.iter().zip(&p.steps) {
            let is_plain_bulk = matches!(s.export, "copy" | "fill");
            if !(is_plain_bulk && s.traps == Some(true)) {
                continue;
            }
            trapping += 1;
            let both_trap =
                matches!(c.emulator, EmuOutcome::Trap { .. }) && is_oob_trap(&c.reference);
            let memory_differs = matches!(&c.verdict, synth_oracle::compare::Verdict::Disagree(m) if m.contains("memory differs"));
            if both_trap && memory_differs {
                caught += 1;
            }
        }
    }
    assert_eq!(trapping, 13, "trapping plain bulk steps moved");
    assert_eq!(
        caught, trapping,
        "every trapping bulk step must disagree on memory when the reference \
         wrote a byte before trapping"
    );
}
