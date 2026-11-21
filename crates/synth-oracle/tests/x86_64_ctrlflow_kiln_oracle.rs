//! RQ-91-X86CTRL (Refs #1741): x86-64 structured control flow against kiln —
//! lane X5.
//!
//! Every probe is compiled by synth with `-b x86_64 --relocatable` and run,
//! as the bytes synth emitted, on unicorn x86-64 (CPU model pinned to QEMU64;
//! SysV arguments with POISONED upper halves; poisoned scratch registers,
//! flags and stack; callee-saved registers, `rsp`, the direction flag and the
//! caller's frame checked; no store below `rsp - 8` and none into the frame
//! at a misaligned `rsp`) and on kiln. Every case has to AGREE.
//!
//! WHAT IS ASKED BEYOND AGREEMENT: every shaped probe also states the value
//! it must return, computed HERE in Rust from the arguments (or, for a trap,
//! WHICH `ud2` of the function it must stop on, with kiln's trap class
//! `unreachable`). So both engines are checked against a third answer.
//!
//! THE GROUPS: loops with counters (top- and bottom-tested, a result loop
//! whose back-edge must carry nothing, nested, i64, a `br_table` back-edge);
//! nested blocks with results (values beneath them, deeper than the six
//! temporaries); `if` with and without `else`; `br` out of nested loops;
//! `br_table` at every index and at out-of-range indices (`0x7fffffff`,
//! `0x80000000`, `0xffffffff`), void and value-carrying, 1 to 16 targets;
//! `unreachable` stopping on the right `ud2`; and the pinned shapes of
//! X86_PLAN lane X5 — every integer export of the #1691 fixture
//! (`scripts/repro/if_arm_dead_value_1691.wat`, embedded) and the two
//! "below entry height" shapes of the plan's cold review 1 (`v1`, `v4`), each
//! with its exact value. Four of the fixture's float exports are checked to
//! be NAMED declines.
//!
//! RANDOM PROGRAMS: 40 seeded modules of random structured control flow
//! (blocks, loops with counters, if/else, br, br_if, br_table, return,
//! unreachable, dead code after a transfer, values beneath frames) run on
//! kiln and as emitted code; every case agrees, the count is exact.
//!
//! RED ON THE BASE (lane X3/X4, 57d4aed8): `block`, `loop`, `if` and
//! `unreachable` are refused there, so every group but the float declines
//! fails to compile.
//!
//! Needs `--features exec`. `SYNTH` may name a prebuilt binary.

#![cfg(feature = "exec")]

use std::path::PathBuf;

use synth_oracle::compare::{EmuOutcome, RefOutcome, TrapClass};
use synth_oracle::emulate::{Cpu, EmuConfig, TEXT_BASE};
use synth_oracle::reference::Imports;
use synth_oracle::synth::{CompiledObject, Machine, compile};
use synth_oracle::value::WasmValue;
use synth_oracle::{Case, run_case};

const FUEL: u64 = 1_000_000;
const FLAGS: &[&str] = &["-b", "x86_64", "--relocatable", "--all-exports"];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum T {
    I32,
    I64,
}

impl T {
    fn s(self) -> &'static str {
        match self {
            T::I32 => "i32",
            T::I64 => "i64",
        }
    }

    fn val(self, bits: u64) -> WasmValue {
        match self {
            T::I32 => WasmValue::I32(bits as u32),
            T::I64 => WasmValue::I64(bits),
        }
    }
}

/// splitmix64: a fixed, seedable stream.
struct Rng(u64);

impl Rng {
    fn new(seed: &str) -> Self {
        let mut h = 0xCBF2_9CE4_8422_2325u64;
        for b in seed.bytes() {
            h = (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01B3);
        }
        Rng(h)
    }

    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// What one case must do, computed from the arguments.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Expect {
    /// Returns exactly this value.
    Exactly(u64),
    /// Traps on `unreachable`, at the function's `ud2` number `k` (0-based,
    /// in address order).
    Trap(usize),
}

type ExpectFn = Box<dyn Fn(&[u64]) -> Expect>;

struct Probe {
    name: String,
    params: Vec<T>,
    result: T,
    body: String,
    vectors: Vec<Vec<u64>>,
    expect: ExpectFn,
    /// How many `ud2` the function holds (checked when a case traps).
    ud2s: usize,
}

fn probe(
    name: &str,
    params: Vec<T>,
    result: T,
    body: &str,
    vectors: Vec<Vec<u64>>,
    expect: impl Fn(&[u64]) -> Expect + 'static,
) -> Probe {
    Probe {
        name: name.to_string(),
        params,
        result,
        body: body.to_string(),
        vectors,
        expect: Box::new(expect),
        ud2s: 0,
    }
}

impl Probe {
    fn with_ud2s(mut self, n: usize) -> Self {
        self.ud2s = n;
        self
    }
}

struct Group {
    label: String,
    probes: Vec<Probe>,
}

impl Group {
    fn new(label: &str, probes: Vec<Probe>) -> Self {
        Group {
            label: label.to_string(),
            probes,
        }
    }

    fn wat(&self) -> String {
        let mut s = String::from("(module\n");
        for p in &self.probes {
            let params: Vec<&str> = p.params.iter().map(|t| t.s()).collect();
            let params = if params.is_empty() {
                String::new()
            } else {
                format!("(param {})", params.join(" "))
            };
            s.push_str(&format!(
                "  (func (export \"{}\") {params} (result {})\n    {})\n",
                p.name,
                p.result.s(),
                p.body
            ));
        }
        s.push_str(")\n");
        s
    }

    fn cases(&self) -> usize {
        self.probes.iter().map(|p| p.vectors.len()).sum()
    }
}

/// i32 edge values, then `n` seeded random ones.
fn xs(seed: &str, n: usize) -> Vec<u64> {
    let mut v: Vec<u64> = vec![
        0,
        1,
        2,
        3,
        5,
        7,
        8,
        15,
        16,
        31,
        0x7F,
        0x80,
        0xFFFF,
        0x7FFF_FFFF,
        0x8000_0000,
        0xFFFF_FFFE,
        0xFFFF_FFFF,
    ];
    let mut r = Rng::new(seed);
    v.extend((0..n).map(|_| r.next() & 0xFFFF_FFFF));
    v
}

fn one(seed: &str) -> Vec<Vec<u64>> {
    xs(seed, 8).into_iter().map(|x| vec![x]).collect()
}

/// Every pair of a short edge list, then seeded random pairs.
fn two(seed: &str) -> Vec<Vec<u64>> {
    let e = [0u64, 1, 2, 3, 6, 7, 0x7FFF_FFFF, 0x8000_0000, 0xFFFF_FFFF];
    let mut v = Vec::new();
    for &a in &e {
        for &b in &e {
            v.push(vec![a, b]);
        }
    }
    let mut r = Rng::new(seed);
    for _ in 0..16 {
        v.push(vec![r.next() & 0xFFFF_FFFF, r.next() & 0xFFFF_FFFF]);
    }
    v
}

fn w32(x: u64) -> u32 {
    x as u32
}

fn ex32(x: u32) -> Expect {
    Expect::Exactly(u64::from(x))
}

// --------------------------------------------------------------- loops ----

fn loops() -> Group {
    Group::new(
        "loops",
        vec![
            // Top-tested: sum 1..n, n = x & 31.
            probe(
                "sum",
                vec![T::I32],
                T::I32,
                "(local i32 i32)
                 local.get 0 i32.const 31 i32.and local.set 1
                 block loop
                   local.get 1 i32.eqz br_if 1
                   local.get 2 local.get 1 i32.add local.set 2
                   local.get 1 i32.const 1 i32.sub local.set 1
                   br 0
                 end end
                 local.get 2",
                one("sum"),
                |v| {
                    let n = w32(v[0]) & 31;
                    ex32(n * (n + 1) / 2)
                },
            ),
            // Bottom-tested (do-while), the back-edge a `br_if`.
            probe(
                "do_while",
                vec![T::I32, T::I32],
                T::I32,
                "(local i32)
                 local.get 0 i32.const 15 i32.and i32.const 1 i32.add local.set 2
                 loop
                   local.get 1 i32.const 3 i32.mul local.get 2 i32.add local.set 1
                   local.get 2 i32.const 1 i32.sub local.tee 2
                   br_if 0
                 end
                 local.get 1",
                two("do_while"),
                |v| {
                    let mut acc = w32(v[1]);
                    let mut i = (w32(v[0]) & 15) + 1;
                    while i != 0 {
                        acc = acc.wrapping_mul(3).wrapping_add(i);
                        i -= 1;
                    }
                    ex32(acc)
                },
            ),
            // A RESULT loop: its back-edge carries NOTHING (the label of a
            // loop is its header, and takes the loop's parameters), and the
            // fall-through leaves the result.
            probe(
                "loop_result",
                vec![T::I32],
                T::I32,
                "(local i32)
                 loop (result i32)
                   local.get 1 i32.const 1 i32.add local.tee 1
                   local.get 1 local.get 0 i32.const 7 i32.and i32.lt_u
                   br_if 0
                 end",
                one("loop_result"),
                |v| ex32((w32(v[0]) & 7).max(1)),
            ),
            // Nested counted loops.
            probe(
                "nested",
                vec![T::I32, T::I32],
                T::I32,
                "(local i32 i32 i32)
                 block loop
                   local.get 2 local.get 0 i32.const 7 i32.and i32.ge_u br_if 1
                   i32.const 0 local.set 3
                   block loop
                     local.get 3 local.get 1 i32.const 7 i32.and i32.ge_u br_if 1
                     local.get 4 local.get 2 local.get 3 i32.mul i32.const 1 i32.add
                     i32.add local.set 4
                     local.get 3 i32.const 1 i32.add local.set 3
                     br 0
                   end end
                   local.get 2 i32.const 1 i32.add local.set 2
                   br 0
                 end end
                 local.get 4",
                two("nested"),
                |v| {
                    let (a, b) = (w32(v[0]) & 7, w32(v[1]) & 7);
                    let mut acc = 0u32;
                    for i in 0..a {
                        for j in 0..b {
                            acc = acc.wrapping_add(i * j + 1);
                        }
                    }
                    ex32(acc)
                },
            ),
            // An i64 accumulator.
            probe(
                "loop64",
                vec![T::I64, T::I32],
                T::I64,
                "(local i32)
                 local.get 1 i32.const 15 i32.and local.set 2
                 block loop
                   local.get 2 i32.eqz br_if 1
                   local.get 0 i64.const 5 i64.mul i64.const 1 i64.add local.set 0
                   local.get 2 i32.const 1 i32.sub local.set 2
                   br 0
                 end end
                 local.get 0",
                {
                    let mut r = Rng::new("loop64");
                    let mut v: Vec<Vec<u64>> = [0u64, 1, 7, 15, 16, 0xFFFF_FFFF]
                        .iter()
                        .flat_map(|&n| [vec![0, n], vec![u64::MAX, n], vec![0x1234_5678_9ABC, n]])
                        .collect();
                    for _ in 0..8 {
                        v.push(vec![r.next(), r.next() & 0xFFFF_FFFF]);
                    }
                    v
                },
                |v| {
                    let mut acc = v[0];
                    for _ in 0..(v[1] & 15) {
                        acc = acc.wrapping_mul(5).wrapping_add(1);
                    }
                    Expect::Exactly(acc)
                },
            ),
            // A `br_table` whose index 0 is the loop's back-edge and whose
            // other targets leave.
            probe(
                "table_loop",
                vec![T::I32],
                T::I32,
                "(local i32 i32)
                 local.get 0 i32.const 15 i32.and i32.const 1 i32.add local.set 1
                 block loop
                   local.get 2 local.get 1 i32.add local.set 2
                   local.get 1 i32.const 1 i32.sub local.tee 1
                   i32.eqz
                   br_table 0 1 1
                 end end
                 local.get 2",
                one("table_loop"),
                |v| {
                    let n = (w32(v[0]) & 15) + 1;
                    ex32(n * (n + 1) / 2)
                },
            ),
        ],
    )
}

// -------------------------------------------------------------- blocks ----

/// `x OP y` for the fold below.
fn fold(stack: &mut Vec<u32>, ops: &[&str]) -> u32 {
    for op in ops {
        let y = stack.pop().unwrap();
        let x = stack.pop().unwrap();
        stack.push(match *op {
            "add" => x.wrapping_add(y),
            "sub" => x.wrapping_sub(y),
            "xor" => x ^ y,
            _ => unreachable!(),
        });
    }
    assert_eq!(stack.len(), 1);
    stack[0]
}

fn blocks() -> Group {
    Group::new(
        "blocks",
        vec![
            // A value-carrying br_if to the inner block, one to the outer
            // block, and the fall-through, with a value beneath both.
            probe(
                "nested_values",
                vec![T::I32, T::I32],
                T::I32,
                "i32.const 1000
                 block (result i32)
                   block (result i32)
                     local.get 0
                     local.get 1 i32.const 1 i32.and br_if 0
                     i32.const 2 i32.mul
                     local.get 1 i32.const 2 i32.and br_if 1
                     i32.const 3 i32.add
                   end
                   i32.const 10 i32.mul
                 end
                 i32.sub",
                two("nested_values"),
                |v| {
                    let (a, b) = (w32(v[0]), w32(v[1]));
                    let outer = if b & 1 != 0 {
                        a.wrapping_mul(10)
                    } else if b & 2 != 0 {
                        a.wrapping_mul(2)
                    } else {
                        a.wrapping_mul(2).wrapping_add(3).wrapping_mul(10)
                    };
                    ex32(1000u32.wrapping_sub(outer))
                },
            ),
            // Seven values beneath a block (one more than the temporaries:
            // the deepest is SPILLED when the block opens), folded after it.
            probe(
                "beneath_spilled",
                vec![T::I32, T::I32],
                T::I32,
                "local.get 0 local.get 1 local.get 0 local.get 1 local.get 0
                 local.get 1 local.get 0
                 i32.const 9 drop
                 block (result i32)
                   local.get 1 local.get 0 local.get 1 i32.lt_u br_if 0
                   i32.const 5 i32.add
                 end
                 i32.add i32.sub i32.xor i32.add i32.sub i32.xor i32.add",
                two("beneath_spilled"),
                |v| {
                    let (a, b) = (w32(v[0]), w32(v[1]));
                    let r = if a < b { b } else { b.wrapping_add(5) };
                    let mut st = vec![a, b, a, b, a, b, a, r];
                    ex32(fold(
                        &mut st,
                        &["add", "sub", "xor", "add", "sub", "xor", "add"],
                    ))
                },
            ),
            // if/else with results, nested.
            probe(
                "if_else_values",
                vec![T::I32, T::I32],
                T::I32,
                "local.get 0 i32.const 3 i32.and
                 if (result i32)
                   local.get 1 i32.const 1 i32.and
                   if (result i32) i32.const 10 else i32.const 20 end
                 else
                   local.get 1
                   if (result i32) i32.const 30 else i32.const 40 end
                 end
                 local.get 0 i32.add",
                two("if_else_values"),
                |v| {
                    let (a, b) = (w32(v[0]), w32(v[1]));
                    let r: u32 = if a & 3 != 0 {
                        if b & 1 != 0 { 10 } else { 20 }
                    } else if b != 0 {
                        30
                    } else {
                        40
                    };
                    ex32(r.wrapping_add(a))
                },
            ),
            // An i64 label value.
            probe(
                "block64",
                vec![T::I64, T::I32],
                T::I64,
                "block (result i64)
                   local.get 0 local.get 1 br_if 0
                   i64.const 3 i64.mul
                 end
                 i64.const 1 i64.add",
                {
                    let mut v = Vec::new();
                    for a in [0u64, 1, u64::MAX, 0x8000_0000_0000_0000, 0x1_0000_0001] {
                        for b in [0u64, 1, 0x8000_0000] {
                            v.push(vec![a, b]);
                        }
                    }
                    v
                },
                |v| {
                    let r = if w32(v[1]) != 0 {
                        v[0]
                    } else {
                        v[0].wrapping_mul(3)
                    };
                    Expect::Exactly(r.wrapping_add(1))
                },
            ),
            // A br_if to the FUNCTION body (a return), with a value beneath.
            probe(
                "br_to_function",
                vec![T::I32],
                T::I32,
                "i32.const 5
                 block
                   i32.const 9 local.get 0 br_if 1 drop
                 end
                 i32.const 77 i32.add",
                one("br_to_function"),
                |v| ex32(if w32(v[0]) != 0 { 9 } else { 82 }),
            ),
        ],
    )
}

// ------------------------------------------------------ if without else ----

fn ifs() -> Group {
    Group::new(
        "if without else",
        vec![
            probe(
                "if_no_else",
                vec![T::I32, T::I32],
                T::I32,
                "(local i32)
                 local.get 1 local.set 2
                 local.get 0
                 if local.get 2 i32.const 3 i32.mul local.set 2 end
                 local.get 2",
                two("if_no_else"),
                |v| {
                    let b = w32(v[1]);
                    ex32(if w32(v[0]) != 0 { b.wrapping_mul(3) } else { b })
                },
            ),
            probe(
                "if_no_else_beneath",
                vec![T::I32, T::I32],
                T::I32,
                "local.get 1
                 local.get 0 i32.const 1 i32.and
                 if local.get 1 i32.const 1 i32.add local.set 1 end
                 local.get 1 i32.add",
                two("if_no_else_beneath"),
                |v| {
                    let b = w32(v[1]);
                    let b2 = if w32(v[0]) & 1 != 0 {
                        b.wrapping_add(1)
                    } else {
                        b
                    };
                    ex32(b.wrapping_add(b2))
                },
            ),
            probe(
                "if_no_else_return",
                vec![T::I32],
                T::I32,
                "i32.const 50
                 local.get 0 if i32.const 4 return end
                 i32.const 1 i32.add",
                one("if_no_else_return"),
                |v| ex32(if w32(v[0]) != 0 { 4 } else { 51 }),
            ),
        ],
    )
}

// ------------------------------------------- br out of nested loops ----

fn break_out() -> Group {
    Group::new(
        "br out of nested loops",
        vec![
            // Search an 8 x 8 grid for (a & 127) = 8i + j; `br 3` leaves both
            // loops carrying 100i + j to a result block. a & 127 >= 64 is not
            // found: -1.
            probe(
                "search",
                vec![T::I32, T::I32],
                T::I32,
                "(local i32 i32)
                 block (result i32)
                   loop
                     i32.const 0 local.set 3
                     loop
                       local.get 2 i32.const 8 i32.mul local.get 3 i32.add
                       local.get 0 i32.const 127 i32.and i32.eq
                       if
                         local.get 2 i32.const 100 i32.mul local.get 3 i32.add
                         br 3
                       end
                       local.get 3 i32.const 1 i32.add local.tee 3
                       i32.const 8 i32.lt_u br_if 0
                     end
                     local.get 2 i32.const 1 i32.add local.tee 2
                     i32.const 8 i32.lt_u br_if 0
                   end
                   i32.const -1
                 end
                 local.get 1 i32.add",
                {
                    let mut v = two("search");
                    for k in [0u64, 9, 63, 64, 100, 127, 128 + 17] {
                        v.push(vec![k, 3]);
                    }
                    v
                },
                |v| {
                    let k = w32(v[0]) & 127;
                    let r = if k < 64 {
                        (k / 8) * 100 + k % 8
                    } else {
                        u32::MAX
                    };
                    ex32(r.wrapping_add(w32(v[1])))
                },
            ),
            // `return` from inside two loops.
            probe(
                "return_from_loops",
                vec![T::I32],
                T::I32,
                "(local i32)
                 loop
                   loop
                     local.get 1 i32.const 1 i32.add local.tee 1
                     local.get 0 i32.const 31 i32.and i32.gt_u
                     if local.get 1 i32.const 1000 i32.add return end
                     local.get 1 i32.const 3 i32.and br_if 0
                   end
                   br 0
                 end
                 unreachable",
                one("return_from_loops"),
                |v| ex32((w32(v[0]) & 31) + 1 + 1000),
            ),
        ],
    )
}

// ------------------------------------------------------------ br_table ----

/// A void `br_table` over `n` targets returning `100 + label`. Target `i`
/// is label `(3i + 1) mod (n + 1)`, the default is label `dflt`.
fn table(n: usize, dflt: usize) -> Probe {
    let labels: Vec<usize> = (0..n).map(|i| (3 * i + 1) % (n + 1)).collect();
    let mut body = "block ".repeat(n + 1);
    body.push_str("local.get 0 br_table");
    for l in &labels {
        body.push_str(&format!(" {l}"));
    }
    body.push_str(&format!(" {dflt}\n"));
    for k in 0..n {
        body.push_str(&format!("end i32.const {} return\n", 100 + k));
    }
    body.push_str(&format!("end i32.const {}", 100 + n));
    let mut idx: Vec<u64> = (0..n as u64 + 3).collect();
    idx.extend([0x7FFF_FFFF, 0x8000_0000, 0xFFFF_FFFF, 0x1_0000_0000 - 2]);
    probe(
        &format!("table{n}_d{dflt}"),
        vec![T::I32],
        T::I32,
        &body,
        idx.into_iter().map(|x| vec![x]).collect(),
        move |v| {
            let i = w32(v[0]) as usize;
            let l = labels.get(i).copied().unwrap_or(dflt);
            ex32(100 + l as u32)
        },
    )
}

fn tables() -> Group {
    let mut probes = vec![table(1, 1), table(2, 0), table(5, 5), table(16, 3)];
    // Value-carrying targets, a value beneath them.
    probes.push(probe(
        "table_valued",
        vec![T::I32, T::I32],
        T::I32,
        "i32.const 1000
         block (result i32)
           block (result i32)
             block (result i32)
               local.get 1 local.get 0 br_table 0 1 2 1
             end i32.const 1 i32.add
           end i32.const 10 i32.add
         end
         i32.sub",
        {
            let mut v: Vec<Vec<u64>> = (0..6).map(|i| vec![i, 0x55]).collect();
            v.extend([0x7FFF_FFFF, 0x8000_0000, 0xFFFF_FFFF].map(|i| vec![i, 7]));
            v.extend(two("table_valued"));
            v
        },
        |v| {
            let b = w32(v[1]);
            let r = match w32(v[0]) {
                0 => b.wrapping_add(11),
                2 => b,
                _ => b.wrapping_add(10),
            };
            ex32(1000u32.wrapping_sub(r))
        },
    ));
    probes.push(probe(
        "table64",
        vec![T::I32, T::I64],
        T::I64,
        "block (result i64)
           block (result i64)
             local.get 1 local.get 0 br_table 0 1
           end i64.const 5 i64.mul
         end",
        {
            let mut v = Vec::new();
            for i in [0u64, 1, 2, 0xFFFF_FFFF] {
                for b in [3u64, u64::MAX, 0x8000_0000_0000_0001] {
                    v.push(vec![i, b]);
                }
            }
            v
        },
        |v| {
            Expect::Exactly(if w32(v[0]) == 0 {
                v[1].wrapping_mul(5)
            } else {
                v[1]
            })
        },
    ));
    Group::new("br_table", probes)
}

// --------------------------------------------------------- unreachable ----

fn traps() -> Group {
    Group::new(
        "unreachable",
        vec![
            // Index 0, 1, 2 reach the first, second and third `unreachable`
            // (in address order); 3 and above return 42.
            probe(
                "three_traps",
                vec![T::I32],
                T::I32,
                "block block block block
                   local.get 0 br_table 0 1 2 3
                 end unreachable
                 end unreachable
                 end unreachable
                 end i32.const 42",
                one("three_traps"),
                |v| match w32(v[0]) {
                    k @ 0..=2 => Expect::Trap(k as usize),
                    _ => Expect::Exactly(42),
                },
            )
            .with_ud2s(3),
            probe(
                "trap_in_arm",
                vec![T::I32],
                T::I32,
                "local.get 0 if (result i32) unreachable else i32.const 6 end",
                one("trap_in_arm"),
                |v| {
                    if w32(v[0]) != 0 {
                        Expect::Trap(0)
                    } else {
                        Expect::Exactly(6)
                    }
                },
            )
            .with_ud2s(1),
        ],
    )
}

// ---------------------------------------------------- the pinned shapes ----

/// Every integer export of `scripts/repro/if_arm_dead_value_1691.wat` (the
/// three #1691 shapes X86_PLAN names among them), and the "below entry
/// height" shapes: the fixture's `refuse_below` and cold review 1's
/// `below.wat` (`v1`, `v4`). Bodies copied verbatim.
const PINNED: &[(&str, &str, &str)] = &[
    (
        "t_i32_then",
        "i32",
        "i32.const 100 block (result i32) local.get 0 i32.eqz if i32.const 1 br 1 end i32.const 7 end i32.sub",
    ),
    (
        "t_i32_else",
        "i32",
        "i32.const 100 block (result i32) local.get 0 i32.eqz if nop else i32.const 1 br 1 end i32.const 7 end i32.sub",
    ),
    (
        "t_i32_both",
        "i32",
        "i32.const 100 block (result i32) local.get 0 i32.eqz if i32.const 1 br 1 else i32.const 2 br 1 end i32.const 7 end i32.sub",
    ),
    (
        "t_i32_nested",
        "i32",
        "i32.const 100 block (result i32) local.get 0 i32.eqz if block i32.const 1 br 2 end end i32.const 7 end i32.sub",
    ),
    (
        "t_i32_br_table",
        "i32",
        "i32.const 100 block (result i32) local.get 0 i32.eqz if i32.const 1 i32.const 0 br_table 1 end i32.const 7 end i32.sub",
    ),
    (
        "t_i32_unreachable",
        "i32",
        "i32.const 100 block (result i32) local.get 0 i32.eqz if i32.const 1 unreachable end i32.const 7 end i32.sub",
    ),
    (
        "t_i32_return_extra",
        "i32",
        "i32.const 100 block (result i32) local.get 0 i32.eqz if i32.const 9 i32.const 1 return end i32.const 7 end i32.sub",
    ),
    (
        "t_i32_void_target",
        "i32",
        "i32.const 100 block local.get 0 i32.eqz if i32.const 1 br 1 end end i32.const 7 i32.sub",
    ),
    (
        "t_i32_mismatch_then",
        "i32",
        "i32.const 100 block (result i32) local.get 0 i32.eqz if (result i32) i32.const 1 i32.const 2 br 1 else i32.const 7 end end i32.sub",
    ),
    (
        "t_i32_mismatch_else",
        "i32",
        "i32.const 100 block (result i32) local.get 0 i32.eqz if (result i32) i32.const 7 else i32.const 1 i32.const 2 br 1 end end i32.sub",
    ),
    (
        "t_i32_both_result",
        "i32",
        "i32.const 100 block (result i32) local.get 0 i32.eqz if (result i32) i32.const 1 br 1 else i32.const 2 i32.const 3 br 1 end end i32.sub",
    ),
    (
        "t_i32_loop_exit",
        "i32",
        "(local i32) i32.const 1000 block (result i32) loop (result i32) local.get 1 i32.const 1 i32.add local.set 1 local.get 1 local.get 0 i32.const 3 i32.add i32.eq if local.get 1 br 2 end br 0 end end i32.sub",
    ),
    (
        "t_i64_void_target",
        "i64",
        "i64.const 100 block local.get 0 i32.eqz if i64.const 1 br 1 end end i64.const 7 i64.sub",
    ),
    (
        "t_i64_beneath_i32_carried",
        "i64",
        "i64.const 100 block (result i32) local.get 0 i32.eqz if i32.const 1 br 1 end i32.const 7 end i64.extend_i32_u i64.sub",
    ),
    (
        "ctl_i32_arity_held",
        "i32",
        "i32.const 100 block (result i32) local.get 0 i32.eqz if (result i32) i32.const 1 br 1 else i32.const 7 end end i32.sub",
    ),
    (
        "ctl_i32_no_dead_arm",
        "i32",
        "i32.const 100 block (result i32) local.get 0 i32.const 1 br_if 0 drop i32.const 7 end i32.sub",
    ),
    (
        "refuse_below",
        "i32",
        "i32.const 100 block (result i32) local.get 0 i32.eqz if i32.const 1 br 1 drop drop end i32.const 7 end i32.sub",
    ),
    (
        "v1",
        "i32",
        "i32.const 100 block (result i32) i32.const 5 local.get 0 i32.eqz if i32.const 1 br 1 drop drop end i32.const 7 i32.add end i32.sub",
    ),
    (
        "v4",
        "i32",
        "i32.const 100 block local.get 0 i32.eqz if br 1 i32.const 9 i32.add drop end end i32.const 7 i32.sub",
    ),
];

/// The value (or trap) each pinned shape must give for `x`.
fn pinned_expect(name: &str, x: u32) -> Expect {
    let z = x == 0;
    let pick = |a: u32, b: u32| ex32(if z { a } else { b });
    match name {
        "t_i32_then"
        | "t_i32_nested"
        | "t_i32_br_table"
        | "ctl_i32_arity_held"
        | "refuse_below"
        | "t_i64_beneath_i32_carried" => pick(99, 93),
        "t_i32_else" => pick(93, 99),
        "t_i32_both" => pick(99, 98),
        "t_i32_unreachable" => {
            if z {
                Expect::Trap(0)
            } else {
                ex32(93)
            }
        }
        "t_i32_return_extra" => pick(1, 93),
        "t_i32_void_target" | "t_i64_void_target" | "v4" => ex32(93),
        "t_i32_mismatch_then" => pick(98, 93),
        "t_i32_mismatch_else" => pick(93, 98),
        "t_i32_both_result" => pick(99, 97),
        "t_i32_loop_exit" => ex32(1000u32.wrapping_sub(x.wrapping_add(3))),
        "ctl_i32_no_dead_arm" => ex32(100u32.wrapping_sub(x)),
        "v1" => pick(99, 88),
        other => panic!("no expectation for {other}"),
    }
}

fn pinned() -> Group {
    // Not 0x7fffffff: t_i32_loop_exit counts up to x + 3.
    let xs = [0u64, 1, 2, 5, 7, 100, 0xFFFF_FFFF];
    Group::new(
        "pinned shapes (#1691, below entry height)",
        PINNED
            .iter()
            .map(|&(name, result, body)| {
                let result = if result == "i64" { T::I64 } else { T::I32 };
                let p = probe(
                    name,
                    vec![T::I32],
                    result,
                    body,
                    xs.iter().map(|&x| vec![x]).collect(),
                    move |v| pinned_expect(name, w32(v[0])),
                );
                if name == "t_i32_unreachable" {
                    p.with_ud2s(1)
                } else {
                    p
                }
            })
            .collect(),
    )
}

/// The fixture's float exports: x86-64 lowers no float, so each is a NAMED
/// decline, never a panic and never an object.
const FLOAT_EXPORTS: &[(&str, &str, &str)] = &[
    (
        "t_f32_then",
        "f32",
        "f32.const 1 block (result f32) local.get 0 i32.eqz if f32.const 0 br 1 end local.get 0 f32.convert_i32_s f32.const 2 f32.mul end f32.sub",
    ),
    (
        "t_f32_void_target",
        "f32",
        "f32.const 1 block local.get 0 i32.eqz if f32.const 0.25 br 1 end end f32.const 2 f32.sub",
    ),
    (
        "t_f64_void_target",
        "f64",
        "f64.const 100 block local.get 0 i32.eqz if f64.const 1 br 1 end end f64.const 7 f64.sub",
    ),
    (
        "t_f64_beneath_f32_carried",
        "f64",
        "f64.const 100 block (result f32) local.get 0 i32.eqz if f32.const 0.25 br 1 end f32.const 2 end f64.promote_f32 f64.sub",
    ),
];

// ------------------------------------------------------------- harness ----

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("synth-oracle-x86-ctrl-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// Compile `wat` for x86-64. `Err` is synth's own refusal (its last line).
fn compile_x86(wat: &str) -> Result<(Vec<u8>, CompiledObject), String> {
    let wasm = wat::parse_str(wat).unwrap_or_else(|e| panic!("probe WAT: {e}\n{wat}"));
    let dir = scratch();
    let input = dir.join("m.wasm");
    std::fs::write(&input, &wasm).unwrap();
    let out = dir.join("m-x86_64.o");
    let run = compile(&input, FLAGS, &out).expect("synth runs");
    if !run.status.success() {
        assert!(
            !run.stderr.contains("panicked"),
            "synth PANICKED: {}",
            run.stderr
        );
        assert!(!out.exists(), "a refused compile wrote an object");
        return Err(run
            .stderr
            .lines()
            .rfind(|l| !l.trim().is_empty())
            .unwrap_or("(no stderr)")
            .to_string());
    }
    assert!(
        !run.stderr.to_lowercase().contains("skipping"),
        "synth printed a skip: {}",
        run.stderr
    );
    let obj = run.object.expect("object parsed");
    assert_eq!(obj.machine, Machine::X86_64);
    Ok((wasm, obj))
}

fn cfg() -> EmuConfig {
    EmuConfig::new(Cpu::X86_64Baseline)
}

fn run_vectors(
    label: &str,
    name: &str,
    params: &[T],
    vectors: &[Vec<u64>],
    wasm: &[u8],
    obj: &CompiledObject,
) -> Vec<Case> {
    assert_eq!(obj.relocs_in(name), 0, "`{name}` carries relocations");
    vectors
        .iter()
        .map(|v| {
            let args: Vec<WasmValue> = params.iter().zip(v).map(|(t, &b)| t.val(b)).collect();
            run_case(wasm, obj, name, &args, FUEL, &Imports::new(), &cfg())
                .unwrap_or_else(|e| panic!("{label} {name}{args:?}: harness error {e:?}"))
        })
        .collect()
}

/// The absolute addresses of the `ud2` instructions of `name`, in order (a
/// byte scan; [`judge`] checks the count against the probe's).
fn ud2_sites(obj: &CompiledObject, name: &str) -> Vec<u64> {
    let f = obj.func(name).unwrap();
    obj.function_bytes(name)
        .unwrap()
        .windows(2)
        .enumerate()
        .filter(|(_, w)| *w == [0x0F, 0x0B])
        .map(|(i, _)| TEXT_BASE + f.offset + i as u64)
        .collect()
}

/// Why this case is wrong, if it is.
fn judge(p: &Probe, c: &Case, v: &[u64], sites: &[u64]) -> Option<String> {
    if !c.verdict.is_agree() {
        return Some(format!("{:?}", c.verdict));
    }
    match ((p.expect)(v), &c.emulator) {
        (Expect::Exactly(want), EmuOutcome::Values(got)) => {
            (got != &vec![p.result.val(want)]).then(|| format!("expected {want:#x}"))
        }
        (Expect::Trap(k), EmuOutcome::Trap { pc, .. }) => {
            let class = match &c.reference {
                RefOutcome::Trap { class, .. } => Some(*class),
                _ => None,
            };
            if class != Some(TrapClass::Unreachable) {
                Some(format!("kiln's trap is {class:?}, not unreachable"))
            } else if sites.len() != p.ud2s {
                Some(format!(
                    "{} ud2 in the function, {} expected",
                    sites.len(),
                    p.ud2s
                ))
            } else if sites.get(k) != Some(pc) {
                Some(format!("trapped at {pc:#x}, not ud2 #{k} of {sites:x?}"))
            } else {
                None
            }
        }
        (want, got) => Some(format!("expected {want:?}, the emulator did {got:?}")),
    }
}

#[derive(Debug, Default, PartialEq, Eq)]
struct Tally {
    cases: usize,
    traps: usize,
}

/// Compile and run every group; every case has to AGREE and do what its probe
/// expects.
fn sweep(label: &str, groups: &[Group]) -> Tally {
    let mut declined = Vec::new();
    let mut bad = Vec::new();
    let mut tally = Tally::default();
    for g in groups {
        let (wasm, obj) = match compile_x86(&g.wat()) {
            Ok(x) => x,
            Err(e) => {
                declined.push(format!("  {}: {e}", g.label));
                continue;
            }
        };
        let mut n = 0;
        for p in &g.probes {
            let sites = ud2_sites(&obj, &p.name);
            let cases = run_vectors(&g.label, &p.name, &p.params, &p.vectors, &wasm, &obj);
            for (c, v) in cases.iter().zip(&p.vectors) {
                n += 1;
                if matches!((p.expect)(v), Expect::Trap(_)) {
                    tally.traps += 1;
                }
                if let Some(why) = judge(p, c, v, &sites) {
                    bad.push(format!(
                        "  {} {}{:x?}: {why} (ref {:?}, emu {:?})",
                        g.label, p.name, v, c.reference, c.emulator
                    ));
                }
            }
        }
        assert_eq!(n, g.cases());
        tally.cases += n;
    }
    for l in declined.iter().chain(bad.iter().take(40)) {
        eprintln!("{l}");
    }
    assert!(
        declined.is_empty() && bad.is_empty(),
        "x86_64-ctrl {label}: {} of {} groups did not compile, {} of {} cases are wrong",
        declined.len(),
        groups.len(),
        bad.len(),
        tally.cases
    );
    tally
}

// --------------------------------------------------------------- tests ----

#[test]
fn loops_agree_with_kiln_and_rust() {
    let t = sweep("loops", &[loops()]);
    assert_eq!(
        t,
        Tally {
            cases: 295,
            traps: 0
        }
    );
    eprintln!(
        "ORACLE x86_64-ctrl loops: {} cases agree over 6 probes",
        t.cases
    );
}

#[test]
fn nested_blocks_and_ifs_agree_with_kiln_and_rust() {
    let t = sweep("blocks", &[blocks(), ifs()]);
    assert_eq!(
        t,
        Tally {
            cases: 550,
            traps: 0
        }
    );
    eprintln!(
        "ORACLE x86_64-ctrl blocks and ifs: {} cases agree over 8 probes",
        t.cases
    );
}

#[test]
fn breaks_out_of_nested_loops_agree_with_kiln_and_rust() {
    let t = sweep("br out", &[break_out()]);
    assert_eq!(
        t,
        Tally {
            cases: 129,
            traps: 0
        }
    );
    eprintln!(
        "ORACLE x86_64-ctrl br out of nested loops: {} cases agree over 2 probes",
        t.cases
    );
}

#[test]
fn br_table_at_every_index_agrees_with_kiln_and_rust() {
    let t = sweep("br_table", &[tables()]);
    assert_eq!(
        t,
        Tally {
            cases: 170,
            traps: 0
        }
    );
    eprintln!(
        "ORACLE x86_64-ctrl br_table: {} cases agree over 6 probes, every index and 4 out-of-range",
        t.cases
    );
}

#[test]
fn unreachable_traps_at_its_own_ud2() {
    let t = sweep("unreachable", &[traps()]);
    assert_eq!(
        t,
        Tally {
            cases: 50,
            traps: 27
        }
    );
    eprintln!(
        "ORACLE x86_64-ctrl unreachable: {} cases agree, {} traps each on its own ud2",
        t.cases, t.traps
    );
}

#[test]
fn the_pinned_shapes_give_their_values() {
    let t = sweep("pinned", &[pinned()]);
    assert_eq!(
        t,
        Tally {
            cases: 133,
            traps: 1
        }
    );
    eprintln!(
        "ORACLE x86_64-ctrl pinned shapes: {} cases agree over 19 exports, each its exact value",
        t.cases
    );
}

/// The fixture's float exports are refused by name: the refusal names the
/// float type, no object is written, nothing panics (`compile_x86`).
#[test]
fn the_fixtures_float_shapes_are_named_declines() {
    for &(name, ty, body) in FLOAT_EXPORTS {
        let wat = format!("(module (func (export \"{name}\") (param i32) (result {ty}) {body}))");
        let e = compile_x86(&wat).expect_err(name);
        assert!(
            e.contains(&format!("has a {ty} parameter, result or local")),
            "{name}: {e}"
        );
    }
}

// -------------------------------------------------------------- random ----

/// What a label carries in the generated programs.
#[derive(Clone, Copy, PartialEq, Eq)]
enum L {
    /// A void block or if: a branch carries nothing.
    Void,
    /// A block, if or the function body with an i32 result.
    Val,
    /// A loop: never a random branch target (the counter back-edge is the
    /// only one), so every program terminates.
    Loop,
}

/// A generator of random, VALID, terminating structured programs over
/// i32: two parameters, four scratch locals (2..=5) and a fresh counter
/// local per loop.
struct Gen {
    r: Rng,
    labels: Vec<L>,
    counters: u32,
}

impl Gen {
    fn new(seed: &str) -> Self {
        Gen {
            r: Rng::new(seed),
            labels: vec![L::Val],
            counters: 0,
        }
    }

    fn pick(&mut self, n: u64) -> u64 {
        self.r.below(n)
    }

    /// A relative depth to a label of kind `want`, if one is visible.
    fn label(&mut self, want: L) -> Option<usize> {
        let ds: Vec<usize> = (0..self.labels.len())
            .filter(|&d| self.labels[self.labels.len() - 1 - d] == want)
            .collect();
        (!ds.is_empty()).then(|| ds[self.pick(ds.len() as u64) as usize])
    }

    fn konst(&mut self) -> String {
        let k = match self.pick(4) {
            0 => self.pick(8) as i64,
            1 => -(self.pick(4) as i64) - 1,
            2 => i64::from(i32::MIN) + self.pick(2) as i64,
            _ => self.r.next() as u32 as i32 as i64,
        };
        format!("i32.const {k}")
    }

    /// Dead code after an unconditional transfer: only pops and balanced
    /// pushes, so it validates against the polymorphic stack whatever the
    /// net count `net` (0 or 1) the context needs.
    fn junk(&mut self, net: u8) -> String {
        let s = match self.pick(5) {
            0 => "",
            1 => "drop drop",
            2 => "i32.const 3 drop",
            3 => "unreachable",
            _ => "br 0",
        };
        match (net, self.pick(2)) {
            (1, 0) => format!("{s} i32.const 11"),
            _ => s.to_string(),
        }
    }

    fn cond(&mut self, d: u32) -> String {
        match self.pick(3) {
            0 => format!("{} i32.const 3 i32.and", self.expr(d)),
            1 => format!("{} {} i32.lt_s", self.expr(d), self.expr(d)),
            _ => self.expr(d),
        }
    }

    /// Code that pushes exactly one i32.
    fn expr(&mut self, d: u32) -> String {
        let choice = if d == 0 { self.pick(2) } else { self.pick(12) };
        match choice {
            0 => self.konst(),
            1 => format!("local.get {}", self.pick(6)),
            2 | 3 => {
                let op = [
                    "add", "sub", "xor", "mul", "and", "or", "shl", "shr_u", "rotl", "lt_u", "eq",
                    "ne",
                ][self.pick(12) as usize];
                format!("{} {} i32.{op}", self.expr(d - 1), self.expr(d - 1))
            }
            4 => {
                self.labels.push(L::Val);
                let body = self.stmts(d - 1);
                let early = if self.pick(2) == 0 {
                    format!("{} {} br_if 0 drop", self.expr(d - 1), self.cond(d - 1))
                } else {
                    String::new()
                };
                let v = self.expr(d - 1);
                self.labels.pop();
                format!("block (result i32) {body} {early} {v} end")
            }
            5 => {
                let c = self.cond(d - 1);
                self.labels.push(L::Val);
                let a = format!("{} {}", self.stmts(d - 1), self.expr(d - 1));
                let b = format!("{} {}", self.stmts(d - 1), self.expr(d - 1));
                self.labels.pop();
                format!("{c} if (result i32) {a} else {b} end")
            }
            6 => {
                // A value-carrying br_table over two result blocks.
                self.labels.push(L::Val);
                self.labels.push(L::Val);
                let v = self.expr(d - 1);
                let i = self.expr(d - 1);
                let n = 1 + self.pick(5);
                let ts: Vec<String> = (0..n).map(|_| self.pick(2).to_string()).collect();
                let dflt = self.pick(2);
                self.labels.pop();
                let k = self.konst();
                self.labels.pop();
                format!(
                    "block (result i32) block (result i32) {v} {i} br_table {} {dflt} end {k} i32.add end",
                    ts.join(" ")
                )
            }
            7 => format!(
                "{} {} {} select",
                self.expr(d - 1),
                self.expr(d - 1),
                self.cond(d - 1)
            ),
            8 => {
                // A value-carrying br_if to any visible valued label (the
                // function body included): its value stays when not taken.
                let t = self.label(L::Val).expect("the function body is valued");
                format!("{} {} br_if {t}", self.expr(d - 1), self.cond(d - 1))
            }
            9 => {
                // An unconditional branch or return with a value, then dead
                // code.
                let v = self.expr(d - 1);
                let j = self.junk(1);
                if self.pick(3) == 0 {
                    format!("{v} return {j}")
                } else {
                    let t = self.label(L::Val).expect("valued");
                    format!("{v} br {t} {j}")
                }
            }
            10 => {
                // Seven operands live at once: spills, then a fold.
                let vs: Vec<String> = (0..7).map(|_| self.expr(0)).collect();
                format!("{} {}", vs.join(" "), "i32.add ".repeat(6))
            }
            _ => format!("{} {}", self.stmts(d - 1), self.expr(d - 1)),
        }
    }

    /// Code with no net effect on the stack.
    fn stmts(&mut self, d: u32) -> String {
        let n = if d == 0 { self.pick(2) } else { self.pick(3) };
        (0..n).map(|_| self.stmt(d)).collect::<Vec<_>>().join(" ")
    }

    fn stmt(&mut self, d: u32) -> String {
        match self.pick(if d == 0 { 3 } else { 10 }) {
            0 => format!("{} local.set {}", self.expr(d), 2 + self.pick(4)),
            1 => match self.label(L::Void) {
                Some(t) => format!("{} br_if {t}", self.cond(d)),
                None => String::new(),
            },
            2 => {
                // A rarely-taken trap.
                format!(
                    "local.get {} i32.const 255 i32.and i32.const 7 i32.eq if unreachable end",
                    self.pick(2)
                )
            }
            3 => {
                let c = self.cond(d - 1);
                self.labels.push(L::Void);
                let a = self.stmts(d - 1);
                let b = self.stmts(d - 1);
                self.labels.pop();
                if self.pick(2) == 0 {
                    format!("{c} if {a} end")
                } else {
                    format!("{c} if {a} else {b} end")
                }
            }
            4 => {
                self.labels.push(L::Void);
                let a = self.stmts(d - 1);
                self.labels.pop();
                format!("block {a} end")
            }
            5 => {
                // A counted loop: 1..=4 iterations of its body.
                let c = 6 + self.counters;
                self.counters += 1;
                let n = 1 + self.pick(4);
                self.labels.push(L::Loop);
                let body = self.stmts(d - 1);
                self.labels.pop();
                format!(
                    "i32.const {n} local.set {c} loop {body} local.get {c} i32.const 1 i32.sub local.tee {c} br_if 0 end"
                )
            }
            6 => match self.label(L::Void) {
                Some(t) => {
                    let j = self.junk(0);
                    format!("br {t} {j}")
                }
                None => String::new(),
            },
            7 => {
                // A void br_table over two fresh blocks and any visible void
                // labels beyond them.
                self.labels.push(L::Void);
                self.labels.push(L::Void);
                let i = self.expr(d - 1);
                let n = 1 + self.pick(6);
                let mut ts = Vec::new();
                for _ in 0..=n {
                    ts.push(self.label(L::Void).expect("two are open").to_string());
                }
                self.labels.pop();
                let a = self.stmts(d - 1);
                self.labels.pop();
                format!("block block {i} br_table {} end {a} end", ts.join(" "))
            }
            8 => format!("{} drop", self.expr(d)),
            _ => {
                let j = self.junk(0);
                format!("{} return {j}", self.expr(d - 1))
            }
        }
    }

    fn function(&mut self, name: &str) -> String {
        self.labels = vec![L::Val];
        self.counters = 0;
        let body = format!("{} {}", self.stmts(3), self.expr(3));
        let locals = "i32 ".repeat(4 + self.counters as usize);
        format!(
            "  (func (export \"{name}\") (param i32 i32) (result i32) (local {locals}) {body})\n"
        )
    }
}

const RANDOM_MODULES: usize = 40;
const RANDOM_FUNCS: usize = 5;
const RANDOM_VECTORS: usize = 8;

#[test]
fn random_structured_programs_agree_with_kiln() {
    let mut cases = 0;
    let mut traps = 0;
    let mut values = 0;
    let mut bad = Vec::new();
    // How often each construct occurs in the generated text, so a generator
    // change that stops emitting one is visible (exact, below).
    let words = [
        "block",
        "loop",
        "if",
        "else",
        "br",
        "br_if",
        "br_table",
        "return",
        "unreachable",
        "select",
    ];
    let mut seen = [0usize; 10];
    for m in 0..RANDOM_MODULES {
        let mut g = Gen::new(&format!("x86-ctrl-random/{m}"));
        let mut wat = String::from("(module\n");
        for f in 0..RANDOM_FUNCS {
            wat.push_str(&g.function(&format!("f{f}")));
        }
        wat.push_str(")\n");
        for tok in wat.split_whitespace() {
            if let Some(k) = words.iter().position(|w| *w == tok) {
                seen[k] += 1;
            }
        }
        let wasm = wat::parse_str(&wat).unwrap_or_else(|e| panic!("generator: {e}\n{wat}"));
        wasmparser::validate(&wasm).unwrap_or_else(|e| panic!("generator: invalid {e}\n{wat}"));
        let (wasm, obj) = compile_x86(&wat).unwrap_or_else(|e| panic!("module {m}: {e}\n{wat}"));
        let mut r = Rng::new(&format!("x86-ctrl-random/{m}/vectors"));
        let edge = [0u64, 1, 7, 0x8000_0007, 0xFFFF_FFFF];
        for f in 0..RANDOM_FUNCS {
            let name = format!("f{f}");
            let vectors: Vec<Vec<u64>> = (0..RANDOM_VECTORS)
                .map(|i| {
                    if i < edge.len() {
                        vec![edge[i], edge[(i + 2) % edge.len()]]
                    } else {
                        vec![r.next() & 0xFFFF_FFFF, r.next() & 0xFFFF_FFFF]
                    }
                })
                .collect();
            let cs = run_vectors("random", &name, &[T::I32, T::I32], &vectors, &wasm, &obj);
            for (c, v) in cs.iter().zip(&vectors) {
                cases += 1;
                match &c.emulator {
                    EmuOutcome::Trap { .. } => traps += 1,
                    EmuOutcome::Values(_) => values += 1,
                    _ => {}
                }
                if !c.verdict.is_agree() {
                    bad.push(format!("  module {m} {name}{v:x?}: {:?}", c.verdict));
                }
            }
        }
    }
    for l in bad.iter().take(20) {
        eprintln!("{l}");
    }
    assert!(
        bad.is_empty(),
        "{} of {cases} random cases disagree",
        bad.len()
    );
    assert_eq!(
        (cases, values, traps),
        (1600, 1480, 120),
        "the random population moved"
    );
    eprintln!(
        "random constructs: {:?}",
        words.iter().zip(seen).collect::<Vec<_>>()
    );
    assert_eq!(
        seen,
        [646, 72, 360, 170, 150, 291, 225, 118, 195, 118],
        "the generated constructs moved"
    );
    eprintln!(
        "ORACLE x86_64-ctrl random programs: {cases} cases agree over {RANDOM_MODULES} modules, {traps} traps on ud2"
    );
}

// ------------------------------------------------------------- potency ----

/// The wrong cases of one probe when the emulator runs `obj`, judged
/// against the `ud2` sites of the UNPATCHED object `orig`.
fn wrong(g: &Group, name: &str, obj: &CompiledObject, orig: &CompiledObject) -> Vec<Vec<u64>> {
    let wasm = wat::parse_str(g.wat()).unwrap();
    let p = g.probes.iter().find(|p| p.name == name).unwrap();
    let sites = ud2_sites(orig, name);
    run_vectors(&g.label, name, &p.params, &p.vectors, &wasm, obj)
        .iter()
        .zip(&p.vectors)
        .filter(|(c, v)| judge(p, c, v, &sites).is_some())
        .map(|(_, v)| v.clone())
        .collect()
}

fn patched(obj: &CompiledObject, name: &str, at: usize, with: &[u8]) -> CompiledObject {
    let f = obj.func(name).unwrap().clone();
    let mut bad = obj.clone();
    let start = f.offset as usize + at;
    bad.text[start..start + with.len()].copy_from_slice(with);
    bad
}

/// Offsets in `name` where `pred` holds over a window of `n` bytes.
fn find_all(
    obj: &CompiledObject,
    name: &str,
    n: usize,
    pred: impl Fn(&[u8]) -> bool,
) -> Vec<usize> {
    obj.function_bytes(name)
        .unwrap()
        .windows(n)
        .enumerate()
        .filter(|(_, w)| pred(w))
        .map(|(i, _)| i)
        .collect()
}

/// The `if`'s skip branch inverted (`je` to `jne`): the then arm runs
/// exactly when the condition is zero. Every vector whose two results differ
/// (3b != b) reds, and no other.
#[test]
fn potency_an_inverted_if_reds_exactly_where_the_arms_differ() {
    let g = ifs();
    let (_, obj) = compile_x86(&g.wat()).unwrap();
    let je = find_all(&obj, "if_no_else", 2, |w| w == [0x0F, 0x84]);
    assert_eq!(je.len(), 1, "one je in if_no_else");
    let bad = patched(&obj, "if_no_else", je[0], &[0x0F, 0x85]);
    let p = &g.probes[0];
    let want: Vec<Vec<u64>> = p
        .vectors
        .iter()
        .filter(|v| w32(v[1]).wrapping_mul(3) != w32(v[1]))
        .cloned()
        .collect();
    assert!(want.len() > 60);
    assert_eq!(wrong(&g, "if_no_else", &bad, &obj), want);
    assert!(wrong(&g, "if_no_else", &obj, &obj).is_empty());
}

/// The second `unreachable`'s `ud2` overwritten with a nop: index 1 then
/// runs on into the third `ud2` — a trap, but at the wrong site. Exactly the
/// index-1 vector reds.
#[test]
fn potency_a_trap_at_the_wrong_ud2_reds() {
    let g = traps();
    let (_, obj) = compile_x86(&g.wat()).unwrap();
    let sites = find_all(&obj, "three_traps", 2, |w| w == [0x0F, 0x0B]);
    assert_eq!(sites.len(), 3);
    let bad = patched(&obj, "three_traps", sites[1], &[0x66, 0x90]);
    assert_eq!(wrong(&g, "three_traps", &bad, &obj), vec![vec![1]]);
    assert!(wrong(&g, "three_traps", &obj, &obj).is_empty());
}

/// One `br_table` compare's immediate changed from 1 to 2 (`cmpl $1` to
/// `cmpl $2`) in the 5-target table. The first compare that matches wins, so
/// index 1 now falls to the default and index 2 takes entry 1's label: the
/// wrong set is computed from that rule, and it is exactly those two.
#[test]
fn potency_a_wrong_br_table_compare_reds_where_the_dispatch_moves() {
    let g = tables();
    let name = "table5_d5";
    let (_, obj) = compile_x86(&g.wat()).unwrap();
    // `cmpl $imm8, %r32`: [REX] 83 /7 ib, ModRM 11 111 rrr.
    let cmps = find_all(&obj, name, 3, |w| w[0] == 0x83 && w[1] & 0xF8 == 0xF8);
    let imms: Vec<u8> = cmps
        .iter()
        .map(|&i| obj.function_bytes(name).unwrap()[i + 2])
        .collect();
    assert_eq!(imms, [0, 1, 2, 3, 4], "one compare per target, in order");
    let bad = patched(&obj, name, cmps[1] + 2, &[2]);
    let labels: Vec<usize> = (0..5).map(|i| (3 * i + 1) % 6).collect();
    let imm = [0u32, 2, 2, 3, 4];
    let p = g.probes.iter().find(|p| p.name == name).unwrap();
    let want: Vec<Vec<u64>> = p
        .vectors
        .iter()
        .filter(|v| {
            let i = w32(v[0]);
            let now = imm.iter().position(|&k| k == i).map_or(5, |e| labels[e]);
            let was = labels.get(i as usize).copied().unwrap_or(5);
            now != was
        })
        .cloned()
        .collect();
    assert_eq!(want, vec![vec![1], vec![2]]);
    assert_eq!(wrong(&g, name, &bad, &obj), want);
    assert!(wrong(&g, name, &obj, &obj).is_empty());
}
