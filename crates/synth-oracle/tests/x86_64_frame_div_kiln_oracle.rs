//! RQ-91-X86FRAME (Refs #1741): the x86-64 frame, locals, spilled operand
//! stack, division and bit counts against kiln — lanes X3 and X4.
//!
//! Every probe is compiled by synth with `-b x86_64 --relocatable` and run,
//! as the bytes synth emitted, on unicorn x86-64 (CPU model pinned to QEMU64;
//! SysV arguments with POISONED upper halves; poisoned scratch registers,
//! flags and stack; callee-saved registers, `rsp`, the direction flag and the
//! caller's frame checked; no store below the red zone) and on kiln. Every
//! case has to AGREE.
//!
//! WHAT IS ASKED BEYOND AGREEMENT, because agreement alone could be two
//! engines both returning a value:
//! - DIVISION: for every case the test computes, from the operands and with
//!   no engine, whether wasm traps and why (a zero divisor; `INT_MIN / -1`
//!   for `div_s`). kiln's trap class and the emulator's outcome must both
//!   match that. An emulator trap is a `ud2` at RIP (the runner's rule; a
//!   `#DE` from `div`/`idiv` is ILLEGAL, never a trap), and it must be the
//!   RIGHT `ud2`: the function's first for a zero divisor, its second for the
//!   overflow. The trap counts are exact literals;
//! - `rem_s(INT_MIN, -1)` is 0 and `clz(0)`/`ctz(0)` are the operand width,
//!   as literals;
//! - a local READ BEFORE IT IS WRITTEN is 0, as a literal, on a stack whose
//!   every byte is poison;
//! - for the bit counts, the locals and the spill probes the expected VALUE
//!   is computed here too (Rust's `leading_zeros`, a stack machine over the
//!   same op list), so both engines are checked against a third answer.
//!
//! OPERAND SHAPES. i32 operands arrive with garbage in bits 63:32 in three
//! ways, each a probe shape: a poisoned i32 argument register (`pp`), a
//! wrapped i64 PARAMETER (`ww`, `w`), and a wrapped i64 TEMPORARY (`wt`: the
//! X2 review's F1 shape, where the value never passes through a 32-bit
//! load). A value is also taken through a SPILL slot and back before it is
//! consumed (`sp`, `ws`), since a spill moves all 64 bits.
//!
//! RED ON THE BASE (lane X2, 3ad771f1): all 17 tests fail there. 21 of the
//! 22 groups are refused with `unsupported wasm op`, `non-parameter local`
//! or `more than 3 temporaries at once`; the 22nd (six parameters, each
//! returned on its own) is within lane X2 and compiles.
//!
//! The small harness below (types, edge values, the seeded stream) repeats
//! the one in `x86_64_alu_kiln_oracle.rs`; integration tests share no module.
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

    fn bits(self) -> u32 {
        match self {
            T::I32 => 32,
            T::I64 => 64,
        }
    }

    /// `bits` truncated to this type's width.
    fn mask(self, bits: u64) -> u64 {
        match self {
            T::I32 => bits & 0xFFFF_FFFF,
            T::I64 => bits,
        }
    }

    fn int_min(self) -> u64 {
        1 << (self.bits() - 1)
    }

    fn minus_one(self) -> u64 {
        self.mask(u64::MAX)
    }

    fn val(self, bits: u64) -> WasmValue {
        match self {
            T::I32 => WasmValue::I32(bits as u32),
            T::I64 => WasmValue::I64(bits),
        }
    }

    fn edges(self) -> &'static [u64] {
        match self {
            T::I32 => EDGE32,
            T::I64 => EDGE64,
        }
    }
}

/// i32 edge values: 0, ±1, both ends, and divisors around them.
const EDGE32: &[u64] = &[
    0,
    1,
    2,
    3,
    7,
    10,
    0x7F,
    0x80,
    0xFF,
    0xFFFF,
    0x1_0000,
    0x3FFF_FFFF,
    0x4000_0000,
    0x7FFF_FFFE,
    0x7FFF_FFFF,
    0x8000_0000,
    0x8000_0001,
    0xC000_0000,
    0xFFFF_FFF9,
    0xFFFF_FFFD,
    0xFFFF_FFFE,
    0xFFFF_FFFF,
];

/// i64 edge values: the same, and both ends of 32 bits.
const EDGE64: &[u64] = &[
    0,
    1,
    2,
    3,
    7,
    10,
    0xFFFF,
    0x7FFF_FFFF,
    0x8000_0000,
    0xFFFF_FFFF,
    0x1_0000_0000,
    0x4000_0000_0000_0000,
    0x7FFF_FFFF_FFFF_FFFE,
    0x7FFF_FFFF_FFFF_FFFF,
    0x8000_0000_0000_0000,
    0x8000_0000_0000_0001,
    0xC000_0000_0000_0000,
    0xFFFF_FFFF_0000_0000,
    0xFFFF_FFFF_8000_0000,
    0xFFFF_FFFF_FFFF_FFF9,
    0xFFFF_FFFF_FFFF_FFFE,
    0xFFFF_FFFF_FFFF_FFFF,
];

const RANDOM_FULL: usize = 40;
const RANDOM_SLICE: usize = 16;

/// splitmix64: a fixed, seedable stream.
struct Rng(u64);

impl Rng {
    fn new(seed: &str) -> Self {
        // FNV-1a over the seed text, so each (op, shape) has its own stream.
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
}

/// What wasm does with one case, computed here from the operands alone.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Expect {
    /// Returns a value (which one is kiln's to say).
    Value,
    /// Returns exactly this value.
    Exactly(u64),
    /// Traps on a zero divisor: the function's FIRST `ud2`.
    DivideByZero,
    /// Traps on `INT_MIN / -1`: the function's SECOND `ud2`.
    Overflow,
}

type ExpectFn = Box<dyn Fn(&[u64]) -> Expect>;

/// One exported function: its signature, its body (declared locals
/// included), the argument vectors it runs over (raw bits, one per
/// parameter) and what each vector must do.
struct Probe {
    name: String,
    params: Vec<T>,
    result: T,
    body: String,
    vectors: Vec<Vec<u64>>,
    expect: ExpectFn,
}

impl Probe {
    fn new(name: &str, params: Vec<T>, result: T, body: String, vectors: Vec<Vec<u64>>) -> Self {
        Probe {
            name: name.to_string(),
            params,
            result,
            body,
            vectors,
            expect: Box::new(|_| Expect::Value),
        }
    }

    fn expecting(mut self, f: impl Fn(&[u64]) -> Expect + 'static) -> Self {
        self.expect = Box::new(f);
        self
    }
}

/// A module of probes.
struct Group {
    op: String,
    probes: Vec<Probe>,
}

impl Group {
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
                "  (func (export \"{}\") {params} (result {}) {})\n",
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

/// Every pair of edge values, then seeded random pairs.
fn full_pairs(t: T, seed: &str) -> Vec<Vec<u64>> {
    let e = t.edges();
    let mut v = Vec::new();
    for &a in e {
        for &b in e {
            v.push(vec![a, b]);
        }
    }
    let mut r = Rng::new(seed);
    for _ in 0..RANDOM_FULL {
        v.push(vec![r.next(), r.next()]);
    }
    v
}

/// A fixed slice: each edge value paired with another (every value appears on
/// both sides), then seeded random tuples. `n` values per vector; slots past
/// the second are random.
fn slice(t: T, n: usize, seed: &str) -> Vec<Vec<u64>> {
    let e = t.edges();
    let mut r = Rng::new(seed);
    let mut v = Vec::new();
    for i in 0..e.len() {
        let mut row = vec![e[i], e[(5 * i + 3) % e.len()]];
        row.truncate(n);
        while row.len() < n {
            row.push(r.next());
        }
        v.push(row);
    }
    for _ in 0..RANDOM_SLICE {
        v.push((0..n).map(|_| r.next()).collect());
    }
    v
}

/// The division-relevant pairs — every combination of {0, 1, -1, INT_MIN,
/// INT_MAX, 7} on both sides — then seeded random pairs.
fn div_pairs(t: T, seed: &str) -> Vec<Vec<u64>> {
    let k = [0, 1, t.minus_one(), t.int_min(), t.int_min() - 1, 7];
    let mut v = Vec::new();
    for a in k {
        for b in k {
            v.push(vec![a, b]);
        }
    }
    let mut r = Rng::new(seed);
    for _ in 0..RANDOM_SLICE {
        v.push(vec![r.next(), r.next()]);
    }
    v
}

/// `v` with a seeded NONZERO upper half over each i32 value: the argument of
/// a probe whose i32 operand is a wrapped i64.
fn widen(v: Vec<Vec<u64>>, seed: &str) -> Vec<Vec<u64>> {
    let mut r = Rng::new(seed);
    v.into_iter()
        .map(|row| {
            row.into_iter()
                .map(|x| {
                    let hi = (r.next() >> 32) | 1;
                    (hi << 32) | (x & 0xFFFF_FFFF)
                })
                .collect()
        })
        .collect()
}

fn get(i: u32) -> String {
    format!("local.get {i}")
}

/// Parameter `i` through an op that leaves it in a TEMPORARY (`x + 0`).
fn temp(t: T, i: u32) -> String {
    format!("local.get {i} {0}.const 0 {0}.add", t.s())
}

/// An i64 parameter wrapped to i32: the register keeps the i64's upper half.
fn wrapped(i: u32) -> String {
    format!("local.get {i} i32.wrap_i64")
}

/// An i64 TEMPORARY wrapped to i32 (`x + 0` as i64, then `wrap`): nothing
/// between the 64-bit add and the consumer zeroes the upper half.
fn wrapped_temp(i: u32) -> String {
    format!("local.get {i} i64.const 0 i64.add i32.wrap_i64")
}

/// Six constants pushed above what is already on the stack, then dropped:
/// with six temporaries this SPILLS up to six values beneath them and loads
/// each back when it is next popped.
fn bury() -> String {
    let mut s = String::new();
    for k in 1..=6 {
        s.push_str(&format!(" i32.const {k}"));
    }
    s.push_str(&" drop".repeat(6));
    s
}

// ------------------------------------------------------------ division ----

/// What `a OP b` does, from the operands alone.
fn div_expect(op: &str, t: T, a: u64, b: u64) -> Expect {
    let (a, b) = (t.mask(a), t.mask(b));
    if b == 0 {
        Expect::DivideByZero
    } else if a == t.int_min() && b == t.minus_one() {
        match op {
            "div_s" => Expect::Overflow,
            // The case x86 `idiv` faults on and wasm defines.
            "rem_s" => Expect::Exactly(0),
            _ => Expect::Value,
        }
    } else {
        Expect::Value
    }
}

/// One division op in every operand shape. Each probe holds exactly ONE
/// divide, so its `ud2` sites are known: the zero-divisor trap first, then
/// (for `div_s` only) the overflow trap.
fn division(name: &str, t: T) -> Group {
    let op = format!("{}.{name}", t.s());
    let o = op.as_str();
    let ts = t.s();
    let seed = |shape: &str| format!("{op}/{shape}");
    let ex = |ia: usize, ib: usize| {
        let name = name.to_string();
        move |v: &[u64]| div_expect(&name, t, v[ia], v[ib])
    };
    // For a probe that computes on with the divide's result: whether it
    // traps, and which trap, but not the value.
    let ex_trap = |ia: usize, ib: usize| {
        let name = name.to_string();
        move |v: &[u64]| match div_expect(&name, t, v[ia], v[ib]) {
            Expect::Exactly(_) => Expect::Value,
            other => other,
        }
    };
    let lit = |k: u64| match t {
        T::I32 => format!("i32.const {}", k as u32 as i32),
        T::I64 => format!("i64.const {}", k as i64),
    };
    let mut probes = vec![
        Probe::new(
            "pp",
            vec![t; 2],
            t,
            format!("{} {} {o}", get(0), get(1)),
            full_pairs(t, &seed("pp")),
        )
        .expecting(ex(0, 1)),
        Probe::new(
            "rv",
            vec![t; 2],
            t,
            format!("{} {} {o}", get(1), get(0)),
            div_pairs(t, &seed("rv")),
        )
        .expecting(ex(1, 0)),
        Probe::new(
            "tt",
            vec![t; 2],
            t,
            format!("{} {} {o}", temp(t, 0), temp(t, 1)),
            div_pairs(t, &seed("tt")),
        )
        .expecting(ex(0, 1)),
        Probe::new(
            "sq",
            vec![t; 1],
            t,
            format!("{} {} {o}", get(0), get(0)),
            slice(t, 1, &seed("sq")),
        )
        .expecting(ex(0, 0)),
        // A third value live in a temporary across the divide (which writes
        // rax and rdx), read back afterwards.
        Probe::new(
            "live",
            vec![t; 3],
            t,
            format!("{} {} {} {o} {ts}.xor", get(2), get(0), get(1)),
            div_pairs(t, &seed("live"))
                .into_iter()
                .enumerate()
                .map(|(i, v)| {
                    vec![
                        v[0],
                        v[1],
                        0x9E37_79B9_7F4A_7C15u64.wrapping_mul(i as u64 + 1),
                    ]
                })
                .collect(),
        )
        .expecting(ex_trap(0, 1)),
        // Both operands SPILLED and loaded back before the divide.
        Probe::new(
            "sp",
            vec![t; 2],
            t,
            format!("{} {}{} {o}", get(0), get(1), bury()),
            div_pairs(t, &seed("sp")),
        )
        .expecting(ex(0, 1)),
        // Six values under the divide's operands, folded in afterwards: the
        // divide runs with spilled values below it.
        Probe::new(
            "deep",
            vec![t; 2],
            t,
            format!(
                "{g0} {g1} {g0} {g1} {g0} {g1} {g0} {g1} {o} \
                 {ts}.add {ts}.xor {ts}.add {ts}.xor {ts}.add {ts}.xor",
                g0 = get(0),
                g1 = get(1)
            ),
            div_pairs(t, &seed("deep")),
        )
        .expecting(ex_trap(0, 1)),
    ];
    // Constant divisors (0 always traps) and constant dividends.
    for (n, k) in [0, 1, 2, 7, t.minus_one(), t.int_min()]
        .into_iter()
        .enumerate()
    {
        let name2 = name.to_string();
        probes.push(
            Probe::new(
                &format!("kb{n}"),
                vec![t],
                t,
                format!("{} {} {o}", get(0), lit(k)),
                slice(t, 1, &seed(&format!("kb{n}"))),
            )
            .expecting(move |v| div_expect(&name2, t, v[0], k)),
        );
        let name2 = name.to_string();
        probes.push(
            Probe::new(
                &format!("ka{n}"),
                vec![t],
                t,
                format!("{} {} {o}", lit(k), get(0)),
                slice(t, 1, &seed(&format!("ka{n}"))),
            )
            .expecting(move |v| div_expect(&name2, t, k, v[0])),
        );
    }
    if t == T::I32 {
        // i32 operands whose registers hold a nonzero upper half: a divisor
        // that is zero in its LOW half only must trap; -1 and INT_MIN are
        // recognised in the low half only.
        for (shape, a, b) in [
            ("ww", wrapped(0), wrapped(1)),
            ("wt", wrapped_temp(0), wrapped_temp(1)),
            (
                "ws",
                wrapped_temp(0),
                format!("{}{}", wrapped_temp(1), bury()),
            ),
        ] {
            probes.push(
                Probe::new(
                    shape,
                    vec![T::I64; 2],
                    t,
                    format!("{a} {b} {o}"),
                    widen(div_pairs(t, &seed(shape)), &seed(shape)),
                )
                .expecting(ex(0, 1)),
            );
        }
    }
    Group { op, probes }
}

const DIVS: &[&str] = &["div_s", "div_u", "rem_s", "rem_u"];

fn division_groups(t: T) -> Vec<Group> {
    DIVS.iter().map(|o| division(o, t)).collect()
}

// ---------------------------------------------------------- bit counts ----

/// Every single bit, every low mask, every high mask, the edges, and seeded
/// random values.
fn bit_values(t: T, seed: &str) -> Vec<u64> {
    let mut v: Vec<u64> = t.edges().to_vec();
    for k in 0..t.bits() {
        let bit = 1u64 << k;
        v.push(bit);
        v.push(bit - 1);
        v.push(t.mask(!(bit - 1)));
        v.push(t.mask(bit | 1));
    }
    let mut r = Rng::new(seed);
    for _ in 0..RANDOM_FULL {
        v.push(t.mask(r.next()));
    }
    v
}

fn bit_expect(name: &str, t: T, x: u64) -> Expect {
    let x = t.mask(x);
    let w = u64::from(t.bits());
    Expect::Exactly(match (name, t) {
        ("clz", T::I32) => u64::from((x as u32).leading_zeros()),
        ("clz", T::I64) => u64::from(x.leading_zeros()),
        ("ctz", _) if x == 0 => w,
        ("ctz", _) => u64::from(x.trailing_zeros()),
        ("popcnt", _) => u64::from(x.count_ones()),
        other => unreachable!("{other:?}"),
    })
}

/// One bit-count op: the operand loaded from a parameter slot, in a
/// temporary, through a spill slot, from the sixth parameter, and (i32) as a
/// wrapped i64 in each of those ways. The expected value is computed here
/// (`leading_zeros` and friends), so kiln and the emulator are both checked
/// against a third answer.
fn bit_count(name: &str, t: T) -> Group {
    let op = format!("{}.{name}", t.s());
    let o = op.as_str();
    let seed = |shape: &str| format!("{op}/{shape}");
    let one = |shape: &str| -> Vec<Vec<u64>> {
        bit_values(t, &seed(shape))
            .into_iter()
            .map(|x| vec![x])
            .collect()
    };
    let ex = |at: usize| {
        let name = name.to_string();
        move |v: &[u64]| bit_expect(&name, t, v[at])
    };
    let mut probes = vec![
        Probe::new("p", vec![t], t, format!("{} {o}", get(0)), one("p")).expecting(ex(0)),
        Probe::new("t", vec![t], t, format!("{} {o}", temp(t, 0)), one("t")).expecting(ex(0)),
        Probe::new(
            "sp",
            vec![t],
            t,
            format!("{}{} {o}", get(0), bury()),
            one("sp"),
        )
        .expecting(ex(0)),
        Probe::new("p5", vec![t; 6], t, format!("{} {o}", get(5)), {
            let mut r = Rng::new(&seed("p5/pad"));
            one("p5")
                .into_iter()
                .map(|x| {
                    let mut row: Vec<u64> = (0..5).map(|_| r.next()).collect();
                    row.push(x[0]);
                    row
                })
                .collect()
        })
        .expecting(ex(5)),
    ];
    if t == T::I32 {
        for (shape, a) in [
            ("w", wrapped(0)),
            ("wt", wrapped_temp(0)),
            ("ws", format!("{}{}", wrapped_temp(0), bury())),
        ] {
            probes.push(
                Probe::new(
                    shape,
                    vec![T::I64],
                    t,
                    format!("{a} {o}"),
                    widen(one(shape), &seed(shape)),
                )
                .expecting(ex(0)),
            );
        }
    }
    Group { op, probes }
}

fn bit_count_groups() -> Vec<Group> {
    let mut v = Vec::new();
    for t in [T::I32, T::I64] {
        for name in ["clz", "ctz", "popcnt"] {
            v.push(bit_count(name, t));
        }
    }
    v
}

// -------------------------------------------------------------- locals ----

fn tuples(t: T, n: usize, seed: &str) -> Vec<Vec<u64>> {
    slice(t, n.max(1), seed)
        .into_iter()
        .map(|mut v| {
            v.truncate(n);
            v
        })
        .collect()
}

/// Locals that are read before any write. Each must read 0; the runner's
/// stack is poison in every byte, so a slot that was not zeroed (or an i64
/// slot zeroed in its low half only) reads `0xFEEDFACE_DEADBEEF`.
fn unwritten_locals() -> Group {
    let mut probes = Vec::new();
    let zero = |_: &[u64]| Expect::Exactly(0);
    // (declared locals, the local read, its type)
    for (n, (decl, at, t)) in [
        ("i32", 1, T::I32),
        ("i64", 1, T::I64),
        ("i32 i64 i32 i64", 2, T::I64),
        ("i32 i64 i32 i64", 3, T::I32),
        ("i32 i64 i32 i64", 4, T::I64),
        (
            "i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64",
            18,
            T::I64,
        ),
    ]
    .into_iter()
    .enumerate()
    {
        probes.push(
            Probe::new(
                &format!("z{n}"),
                vec![T::I64],
                t,
                format!("(local {decl}) local.get {at}"),
                tuples(T::I64, 1, &format!("locals/z{n}")),
            )
            .expecting(zero),
        );
    }
    // No parameter at all, and the same after other locals were written.
    probes.push(
        Probe::new(
            "z_np",
            vec![],
            T::I64,
            "(local i64 i64) local.get 1".into(),
            vec![vec![]],
        )
        .expecting(zero),
    );
    probes.push(
        Probe::new(
            "z_after",
            vec![T::I64],
            T::I64,
            "(local i64 i64 i64) local.get 0 local.set 1 local.get 0 local.set 3 local.get 2"
                .into(),
            tuples(T::I64, 1, "locals/z_after"),
        )
        .expecting(zero),
    );
    // An unwritten local used in arithmetic: x + 0 + 0 is x.
    probes.push(
        Probe::new(
            "z_sum",
            vec![T::I32],
            T::I32,
            "(local i32 i32) local.get 1 local.get 0 i32.add local.get 2 i32.add".into(),
            tuples(T::I32, 1, "locals/z_sum"),
        )
        .expecting(|v| Expect::Exactly(v[0] & 0xFFFF_FFFF)),
    );
    Group {
        op: "locals.unwritten".into(),
        probes,
    }
}

/// Six parameters of alternating width, each returned on its own: a
/// parameter homed to the wrong slot, or at the wrong width, returns another
/// parameter's bits or poison.
fn six_params() -> Group {
    let params = vec![T::I32, T::I64, T::I32, T::I64, T::I32, T::I64];
    let mut r = Rng::new("locals/p6");
    let mut vectors: Vec<Vec<u64>> = (0..24)
        .map(|_| (0..6).map(|_| r.next()).collect())
        .collect();
    vectors.push(vec![0; 6]);
    vectors.push(vec![u64::MAX; 6]);
    let mut probes = Vec::new();
    for (k, &t) in params.iter().enumerate() {
        probes.push(
            Probe::new(
                &format!("p{k}"),
                params.clone(),
                t,
                get(k as u32),
                vectors.clone(),
            )
            .expecting(move |v| Expect::Exactly(t.mask(v[k]))),
        );
    }
    // All six at once, i32 ones zero-extended: every slot is read.
    probes.push(Probe::new(
        "all",
        params.clone(),
        T::I64,
        "local.get 0 i64.extend_i32_u local.get 1 i64.const 3 i64.mul i64.add \
         local.get 2 i64.extend_i32_s i64.const 5 i64.mul i64.xor \
         local.get 3 i64.const 7 i64.mul i64.add \
         local.get 4 i64.extend_i32_u i64.const 11 i64.mul i64.xor \
         local.get 5 i64.const 13 i64.mul i64.add"
            .into(),
        vectors,
    ));
    Group {
        op: "locals.six_params".into(),
        probes,
    }
}

/// `local.set`, `local.tee`, a write under a value already on the stack, a
/// swap through a third local, and a ten-step recurrence held in locals.
fn set_and_tee(t: T) -> Group {
    let ts = t.s();
    let seed = |n: &str| format!("locals.{ts}/{n}");
    let p = |name: &str, body: String, ex: fn(T, &[u64]) -> u64| {
        Probe::new(name, vec![t; 2], t, body, slice(t, 2, &seed(name)))
            .expecting(move |v| Expect::Exactly(t.mask(ex(t, v))))
    };
    let mut fib = format!("(local {ts} {ts}) local.get 0 local.set 2 local.get 1 local.set 3");
    for _ in 0..10 {
        // (l2, l3) = (l3, l2 + l3)
        fib.push_str(&format!(
            " local.get 3 local.get 2 local.get 3 {ts}.add local.set 3 local.set 2"
        ));
    }
    fib.push_str(" local.get 3");
    let probes = vec![
        p(
            "set",
            "local.get 1 local.set 0 local.get 0".into(),
            |_, v| v[1],
        ),
        p(
            "tee",
            format!("local.get 1 local.tee 0 local.get 0 {ts}.add"),
            |_, v| v[1].wrapping_mul(2),
        ),
        // The OLD value of local 0 is on the stack when it is overwritten.
        p(
            "alias",
            format!("local.get 0 local.get 1 local.set 0 local.get 0 {ts}.sub"),
            |_, v| v[0].wrapping_sub(v[1]),
        ),
        p(
            "alias_tee",
            format!("local.get 0 local.get 1 local.tee 0 {ts}.sub local.get 0 {ts}.xor"),
            |_, v| v[0].wrapping_sub(v[1]) ^ v[1],
        ),
        p(
            "swap",
            format!(
                "(local {ts}) local.get 0 local.set 2 local.get 1 local.set 0 \
                 local.get 2 local.set 1 local.get 0 local.get 1 {ts}.sub"
            ),
            |_, v| v[1].wrapping_sub(v[0]),
        ),
        // F(11) and F(10) of the recurrence: 55 a + 89 b.
        p("fib", fib, |_, v| {
            v[0].wrapping_mul(55).wrapping_add(v[1].wrapping_mul(89))
        }),
    ];
    Group {
        op: format!("locals.{ts}"),
        probes,
    }
}

/// Twenty-four locals, so slots on both sides of the 8-bit displacement
/// boundary (`-0x80(%rbp)` is the sixteenth slot): each is written a distinct
/// value and all are read back, rotated by their index.
fn many_locals(t: T) -> Group {
    let ts = t.s();
    const N: u32 = 24;
    let mut body = format!("(local{})", format!(" {ts}").repeat(N as usize));
    for i in 1..=N {
        body.push_str(&format!(
            " local.get 0 {ts}.const {} {ts}.mul local.set {i}",
            2 * i + 1
        ));
    }
    body.push_str(" local.get 0");
    for i in 1..=N {
        body.push_str(&format!(" local.get {i} {ts}.const {i} {ts}.rotl {ts}.xor"));
    }
    let probe = Probe::new(
        "many",
        vec![t],
        t,
        body,
        tuples(t, 1, &format!("locals.many.{ts}")),
    )
    .expecting(move |v| {
        let x = t.mask(v[0]);
        let mut acc = x;
        for i in 1..=N {
            let y = t.mask(x.wrapping_mul(u64::from(2 * i + 1)));
            acc ^= match t {
                T::I32 => u64::from((y as u32).rotate_left(i)),
                T::I64 => y.rotate_left(i),
            };
        }
        Expect::Exactly(acc)
    });
    Group {
        op: format!("locals.many.{ts}"),
        probes: vec![probe],
    }
}

/// THE i32 UPPER-HALF RULE through every path lanes X3-X4 add (the X2
/// review's F1): `i64.extend_i32_u` must give the low half ZERO-extended —
/// and `extend_i32_s` the low half sign-extended — whatever the upper half of
/// the i32's register or slot holds.
fn upper_half() -> Group {
    let lo = |v: &[u64]| Expect::Exactly(v[0] & 0xFFFF_FFFF);
    let sx = |v: &[u64]| Expect::Exactly(v[0] as u32 as i32 as i64 as u64);
    let v64 = |n: &str| -> Vec<Vec<u64>> {
        let mut v: Vec<Vec<u64>> = EDGE64.iter().map(|&x| vec![x]).collect();
        let mut r = Rng::new(&format!("upper/{n}"));
        for _ in 0..RANDOM_FULL {
            v.push(vec![r.next()]);
        }
        v
    };
    let mut probes = Vec::new();
    let mut add = |name: &str, param: T, body: String, ex: fn(&[u64]) -> Expect| {
        probes.push(Probe::new(name, vec![param], T::I64, body, v64(name)).expecting(ex));
    };
    // A poisoned i32 ARGUMENT, homed and loaded.
    add("arg_u", T::I32, "local.get 0 i64.extend_i32_u".into(), lo);
    add("arg_s", T::I32, "local.get 0 i64.extend_i32_s".into(), sx);
    // A wrapped i64 parameter and a wrapped i64 TEMPORARY (F1's probe).
    add(
        "w_u",
        T::I64,
        format!("{} i64.extend_i32_u", wrapped(0)),
        lo,
    );
    add(
        "wt_u",
        T::I64,
        format!("{} i64.extend_i32_u", wrapped_temp(0)),
        lo,
    );
    add(
        "wt_s",
        T::I64,
        format!("{} i64.extend_i32_s", wrapped_temp(0)),
        sx,
    );
    // ... through a spill slot (which keeps all 64 bits) and back.
    add(
        "ws_u",
        T::I64,
        format!("{}{} i64.extend_i32_u", wrapped_temp(0), bury()),
        lo,
    );
    add(
        "ws_s",
        T::I64,
        format!("{}{} i64.extend_i32_s", wrapped_temp(0), bury()),
        sx,
    );
    // ... through an i32 LOCAL, by set and by tee.
    add(
        "wl_u",
        T::I64,
        format!(
            "(local i32) {} local.set 1 local.get 1 i64.extend_i32_u",
            wrapped_temp(0)
        ),
        lo,
    );
    add(
        "wtee_u",
        T::I64,
        format!(
            "(local i32) {} local.tee 1 i64.extend_i32_u",
            wrapped_temp(0)
        ),
        lo,
    );
    // ... through an i32 local that is then read TWICE.
    add(
        "wp_u",
        T::I64,
        format!(
            "(local i32) {} local.set 1 local.get 1 i64.extend_i32_u local.get 1 i64.extend_i32_s i64.xor",
            wrapped_temp(0)
        ),
        |v| Expect::Exactly((v[0] & 0xFFFF_FFFF) ^ (v[0] as u32 as i32 as i64 as u64)),
    );
    // An i32 consumer that is not an extension: eqz and a compare see the
    // low half only.
    probes.push(
        Probe::new(
            "ws_eqz",
            vec![T::I64],
            T::I32,
            format!("{}{} i32.eqz", wrapped_temp(0), bury()),
            v64("ws_eqz"),
        )
        .expecting(|v| Expect::Exactly(u64::from(v[0] & 0xFFFF_FFFF == 0))),
    );
    probes.push(
        Probe::new(
            "ws_lt",
            vec![T::I64],
            T::I32,
            format!("{}{} i32.const 1 i32.lt_u", wrapped_temp(0), bury()),
            v64("ws_lt"),
        )
        .expecting(|v| Expect::Exactly(u64::from(v[0] & 0xFFFF_FFFF == 0))),
    );
    Group {
        op: "upper_half".into(),
        probes,
    }
}

fn local_groups() -> Vec<Group> {
    vec![
        unwritten_locals(),
        six_params(),
        set_and_tee(T::I32),
        set_and_tee(T::I64),
        many_locals(T::I32),
        many_locals(T::I64),
        upper_half(),
    ]
}

// -------------------------------------------------------------- spills ----

const FOLD: &[&str] = &["sub", "xor", "mul", "sub", "add", "rotl"];

/// `n` values pushed, then folded from the top with a cycle of ops in which
/// position matters. Value `i` is parameter 0, parameter 1 or a constant.
fn deep(t: T, n: usize) -> (String, impl Fn(&[u64]) -> Expect + 'static) {
    let ts = t.s();
    let konst = move |i: usize| t.mask(0x9E37_79B9_7F4A_7C15u64.wrapping_mul(i as u64 + 1));
    let mut body = String::new();
    for i in 0..n {
        match i % 3 {
            0 => body.push_str(" local.get 0"),
            1 => body.push_str(" local.get 1"),
            _ => body.push_str(&match t {
                T::I32 => format!(" i32.const {}", konst(i) as u32 as i32),
                T::I64 => format!(" i64.const {}", konst(i) as i64),
            }),
        }
    }
    for k in 0..n - 1 {
        body.push_str(&format!(" {ts}.{}", FOLD[k % FOLD.len()]));
    }
    let ex = move |v: &[u64]| {
        let mut stack: Vec<u64> = (0..n)
            .map(|i| match i % 3 {
                0 => t.mask(v[0]),
                1 => t.mask(v[1]),
                _ => konst(i),
            })
            .collect();
        for k in 0..n - 1 {
            let b = stack.pop().unwrap();
            let a = stack.pop().unwrap();
            let r = match (FOLD[k % FOLD.len()], t) {
                ("sub", _) => a.wrapping_sub(b),
                ("xor", _) => a ^ b,
                ("mul", _) => a.wrapping_mul(b),
                ("add", _) => a.wrapping_add(b),
                ("rotl", T::I32) => u64::from((a as u32).rotate_left(b as u32 & 31)),
                ("rotl", T::I64) => a.rotate_left((b & 63) as u32),
                other => unreachable!("{other:?}"),
            };
            stack.push(t.mask(r));
        }
        Expect::Exactly(stack[0])
    };
    (body, ex)
}

/// Operand stacks deeper than the six temporaries. The expected value of
/// every probe is computed here, by a stack machine over the same op list.
fn spills(t: T) -> Group {
    let ts = t.s();
    let seed = |n: &str| format!("spill.{ts}/{n}");
    let mut probes = Vec::new();
    // 6 fits the temporaries exactly (no spill): the control beside 7.
    for n in [6, 7, 8, 9, 13, 20, 40] {
        let (body, ex) = deep(t, n);
        let name = format!("deep{n}");
        probes
            .push(Probe::new(&name, vec![t; 2], t, body, slice(t, 2, &seed(&name))).expecting(ex));
    }
    let two = |name: &str, body: String, ex: fn(T, &[u64]) -> u64| {
        Probe::new(name, vec![t; 2], t, body, slice(t, 2, &seed(name)))
            .expecting(move |v| Expect::Exactly(t.mask(ex(t, v))))
    };
    // Each consumer with BOTH operands loaded back from spill slots.
    probes.push(two(
        "sub",
        format!("local.get 0 local.get 1{} {ts}.sub", bury()),
        |_, v| v[0].wrapping_sub(v[1]),
    ));
    probes.push(two(
        "shl",
        format!("local.get 0 local.get 1{} {ts}.shl", bury()),
        |t, v| t.mask(v[0]) << (v[1] & u64::from(t.bits() - 1)),
    ));
    // A spilled value DROPPED (its slot freed with no load), then the slot
    // reused by a second burial.
    probes.push(two(
        "drop",
        format!(
            "local.get 0 local.get 1{} drop local.get 1{} drop {ts}.const 3 {ts}.mul",
            bury(),
            bury()
        ),
        |_, v| v[0].wrapping_mul(3),
    ));
    // `return` with spilled values still under the result.
    probes.push(two(
        "ret",
        format!("local.get 1 local.get 1 local.get 0{} return", bury()),
        |_, v| v[0],
    ));
    // Spill slots sit below the locals and must not overwrite them: two
    // locals are written, a deep stack is built and folded, and the locals
    // are read again.
    {
        let (body, ex) = deep(t, 12);
        probes.push(
            Probe::new(
                "locals",
                vec![t; 2],
                t,
                format!(
                    "(local {ts} {ts}) local.get 0 {ts}.const 3 {ts}.mul local.set 2 \
                     local.get 1 {ts}.const 5 {ts}.mul local.set 3 {body} \
                     local.get 2 {ts}.add local.get 3 {ts}.xor"
                ),
                slice(t, 2, &seed("locals")),
            )
            .expecting(move |v| {
                let Expect::Exactly(d) = ex(v) else {
                    unreachable!()
                };
                Expect::Exactly(
                    t.mask(d.wrapping_add(v[0].wrapping_mul(3)) ^ t.mask(v[1].wrapping_mul(5))),
                )
            }),
        );
    }
    // A compare and a select whose operands all come back from spill slots.
    probes.push(
        Probe::new(
            "lt_s",
            vec![t; 2],
            T::I32,
            format!("local.get 0 local.get 1{} {ts}.lt_s", bury()),
            slice(t, 2, &seed("lt_s")),
        )
        .expecting(move |v| {
            Expect::Exactly(u64::from(match t {
                T::I32 => (v[0] as i32) < (v[1] as i32),
                T::I64 => (v[0] as i64) < (v[1] as i64),
            }))
        }),
    );
    {
        const CONDS: &[u64] = &[0, 1, 0x100, 0x8000_0000];
        let mut vectors = Vec::new();
        for row in slice(t, 2, &seed("select")) {
            for &c in CONDS {
                vectors.push(vec![row[0], row[1], c]);
            }
        }
        probes.push(
            Probe::new(
                "select",
                vec![t, t, T::I32],
                t,
                format!("local.get 0 local.get 1 local.get 2{} select", bury()),
                vectors,
            )
            .expecting(move |v| {
                Expect::Exactly(t.mask(if v[2] & 0xFFFF_FFFF != 0 { v[0] } else { v[1] }))
            }),
        );
    }
    Group {
        op: format!("spill.{ts}"),
        probes,
    }
}

// ------------------------------------------------------------- harness ----

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("synth-oracle-x86-frame-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// Compile `wat` for x86-64. `Err` is synth's own refusal.
fn compile_x86(wat: &str) -> Result<(Vec<u8>, CompiledObject), String> {
    let wasm = wat::parse_str(wat).unwrap_or_else(|e| panic!("probe WAT: {e}\n{wat}"));
    let dir = scratch();
    let input = dir.join("m.wasm");
    std::fs::write(&input, &wasm).unwrap();
    let out = dir.join("m-x86_64.o");
    let run = compile(&input, FLAGS, &out).expect("synth runs");
    if !run.status.success() {
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

fn args_of(p: &Probe, v: &[u64]) -> Vec<WasmValue> {
    p.params.iter().zip(v).map(|(t, &b)| t.val(b)).collect()
}

fn run_probe(g: &Group, p: &Probe, wasm: &[u8], obj: &CompiledObject) -> Vec<Case> {
    assert_eq!(
        obj.relocs_in(&p.name),
        0,
        "`{}` carries relocations",
        p.name
    );
    p.vectors
        .iter()
        .map(|v| {
            let args = args_of(p, v);
            run_case(wasm, obj, &p.name, &args, FUEL, &Imports::new(), &cfg())
                .unwrap_or_else(|e| panic!("{} {}{args:?}: harness error {e:?}", g.op, p.name))
        })
        .collect()
}

/// The absolute addresses of the `ud2` instructions of `name`, in order.
/// (A byte scan: the probes that rely on it hold one divide and no constant
/// whose bytes spell `0F 0B`, and the callers check the count.)
fn ud2_sites(obj: &CompiledObject, name: &str) -> Vec<u64> {
    let f = obj.func(name).unwrap();
    let body = obj.function_bytes(name).unwrap();
    body.windows(2)
        .enumerate()
        .filter(|(_, w)| *w == [0x0F, 0x0B])
        .map(|(i, _)| TEXT_BASE + f.offset + i as u64)
        .collect()
}

/// Why this case is wrong, if it is: the two engines have to agree, and both
/// must do what `expect` says.
fn judge(p: &Probe, c: &Case, v: &[u64], sites: &[u64]) -> Option<String> {
    if !c.verdict.is_agree() {
        return Some(format!("{:?}", c.verdict));
    }
    let class = match &c.reference {
        RefOutcome::Trap { class, .. } => Some(*class),
        _ => None,
    };
    match ((p.expect)(v), &c.emulator) {
        (Expect::Value, EmuOutcome::Values(_)) => None,
        (Expect::Exactly(want), EmuOutcome::Values(got)) => {
            (got != &vec![p.result.val(want)]).then(|| format!("expected {want:#x}"))
        }
        (Expect::DivideByZero, EmuOutcome::Trap { pc, .. }) => {
            if class != Some(TrapClass::IntegerDivideByZero) {
                Some(format!("kiln's trap is {class:?}, not a divide by zero"))
            } else if sites.first() != Some(pc) {
                Some(format!(
                    "trapped at {pc:#x}, not the first ud2 of {sites:x?}"
                ))
            } else {
                None
            }
        }
        (Expect::Overflow, EmuOutcome::Trap { pc, .. }) => {
            if class != Some(TrapClass::IntegerOverflow) {
                Some(format!("kiln's trap is {class:?}, not an overflow"))
            } else if sites.get(1) != Some(pc) {
                Some(format!(
                    "trapped at {pc:#x}, not the second ud2 of {sites:x?}"
                ))
            } else {
                None
            }
        }
        (want, got) => Some(format!("expected {want:?}, the emulator did {got:?}")),
    }
}

#[derive(Default, Debug, PartialEq, Eq)]
struct Tally {
    cases: usize,
    zero_traps: usize,
    overflow_traps: usize,
}

/// Compile and run every group; every case has to agree and do what its probe
/// expects. Returns the exact counts.
fn sweep(label: &str, groups: &[Group]) -> Tally {
    let mut declined = Vec::new();
    let mut bad = Vec::new();
    let mut tally = Tally::default();
    for g in groups {
        let (wasm, obj) = match compile_x86(&g.wat()) {
            Ok(x) => x,
            Err(e) => {
                declined.push(format!("  {}: {e}", g.op));
                continue;
            }
        };
        let mut n = 0;
        for p in &g.probes {
            let sites = ud2_sites(&obj, &p.name);
            for (c, v) in run_probe(g, p, &wasm, &obj).iter().zip(&p.vectors) {
                n += 1;
                match (p.expect)(v) {
                    Expect::DivideByZero => tally.zero_traps += 1,
                    Expect::Overflow => tally.overflow_traps += 1,
                    Expect::Value | Expect::Exactly(_) => {}
                }
                if let Some(why) = judge(p, c, v, &sites) {
                    bad.push(format!(
                        "  {} {}{:x?}: {why} (ref {:?}, emu {:?})",
                        g.op, p.name, v, c.reference, c.emulator
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
        "x86_64-frame {label}: {} of {} groups did not compile, {} of {} cases are wrong",
        declined.len(),
        groups.len(),
        bad.len(),
        tally.cases
    );
    tally
}

/// Every division probe holds one divide: one `ud2`, or two for `div_s`.
#[test]
fn every_division_probe_has_its_trap_sites() {
    let mut checked = 0;
    for t in [T::I32, T::I64] {
        for g in division_groups(t) {
            let (_, obj) = compile_x86(&g.wat()).unwrap_or_else(|e| panic!("{}: {e}", g.op));
            let want = if g.op.ends_with("div_s") { 2 } else { 1 };
            for p in &g.probes {
                let sites = ud2_sites(&obj, &p.name);
                assert_eq!(sites.len(), want, "{} {}: {sites:x?}", g.op, p.name);
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 4 * (19 + 3) + 4 * 19);
}

#[test]
fn i32_division_agrees_with_kiln_trap_for_trap() {
    let groups = division_groups(T::I32);
    assert_eq!(groups.len(), 4);
    let t = sweep("i32 division", &groups);
    assert_eq!(
        t,
        Tally {
            cases: 5736,
            zero_traps: 460,
            overflow_traps: 11
        },
        "counts moved"
    );
    eprintln!(
        "ORACLE x86_64-frame i32 division: {} cases agree over 4 ops, {} divide-by-zero and {} overflow traps on their ud2",
        t.cases, t.zero_traps, t.overflow_traps
    );
}

#[test]
fn i64_division_agrees_with_kiln_trap_for_trap() {
    let groups = division_groups(T::I64);
    assert_eq!(groups.len(), 4);
    let t = sweep("i64 division", &groups);
    assert_eq!(
        t,
        Tally {
            cases: 5112,
            zero_traps: 388,
            overflow_traps: 8
        },
        "counts moved"
    );
    eprintln!(
        "ORACLE x86_64-frame i64 division: {} cases agree over 4 ops, {} divide-by-zero and {} overflow traps on their ud2",
        t.cases, t.zero_traps, t.overflow_traps
    );
}

#[test]
fn bit_counts_agree_with_kiln_and_with_rust() {
    let groups = bit_count_groups();
    assert_eq!(groups.len(), 6);
    let t = sweep("bit counts", &groups);
    assert_eq!(t.zero_traps + t.overflow_traps, 0);
    assert_eq!(t.cases, 7806, "case count moved");
    eprintln!(
        "ORACLE x86_64-frame bit counts: {} cases agree over 6 ops",
        t.cases
    );
}

#[test]
fn locals_and_parameter_homing_agree_with_kiln() {
    let groups = local_groups();
    assert_eq!(groups.len(), 7);
    let t = sweep("locals", &groups);
    assert_eq!(t.zero_traps + t.overflow_traps, 0);
    assert_eq!(t.cases, 1763, "case count moved");
    eprintln!(
        "ORACLE x86_64-frame locals: {} cases agree over 7 groups",
        t.cases
    );
}

#[test]
fn spilled_operand_stacks_agree_with_kiln() {
    let groups = [spills(T::I32), spills(T::I64)];
    let t = sweep("spills", &groups);
    assert_eq!(t.zero_traps + t.overflow_traps, 0);
    assert_eq!(t.cases, 1292, "case count moved");
    eprintln!(
        "ORACLE x86_64-frame spills: {} cases agree over 2 groups",
        t.cases
    );
}

/// The named edge cases, as literals on both engines.
#[test]
fn the_named_edge_cases_hold() {
    let run = |g: &Group, probe: &str, v: &[u64]| -> Case {
        let (wasm, obj) = compile_x86(&g.wat()).unwrap_or_else(|e| panic!("{}: {e}", g.op));
        let p = g.probes.iter().find(|p| p.name == probe).unwrap();
        let args = args_of(p, v);
        run_case(&wasm, &obj, probe, &args, FUEL, &Imports::new(), &cfg()).unwrap()
    };
    for t in [T::I32, T::I64] {
        let (min, m1) = (t.int_min(), t.minus_one());
        // INT_MIN rem_s -1 is 0 and does not fault.
        let c = run(&division("rem_s", t), "pp", &[min, m1]);
        assert_eq!(c.reference, RefOutcome::Values(vec![t.val(0)]));
        assert_eq!(c.emulator, EmuOutcome::Values(vec![t.val(0)]));
        // INT_MIN div_s -1 traps with an overflow, on a ud2.
        let c = run(&division("div_s", t), "pp", &[min, m1]);
        assert!(
            matches!(
                c.reference,
                RefOutcome::Trap {
                    class: TrapClass::IntegerOverflow,
                    ..
                }
            ),
            "{:?}",
            c.reference
        );
        assert!(
            matches!(&c.emulator, EmuOutcome::Trap { insn, .. } if insn == "ud2"),
            "{:?}",
            c.emulator
        );
        // INT_MIN div_u -1 and INT_MIN rem_u -1 are ordinary values.
        for (op, want) in [("div_u", 0), ("rem_u", min)] {
            let c = run(&division(op, t), "pp", &[min, m1]);
            assert_eq!(c.emulator, EmuOutcome::Values(vec![t.val(want)]), "{op}");
            assert!(c.verdict.is_agree());
        }
        // Every divide traps on a zero divisor, with a divide-by-zero.
        for op in DIVS {
            let c = run(&division(op, t), "pp", &[min, 0]);
            assert!(
                matches!(
                    c.reference,
                    RefOutcome::Trap {
                        class: TrapClass::IntegerDivideByZero,
                        ..
                    }
                ),
                "{op}: {:?}",
                c.reference
            );
            assert!(matches!(c.emulator, EmuOutcome::Trap { .. }), "{op}");
        }
        // clz(0) and ctz(0) are the width; popcnt(-1) too.
        let w = u64::from(t.bits());
        for (op, x) in [("clz", 0), ("ctz", 0), ("popcnt", m1)] {
            let c = run(&bit_count(op, t), "p", &[x]);
            assert_eq!(c.reference, RefOutcome::Values(vec![t.val(w)]), "{op}");
            assert_eq!(c.emulator, EmuOutcome::Values(vec![t.val(w)]), "{op}");
        }
    }
}

// ---------------------------------------------------------------- potency --

/// The wrong cases of one probe when the emulator runs `obj` (kiln runs the
/// group's own module).
fn wrong(g: &Group, probe: &str, obj: &CompiledObject) -> Vec<Vec<u64>> {
    let wasm = wat::parse_str(g.wat()).unwrap();
    let p = g.probes.iter().find(|p| p.name == probe).unwrap();
    let sites = ud2_sites(obj, probe);
    run_probe(g, p, &wasm, obj)
        .iter()
        .zip(&p.vectors)
        .filter(|(c, v)| judge(p, c, v, &sites).is_some())
        .map(|(_, v)| v.clone())
        .collect()
}

/// `obj` with `len` bytes at `at` (relative to `name`) replaced by `with`.
fn patched(obj: &CompiledObject, name: &str, at: usize, with: &[u8]) -> CompiledObject {
    let f = obj.func(name).unwrap().clone();
    let mut bad = obj.clone();
    let start = f.offset as usize + at;
    bad.text[start..start + with.len()].copy_from_slice(with);
    bad
}

/// The offset of the `n`th occurrence of `needle` in `name`.
fn find(obj: &CompiledObject, name: &str, needle: &[u8], n: usize) -> usize {
    obj.function_bytes(name)
        .unwrap()
        .windows(needle.len())
        .enumerate()
        .filter(|(_, w)| *w == needle)
        .map(|(i, _)| i)
        .nth(n)
        .unwrap_or_else(|| panic!("no occurrence {n} of {needle:02x?} in `{name}`"))
}

const NOP2: [u8; 2] = [0x66, 0x90];

/// The zero-divisor guard's `ud2` overwritten with a 2-byte nop: the divide
/// then runs with a zero divisor and the CPU raises #DE. That is ILLEGAL, not
/// a trap — every zero-divisor vector reds, and no other.
#[test]
fn potency_a_removed_zero_guard_is_a_fault_not_a_trap() {
    for (name, t) in [("div_u", T::I32), ("rem_s", T::I64)] {
        let g = division(name, t);
        let (_, obj) = compile_x86(&g.wat()).unwrap();
        let bad = patched(&obj, "pp", find(&obj, "pp", &[0x0F, 0x0B], 0), &NOP2);
        let p = &g.probes[0];
        let zero: Vec<Vec<u64>> = p
            .vectors
            .iter()
            .filter(|v| t.mask(v[1]) == 0)
            .cloned()
            .collect();
        assert_eq!(zero.len(), 22);
        assert_eq!(wrong(&g, "pp", &bad), zero, "{name}");
        assert!(wrong(&g, "pp", &obj).is_empty());
    }
}

/// The overflow guard's `ud2` overwritten: `idiv` runs on `INT_MIN / -1` and
/// faults. Exactly that one pair reds.
#[test]
fn potency_a_removed_overflow_guard_reds_on_int_min_over_minus_one() {
    for t in [T::I32, T::I64] {
        let g = division("div_s", t);
        let (_, obj) = compile_x86(&g.wat()).unwrap();
        let bad = patched(&obj, "pp", find(&obj, "pp", &[0x0F, 0x0B], 1), &NOP2);
        assert_eq!(
            wrong(&g, "pp", &bad),
            vec![vec![t.int_min(), t.minus_one()]]
        );
    }
}

/// `rem_s`: the `xorl %eax, %eax` that replaces the dividend when the divisor
/// is -1 overwritten with a nop. `idiv` then divides INT_MIN by -1 and
/// faults; every other dividend still gives remainder 0, so exactly one pair
/// reds.
#[test]
fn potency_rem_s_by_minus_one_needs_its_zeroed_dividend() {
    for t in [T::I32, T::I64] {
        let g = division("rem_s", t);
        let (_, obj) = compile_x86(&g.wat()).unwrap();
        // `xorl %eax, %eax` = 31 C0; the only one in `pp`.
        let bad = patched(&obj, "pp", find(&obj, "pp", &[0x31, 0xC0], 0), &NOP2);
        assert_eq!(
            wrong(&g, "pp", &bad),
            vec![vec![t.int_min(), t.minus_one()]]
        );
    }
}

/// The two traps are told apart: with the zero guard's branch inverted
/// (`jne` to `je`), a NONZERO divisor reaches the first `ud2`. Agreement on
/// "both trapped" is not enough — the site and kiln's class are compared — so
/// every vector reds: nonzero divisors trap where kiln returns, and zero
/// divisors run into the divide.
#[test]
fn potency_an_inverted_zero_guard_reds_everywhere() {
    let g = division("div_s", T::I32);
    let (_, obj) = compile_x86(&g.wat()).unwrap();
    // The first `jne rel32` = 0F 85.
    let at = find(&obj, "pp", &[0x0F, 0x85], 0);
    let bad = patched(&obj, "pp", at, &[0x0F, 0x84]);
    assert_eq!(wrong(&g, "pp", &bad).len(), g.probes[0].vectors.len());
}

/// A planted wrong REFERENCE: kiln runs `div_u` for the compiled `div_s`.
/// The overflow pair reds (kiln returns, synth traps) and so does every pair
/// whose signed and unsigned quotients differ.
#[test]
fn potency_a_signedness_swap_in_the_reference_reds() {
    let g = division("div_s", T::I32);
    let (_, obj) = compile_x86(&g.wat()).unwrap();
    let planted = wat::parse_str(g.wat().replace("i32.div_s", "i32.div_u")).unwrap();
    let p = &g.probes[0];
    let got = p
        .vectors
        .iter()
        .filter(|v| {
            !run_case(
                &planted,
                &obj,
                "pp",
                &args_of(p, v),
                FUEL,
                &Imports::new(),
                &cfg(),
            )
            .unwrap()
            .verdict
            .is_agree()
        })
        .count();
    let expect = p
        .vectors
        .iter()
        .filter(|v| {
            let (a, b) = (v[0] as u32, v[1] as u32);
            b != 0
                && ((a == 0x8000_0000 && b == u32::MAX)
                    || (a as i32).wrapping_div(b as i32) as u32 != a / b)
        })
        .count();
    assert!(
        expect > 200,
        "the vectors barely separate the two ({expect})"
    );
    assert_eq!(got, expect);
}

/// `clz`: the `cmov` that supplies the zero-input answer overwritten with a
/// 3-byte nop. `bsr` of zero leaves no defined value; exactly the zero input
/// reds.
#[test]
fn potency_clz_of_zero_needs_its_cmov() {
    let g = bit_count("clz", T::I32);
    let (_, obj) = compile_x86(&g.wat()).unwrap();
    // `cmovel %ecx, %esi` = 0F 44 F1.
    let bad = patched(
        &obj,
        "p",
        find(&obj, "p", &[0x0F, 0x44, 0xF1], 0),
        &[0x0F, 0x1F, 0x00],
    );
    let zeros = g.probes[0].vectors.iter().filter(|v| v[0] == 0).count();
    assert!(zeros >= 2);
    assert_eq!(wrong(&g, "p", &bad), vec![vec![0u64]; zeros]);
}

/// A local's zeroing store overwritten with a nop: the read-before-write
/// local reads the stack's poison. Every vector reds.
#[test]
fn potency_an_unzeroed_local_reads_poison() {
    let g = unwritten_locals();
    let (_, obj) = compile_x86(&g.wat()).unwrap();
    // z1 is `(param i64) (local i64) local.get 1`: its zeroing store is
    // `movq %rax, -0x10(%rbp)` = 48 89 45 F0.
    let bad = patched(
        &obj,
        "z1",
        find(&obj, "z1", &[0x48, 0x89, 0x45, 0xF0], 0),
        &[0x0F, 0x1F, 0x40, 0x00],
    );
    let p = g.probes.iter().find(|p| p.name == "z1").unwrap();
    assert_eq!(wrong(&g, "z1", &bad).len(), p.vectors.len());
    // Zeroed in its low half only (`movl`: the REX.W dropped, a 1-byte nop in
    // its place): the i64 local's upper half is poison.
    let bad = patched(
        &obj,
        "z1",
        find(&obj, "z1", &[0x48, 0x89, 0x45, 0xF0], 0),
        &[0x90],
    );
    assert_eq!(wrong(&g, "z1", &bad).len(), p.vectors.len());
    assert!(wrong(&g, "z1", &obj).is_empty());
}

/// A spill reload aimed at the wrong slot: the second operand of `a - b` is
/// loaded from spill slot 0 (where `a` is) instead of slot 1.
#[test]
fn potency_a_spill_reload_from_the_wrong_slot_reds() {
    let g = spills(T::I64);
    let (_, obj) = compile_x86(&g.wat()).unwrap();
    // `sub`: both operands are spilled to -0x18 and -0x20. The reload of the
    // second operand is `movq -0x20(%rbp), %r` — retarget it at -0x18.
    let body = obj.function_bytes("sub").unwrap();
    let at = (0..body.len() - 3)
        .rfind(|&i| body[i] & 0xF8 == 0x48 && body[i + 1] == 0x8B && body[i + 3] == 0xE0)
        .expect("a load from -0x20(%rbp) in `sub`");
    let bad = patched(&obj, "sub", at + 3, &[0xE8]);
    let p = g.probes.iter().find(|p| p.name == "sub").unwrap();
    // a - b becomes a - a = 0: wrong unless a == b.
    let expect = p.vectors.iter().filter(|v| v[0] != v[1]).count();
    assert!(expect >= 30);
    assert_eq!(wrong(&g, "sub", &bad).len(), expect);
    assert!(wrong(&g, "sub", &obj).is_empty());
}

/// THE X2 REVIEW'S MUTANT B, in the image: the `movl %r, %r` of
/// `i64.extend_i32_u` overwritten with a nop. The wrapped-TEMPORARY probe,
/// its spilled twin and the wrapped-parameter probe all red on every vector
/// whose upper half is nonzero.
#[test]
fn potency_a_dropped_re_zeroing_reds_on_the_wrapped_temporary() {
    let g = upper_half();
    let (_, obj) = compile_x86(&g.wat()).unwrap();
    for name in ["wt_u", "ws_u", "w_u"] {
        // `movl %esi, %esi` = 89 F6; the last one is the extension.
        let n = obj
            .function_bytes(name)
            .unwrap()
            .windows(2)
            .filter(|w| *w == [0x89, 0xF6])
            .count();
        assert_eq!(n, 1, "{name}: one `movl %esi, %esi`");
        let bad = patched(&obj, name, find(&obj, name, &[0x89, 0xF6], 0), &NOP2);
        let p = g.probes.iter().find(|p| p.name == name).unwrap();
        let expect: Vec<Vec<u64>> = p
            .vectors
            .iter()
            .filter(|v| v[0] >> 32 != 0)
            .cloned()
            .collect();
        assert!(expect.len() >= 40, "{name}");
        assert_eq!(wrong(&g, name, &bad), expect, "{name}");
        assert!(wrong(&g, name, &obj).is_empty());
    }
}

/// An i64 parameter homed with a 32-bit store: the upper half of its slot
/// stays the stack's poison, and the 64-bit load reads it back.
#[test]
fn potency_a_parameter_homed_at_the_wrong_width_reds() {
    let g = six_params();
    let (_, obj) = compile_x86(&g.wat()).unwrap();
    // p1 returns the i64 parameter 1, homed by `movq %rsi, -0x10(%rbp)` =
    // 48 89 75 F0. Drop the REX.W (a 1-byte nop in its place): a 32-bit
    // store, and the slot's upper half stays poison.
    let bad = patched(
        &obj,
        "p1",
        find(&obj, "p1", &[0x48, 0x89, 0x75, 0xF0], 0),
        &[0x90],
    );
    let p = g.probes.iter().find(|p| p.name == "p1").unwrap();
    assert_eq!(wrong(&g, "p1", &bad).len(), p.vectors.len());
    assert!(wrong(&g, "p1", &obj).is_empty());
}
