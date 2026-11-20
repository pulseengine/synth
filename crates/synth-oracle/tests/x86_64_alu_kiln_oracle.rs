//! RQ-91-X86ALU (Refs #1741): the x86-64 straight-line integer core against
//! kiln.
//!
//! Every op lane X2 lowers — the 52 rows of the x86-64 rule table (i32 and
//! i64 add, sub, mul, and, or, xor, shl, shr_s, shr_u, rotl, rotr, the ten
//! compares, eqz, the sign extensions, `i64.extend_i32_s/u`, `i32.wrap_i64`),
//! `select`, `i32.const`/`i64.const`, `drop` and `nop` — is compiled by synth
//! with `-b x86_64 --relocatable` and run, as the bytes synth emitted, on
//! unicorn x86-64 (CPU model pinned to QEMU64, SysV arguments with POISONED
//! upper halves, poisoned scratch registers, flags and stack; callee-saved
//! registers, `rsp`, the direction flag and the caller's frame checked) and on
//! kiln. Every case has to AGREE.
//!
//! ONE MODULE PER OP, each holding the op in every OPERAND SHAPE the selector
//! distinguishes: both operands in parameter registers (in both orders), one
//! or both in temporaries, the same register twice, four-parameter functions
//! (where `rcx`, the shift-count register, arrives holding a parameter that
//! is read back afterwards), and — for i32 ops — operands that are wrapped i64
//! parameters and wrapped i64 TEMPORARIES, whose upper halves are nonzero
//! garbage an i32 op must not read and `i64.extend_i32_u` must clear.
//! (The shapes were drawn for lane X2's register-resident parameters. Since
//! lane X3 every parameter is homed to a frame slot and loaded into a
//! temporary, so several shapes now lower alike; they are kept as they are.)
//!
//! VECTORS: the both-parameters shape runs EXHAUSTIVELY over the edge values
//! (every pair; the edge set holds the shift counts 0, 1, 31, 32, 33, 63, 64,
//! 65 and both ends of each width) plus seeded random pairs; every other
//! shape runs a fixed slice of edge pairs plus seeded random ones. The counts
//! are exact literals.
//!
//! RED ON THE STACK BASE (the X1 skeleton, 4dd56c1d): every group fails to
//! compile there with `unsupported wasm op` or, for i64, a refused signature;
//! no group compiles.
//!
//! Needs `--features exec`. `SYNTH` may name a prebuilt binary.

#![cfg(feature = "exec")]

use std::path::PathBuf;

use synth_oracle::compare::EmuOutcome;
use synth_oracle::emulate::{Cpu, EmuConfig};
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

    fn edges(self) -> &'static [u64] {
        match self {
            T::I32 => EDGE32,
            T::I64 => EDGE64,
        }
    }
}

/// i32 edge values. The shift counts 0, 1, 31, 32, 33, 63, 64, 65 are in it.
const EDGE32: &[u64] = &[
    0,
    1,
    2,
    7,
    31,
    32,
    33,
    63,
    64,
    65,
    0x7F,
    0x80,
    0xFF,
    0x100,
    0x7FFF,
    0x8000,
    0xFFFF,
    0x7FFF_FFFF,
    0x8000_0000,
    0x8000_0001,
    0xFFFF_FFFE,
    0xFFFF_FFFF,
];

/// i64 edge values: the same counts, both ends of 32 and of 64 bits.
const EDGE64: &[u64] = &[
    0,
    1,
    2,
    31,
    32,
    33,
    63,
    64,
    65,
    0x7F,
    0x80,
    0xFFFF,
    0x7FFF_FFFF,
    0x8000_0000,
    0xFFFF_FFFF,
    0x1_0000_0000,
    0x7FFF_FFFF_FFFF_FFFF,
    0x8000_0000_0000_0000,
    0x8000_0000_0000_0001,
    0xFFFF_FFFF_0000_0000,
    0xFFFF_FFFF_FFFF_FFFE,
    0xFFFF_FFFF_FFFF_FFFF,
];

/// Seeded random pairs added to the exhaustive shape, and to every other.
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

/// One exported function of a group: its parameter types, its body, and the
/// argument vectors it runs over (raw bits, one per parameter).
struct Probe {
    name: String,
    params: Vec<T>,
    result: T,
    body: String,
    vectors: Vec<Vec<u64>>,
}

/// One op: a module of probes.
struct Group {
    op: String,
    probes: Vec<Probe>,
}

impl Group {
    fn wat(&self) -> String {
        let mut s = String::from("(module\n");
        for p in &self.probes {
            let params: Vec<&str> = p.params.iter().map(|t| t.s()).collect();
            s.push_str(&format!(
                "  (func (export \"{}\") (param {}) (result {}) {})\n",
                p.name,
                params.join(" "),
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

fn get(i: u32) -> String {
    format!("local.get {i}")
}

/// Parameter `i` moved into a TEMPORARY (`x + 0`).
fn temp(t: T, i: u32) -> String {
    format!("local.get {i} {0}.const 0 {0}.add", t.s())
}

/// An i32 that is a wrapped i64 TEMPORARY: i64 parameter `i` computed into a
/// temporary (`x + 0` at 64 bits) and then wrapped. `i32.wrap_i64` emits
/// nothing, so the temporary keeps the i64's upper half — the one operand
/// shape in which an i32 value sits in a TEMPORARY with nonzero bits 63:32.
/// (A wrapped PARAMETER is always copied before it is written, and a
/// temporary built by an i32 op has a zero upper half, so neither reaches the
/// in-place paths.)
fn wrapped_temp(i: u32) -> String {
    format!("local.get {i} i64.const 0 i64.add i32.wrap_i64")
}

/// `xor` the result with parameter 3 — the one that arrives in `rcx` — so a
/// shift that failed to preserve it shows.
fn rcx_tail(t: T, r: T) -> String {
    match (t, r) {
        (T::I64, T::I32) => "local.get 3 i32.wrap_i64 i32.xor".to_string(),
        (T::I32, T::I32) | (T::I64, T::I64) => format!("local.get 3 {}.xor", r.s()),
        (T::I32, T::I64) => unreachable!("no binary op takes i32 and gives i64"),
    }
}

/// A binary op `t x t -> r`, in every operand shape.
fn binary(op: &str, t: T, r: T) -> Group {
    let o = op;
    let mut probes = Vec::new();
    let mut add = |name: &str, params: Vec<T>, body: String, vectors: Vec<Vec<u64>>| {
        probes.push(Probe {
            name: name.to_string(),
            params,
            result: r,
            body,
            vectors,
        });
    };
    let seed = |shape: &str| format!("{op}/{shape}");
    add(
        "pp",
        vec![t; 2],
        format!("{} {} {o}", get(0), get(1)),
        full_pairs(t, &seed("pp")),
    );
    add(
        "rv",
        vec![t; 2],
        format!("{} {} {o}", get(1), get(0)),
        slice(t, 2, &seed("rv")),
    );
    add(
        "tp",
        vec![t; 2],
        format!("{} {} {o}", temp(t, 0), get(1)),
        slice(t, 2, &seed("tp")),
    );
    add(
        "pt",
        vec![t; 2],
        format!("{} {} {o}", get(0), temp(t, 1)),
        slice(t, 2, &seed("pt")),
    );
    add(
        "tt",
        vec![t; 2],
        format!("{} {} {o}", temp(t, 0), temp(t, 1)),
        slice(t, 2, &seed("tt")),
    );
    add(
        "sq",
        vec![t; 1],
        format!("{} {} {o}", get(0), get(0)),
        slice(t, 1, &seed("sq")),
    );
    // Four parameters: rcx holds parameter 3, which the tail reads back.
    add(
        "p4",
        vec![t; 4],
        format!("{} {} {o} {}", get(0), get(1), rcx_tail(t, r)),
        slice(t, 4, &seed("p4")),
    );
    add(
        "t4",
        vec![t; 4],
        format!("{} {} {o} {}", temp(t, 0), temp(t, 1), rcx_tail(t, r)),
        slice(t, 4, &seed("t4")),
    );
    // Parameter 3 as the right operand (a shift count already in cl) ...
    add(
        "c3",
        vec![t; 4],
        format!("{} {} {o} {}", get(0), get(3), rcx_tail(t, r)),
        // Slots 0 and 3 carry the edge pair.
        slice(t, 4, &seed("c3"))
            .into_iter()
            .map(|v| vec![v[0], v[2], v[3], v[1]])
            .collect(),
    );
    // ... and as the left one (the value shifted lives in rcx).
    add(
        "v3",
        vec![t; 4],
        format!("{} {} {o} {}", get(3), get(0), rcx_tail(t, r)),
        slice(t, 4, &seed("v3"))
            .into_iter()
            .map(|v| vec![v[1], v[2], v[3], v[0]])
            .collect(),
    );
    if t == T::I32 {
        // i32 operands that are WRAPPED i64 parameters: their registers'
        // upper halves hold whatever the i64 held.
        probes.push(Probe {
            name: "ww".to_string(),
            params: vec![T::I64; 2],
            result: r,
            body: format!("{} i32.wrap_i64 {} i32.wrap_i64 {o}", get(0), get(1)),
            vectors: slice(T::I64, 2, &format!("{op}/ww")),
        });
        // The same, with both operands wrapped i64 TEMPORARIES.
        probes.push(Probe {
            name: "wt".to_string(),
            params: vec![T::I64; 2],
            result: r,
            body: format!("{} {} {o}", wrapped_temp(0), wrapped_temp(1)),
            vectors: slice(T::I64, 2, &format!("{op}/wt")),
        });
    }
    Group {
        op: op.to_string(),
        probes,
    }
}

/// A unary op `t -> r`: the operand in each of three parameter registers
/// (`dil`/`sil` need a REX prefix as byte registers, `r9b` a REX.B), in a
/// temporary, and (for an i32 operand) as a wrapped i64.
fn unary(op: &str, t: T, r: T) -> Group {
    let all = |n: usize, at: usize, seed: &str| -> Vec<Vec<u64>> {
        let mut rng = Rng::new(seed);
        let mut v: Vec<Vec<u64>> = Vec::new();
        let mut vals: Vec<u64> = t.edges().to_vec();
        for _ in 0..RANDOM_FULL {
            vals.push(rng.next());
        }
        for x in vals {
            v.push(
                (0..n)
                    .map(|i| if i == at { x } else { rng.next() })
                    .collect(),
            );
        }
        v
    };
    let mut probes = vec![
        Probe {
            name: "p".into(),
            params: vec![t],
            result: r,
            body: format!("{} {op}", get(0)),
            vectors: all(1, 0, &format!("{op}/p")),
        },
        Probe {
            name: "p1".into(),
            params: vec![t; 2],
            result: r,
            body: format!("{} {op}", get(1)),
            vectors: all(2, 1, &format!("{op}/p1")),
        },
        Probe {
            name: "p5".into(),
            params: vec![t; 6],
            result: r,
            body: format!("{} {op}", get(5)),
            vectors: all(6, 5, &format!("{op}/p5")),
        },
        Probe {
            name: "t".into(),
            params: vec![t],
            result: r,
            body: format!("{} {op}", temp(t, 0)),
            vectors: all(1, 0, &format!("{op}/t")),
        },
    ];
    if t == T::I32 {
        let mut rng = Rng::new(&format!("{op}/w"));
        let mut vectors: Vec<Vec<u64>> = EDGE64.iter().map(|&x| vec![x]).collect();
        for _ in 0..RANDOM_FULL {
            vectors.push(vec![rng.next()]);
        }
        probes.push(Probe {
            name: "w".into(),
            params: vec![T::I64],
            result: r,
            body: format!("{} i32.wrap_i64 {op}", get(0)),
            vectors: vectors.clone(),
        });
        // The operand is a wrapped i64 TEMPORARY: the op runs in place on a
        // register whose upper half is the i64's. `i64.extend_i32_u` must
        // still re-zero it (`movl %eax, %eax`).
        probes.push(Probe {
            name: "wt".into(),
            params: vec![T::I64],
            result: r,
            body: format!("{} {op}", wrapped_temp(0)),
            vectors,
        });
    }
    Group {
        op: op.to_string(),
        probes,
    }
}

/// `select` over values of type `t`: every mix of parameter and temporary
/// operands, and a condition that is a wrapped i64 (zero in its low half only).
fn select(t: T) -> Group {
    const CONDS: &[u64] = &[0, 1, 2, 0x100, 0x8000_0000, 0xFFFF_FFFF];
    let pairs = |seed: &str| -> Vec<Vec<u64>> {
        let mut v = Vec::new();
        for row in slice(t, 2, seed) {
            for &c in CONDS {
                v.push(vec![row[0], row[1], c]);
            }
        }
        v
    };
    let params = vec![t, t, T::I32];
    let shape = |name: &str, a: String, b: String, c: String| Probe {
        name: name.to_string(),
        params: params.clone(),
        result: t,
        body: format!("{a} {b} {c} select"),
        vectors: pairs(&format!("select.{}/{name}", t.s())),
    };
    let mut probes = vec![
        shape("ppp", get(0), get(1), get(2)),
        shape("tpp", temp(t, 0), get(1), get(2)),
        shape("ptp", get(0), temp(t, 1), get(2)),
        shape("ppt", get(0), get(1), temp(T::I32, 2)),
        shape("ttt", temp(t, 0), temp(t, 1), temp(T::I32, 2)),
        shape("same", get(0), get(0), get(2)),
    ];
    // The condition is a wrapped i64: only its LOW half decides.
    let wide: &[u64] = &[
        0,
        1,
        0x1_0000_0000,
        0xFFFF_FFFF_0000_0000,
        0x8000_0000_0000_0000,
        0xFFFF_FFFF_FFFF_FFFF,
    ];
    let mut vectors = Vec::new();
    for row in slice(t, 2, &format!("select.{}/wc", t.s())) {
        for &c in wide {
            vectors.push(vec![row[0], row[1], c]);
        }
    }
    probes.push(Probe {
        name: "wc".into(),
        params: vec![t, t, T::I64],
        result: t,
        body: format!("{} {} {} i32.wrap_i64 select", get(0), get(1), get(2)),
        vectors: vectors.clone(),
    });
    // The condition is a wrapped i64 TEMPORARY.
    probes.push(Probe {
        name: "wtc".into(),
        params: vec![t, t, T::I64],
        result: t,
        body: format!("{} {} {} select", get(0), get(1), wrapped_temp(2)),
        vectors,
    });
    if t == T::I32 {
        // The selected VALUES are wrapped i64 temporaries, and the result is
        // widened unsigned so their upper halves would show.
        let mut vectors = Vec::new();
        for row in slice(T::I64, 2, "select.i32/wtv") {
            for &c in CONDS {
                vectors.push(vec![row[0], row[1], c]);
            }
        }
        probes.push(Probe {
            name: "wtv".into(),
            params: vec![T::I64, T::I64, T::I32],
            result: T::I64,
            body: format!(
                "{} {} {} select i64.extend_i32_u",
                wrapped_temp(0),
                wrapped_temp(1),
                get(2)
            ),
            vectors,
        });
    }
    Group {
        op: format!("select.{}", t.s()),
        probes,
    }
}

/// Constants: every edge value and the boundaries of the three immediate
/// forms, each as its own nullary function; and each added to a parameter.
fn consts(t: T) -> Group {
    let mut ks: Vec<u64> = t.edges().to_vec();
    if t == T::I64 {
        ks.extend([
            0x7FFF_FFFF_FFFF_FF80,
            0xFFFF_FFFF_7FFF_FFFF,
            0xFFFF_FFFF_8000_0000,
            0xFFFF_FFFF_FFFF_FF80,
            0x1122_3344_5566_7788,
        ]);
    }
    let lit = |k: u64| match t {
        T::I32 => format!("i32.const {}", k as u32 as i32),
        T::I64 => format!("i64.const {}", k as i64),
    };
    let mut probes = Vec::new();
    for (n, &k) in ks.iter().enumerate() {
        probes.push(Probe {
            name: format!("k{n}"),
            params: vec![],
            result: t,
            body: lit(k),
            vectors: vec![vec![]],
        });
        probes.push(Probe {
            name: format!("a{n}"),
            params: vec![t],
            result: t,
            body: format!("{} {} {}.add", get(0), lit(k), t.s()),
            vectors: vec![vec![0], vec![1], vec![k], vec![!k]],
        });
    }
    Group {
        op: format!("{}.const", t.s()),
        probes,
    }
}

/// `drop` and `nop`: the dropped value's temporary is reused; the kept one is
/// the result.
fn drop_nop() -> Group {
    let v32 = slice(T::I32, 2, "drop/i32");
    let v64 = slice(T::I64, 2, "drop/i64");
    let p = |name: &str, t: T, body: String, vectors: &[Vec<u64>]| Probe {
        name: name.to_string(),
        params: vec![t; 2],
        result: t,
        body,
        vectors: vectors.to_vec(),
    };
    Group {
        op: "drop".into(),
        probes: vec![
            p(
                "d32",
                T::I32,
                "local.get 0 local.get 1 drop nop".into(),
                &v32,
            ),
            p(
                "dt32",
                T::I32,
                "local.get 0 local.get 1 i32.const 9 i32.add drop local.get 1 i32.const 5 i32.mul i32.sub".into(),
                &v32,
            ),
            // Three drops in a row, then two temporaries: a drop that did not
            // free its temporary would leave none.
            p(
                "d3",
                T::I32,
                "i32.const 1 drop i32.const 2 drop i32.const 3 drop local.get 0 i32.const 0 i32.add local.get 1 i32.const 0 i32.add i32.sub".into(),
                &v32,
            ),
            p(
                "d64",
                T::I64,
                "nop local.get 1 local.get 0 drop".into(),
                &v64,
            ),
            p(
                "dt64",
                T::I64,
                "local.get 0 local.get 1 i64.const 9 i64.add drop local.get 1 i64.const 5 i64.mul i64.sub".into(),
                &v64,
            ),
        ],
    }
}

const ARITH: &[&str] = &[
    "add", "sub", "mul", "and", "or", "xor", "shl", "shr_s", "shr_u", "rotl", "rotr",
];
const COMPARE: &[&str] = &[
    "eq", "ne", "lt_s", "lt_u", "gt_s", "gt_u", "le_s", "le_u", "ge_s", "ge_u",
];

fn arith_groups(t: T) -> Vec<Group> {
    ARITH
        .iter()
        .map(|o| binary(&format!("{}.{o}", t.s()), t, t))
        .collect()
}

fn compare_groups(t: T) -> Vec<Group> {
    COMPARE
        .iter()
        .map(|o| binary(&format!("{}.{o}", t.s()), t, T::I32))
        .collect()
}

fn other_groups() -> Vec<Group> {
    vec![
        unary("i32.eqz", T::I32, T::I32),
        unary("i64.eqz", T::I64, T::I32),
        unary("i32.extend8_s", T::I32, T::I32),
        unary("i32.extend16_s", T::I32, T::I32),
        unary("i64.extend8_s", T::I64, T::I64),
        unary("i64.extend16_s", T::I64, T::I64),
        unary("i64.extend32_s", T::I64, T::I64),
        unary("i64.extend_i32_s", T::I32, T::I64),
        unary("i64.extend_i32_u", T::I32, T::I64),
        unary("i32.wrap_i64", T::I64, T::I32),
        select(T::I32),
        select(T::I64),
        consts(T::I32),
        consts(T::I64),
        drop_nop(),
    ]
}

fn scratch() -> PathBuf {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("synth-oracle-x86-alu-{}-{n}", std::process::id()));
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
    // The AArch64 rule: a compile that printed "skipping" lowered less than
    // it was given.
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

fn run_group(g: &Group, wasm: &[u8], obj: &CompiledObject) -> Vec<Case> {
    let mut cases = Vec::new();
    for p in &g.probes {
        assert_eq!(
            obj.relocs_in(&p.name),
            0,
            "`{}` carries relocations",
            p.name
        );
        for v in &p.vectors {
            let args = args_of(p, v);
            cases.push(
                run_case(wasm, obj, &p.name, &args, FUEL, &Imports::new(), &cfg())
                    .unwrap_or_else(|e| panic!("{} {}{args:?}: harness error {e:?}", g.op, p.name)),
            );
        }
    }
    cases
}

/// Compile and run every group; require every case to agree and to return
/// VALUES on both sides (this lane emits no trap). Returns the case count.
fn sweep(label: &str, groups: &[Group]) -> usize {
    let mut declined = Vec::new();
    let mut bad = Vec::new();
    let mut total = 0;
    for g in groups {
        let (wasm, obj) = match compile_x86(&g.wat()) {
            Ok(x) => x,
            Err(e) => {
                declined.push(format!("  {}: {e}", g.op));
                continue;
            }
        };
        let cases = run_group(g, &wasm, &obj);
        assert_eq!(cases.len(), g.cases());
        total += cases.len();
        for c in &cases {
            if !c.verdict.is_agree() || !matches!(c.emulator, EmuOutcome::Values(_)) {
                bad.push(format!(
                    "  {} {}{:?}: {:?} (ref {:?}, emu {:?})",
                    g.op, c.export, c.args, c.verdict, c.reference, c.emulator
                ));
            }
        }
    }
    for l in declined.iter().chain(bad.iter().take(40)) {
        eprintln!("{l}");
    }
    assert!(
        declined.is_empty() && bad.is_empty(),
        "x86_64-alu {label}: {} of {} op groups did not compile, {} of {total} cases do not agree",
        declined.len(),
        groups.len(),
        bad.len()
    );
    total
}

#[test]
fn i32_arithmetic_agrees_with_kiln() {
    let groups = arith_groups(T::I32);
    assert_eq!(groups.len(), 11);
    let n = sweep("i32 arithmetic", &groups);
    assert_eq!(n, 10362, "case count moved");
    eprintln!("ORACLE x86_64-alu i32 arithmetic: {n} cases agree over 11 ops");
}

#[test]
fn i32_compares_agree_with_kiln() {
    let groups = compare_groups(T::I32);
    assert_eq!(groups.len(), 10);
    let n = sweep("i32 compares", &groups);
    assert_eq!(n, 9420, "case count moved");
    eprintln!("ORACLE x86_64-alu i32 compares: {n} cases agree over 10 ops");
}

#[test]
fn i64_arithmetic_agrees_with_kiln() {
    let groups = arith_groups(T::I64);
    assert_eq!(groups.len(), 11);
    let n = sweep("i64 arithmetic", &groups);
    assert_eq!(n, 9526, "case count moved");
    eprintln!("ORACLE x86_64-alu i64 arithmetic: {n} cases agree over 11 ops");
}

#[test]
fn i64_compares_agree_with_kiln() {
    let groups = compare_groups(T::I64);
    assert_eq!(groups.len(), 10);
    let n = sweep("i64 compares", &groups);
    assert_eq!(n, 8660, "case count moved");
    eprintln!("ORACLE x86_64-alu i64 compares: {n} cases agree over 10 ops");
}

#[test]
fn conversions_select_consts_and_drop_agree_with_kiln() {
    let groups = other_groups();
    assert_eq!(groups.len(), 15);
    let n = sweep("conversions, select, consts, drop", &groups);
    assert_eq!(n, 7411, "case count moved");
    eprintln!("ORACLE x86_64-alu conversions/select/consts/drop: {n} cases agree over 15 groups");
}

// ---------------------------------------------------------------- potency --

/// The disagreements of one probe when kiln runs `reference_wat` and the
/// emulator runs `obj`.
fn disagreements(g: &Group, probe: &str, reference_wat: &str, obj: &CompiledObject) -> usize {
    let wasm = wat::parse_str(reference_wat).unwrap();
    let p = g.probes.iter().find(|p| p.name == probe).unwrap();
    p.vectors
        .iter()
        .filter(|v| {
            !run_case(
                &wasm,
                obj,
                probe,
                &args_of(p, v),
                FUEL,
                &Imports::new(),
                &cfg(),
            )
            .unwrap()
            .verdict
            .is_agree()
        })
        .count()
}

/// A planted wrong REFERENCE: kiln runs `lt_u` for the compiled `lt_s`. The
/// two differ exactly when the operands' sign bits differ.
#[test]
fn potency_a_signedness_swap_in_the_reference_reds() {
    let g = binary("i32.lt_s", T::I32, T::I32);
    let (_, obj) = compile_x86(&g.wat()).expect("lt_s compiles");
    let planted = g.wat().replace("i32.lt_s", "i32.lt_u");
    assert_ne!(planted, g.wat());
    let p = &g.probes[0];
    assert_eq!(p.name, "pp");
    let expect = p
        .vectors
        .iter()
        .filter(|v| ((v[0] as u32) ^ (v[1] as u32)) >> 31 == 1)
        .count();
    assert!(
        expect > 100,
        "the vectors barely separate the two ({expect})"
    );
    assert_eq!(disagreements(&g, "pp", &planted, &obj), expect);
    assert_eq!(disagreements(&g, "pp", &g.wat(), &obj), 0);
}

/// The emitted IMAGE mutated: `setl` (`0F 9C`) becomes `setb` (`0F 92`) in the
/// bytes synth wrote for `lt_s`. Same vectors must red.
#[test]
fn potency_a_mutated_condition_in_the_image_reds() {
    let g = binary("i32.lt_s", T::I32, T::I32);
    let (_, obj) = compile_x86(&g.wat()).expect("lt_s compiles");
    let f = obj.func("pp").unwrap().clone();
    let body = &obj.text[f.offset as usize..(f.offset + f.size) as usize];
    let at = body
        .windows(2)
        .position(|w| w == [0x0F, 0x9C])
        .expect("a `setl` in `pp`");
    let mut bad = obj.clone();
    bad.text[f.offset as usize + at + 1] = 0x92;
    let p = &g.probes[0];
    let expect = p
        .vectors
        .iter()
        .filter(|v| ((v[0] as u32) ^ (v[1] as u32)) >> 31 == 1)
        .count();
    assert_eq!(disagreements(&g, "pp", &g.wat(), &bad), expect);
}

/// The shift COUNT's move into `cl` removed from the image (`movl %edi, %ecx`
/// overwritten with a 2-byte nop). Since lane X3 every parameter is homed and
/// `rcx` is scratch, so nothing restores it; in the four-parameter probe it
/// still holds ARGUMENT 3 at that point, and the shift then counts by that
/// instead of by parameter 1.
#[test]
fn potency_a_dropped_count_move_reds() {
    let g = binary("i32.shl", T::I32, T::I32);
    let (_, obj) = compile_x86(&g.wat()).expect("shl compiles");
    let f = obj.func("p4").unwrap().clone();
    let body = &obj.text[f.offset as usize..(f.offset + f.size) as usize];
    // `movl %edi, %ecx` = 89 F9, once in `p4`.
    let hits: Vec<usize> = body
        .windows(2)
        .enumerate()
        .filter(|(_, w)| *w == [0x89, 0xF9])
        .map(|(i, _)| i)
        .collect();
    assert_eq!(hits.len(), 1, "the count move in `p4`");
    let mut bad = obj.clone();
    let at = f.offset as usize + hits[0];
    bad.text[at..at + 2].copy_from_slice(&[0x66, 0x90]);
    let p = g.probes.iter().find(|p| p.name == "p4").unwrap();
    let expect = p
        .vectors
        .iter()
        .filter(|v| {
            (v[0] as u32).wrapping_shl(v[1] as u32) != (v[0] as u32).wrapping_shl(v[3] as u32)
        })
        .count();
    assert!(expect >= 30);
    assert_eq!(disagreements(&g, "p4", &g.wat(), &bad), expect);
    assert_eq!(disagreements(&g, "p4", &g.wat(), &obj), 0);
}

/// The re-zeroing of `i64.extend_i32_u` removed from the image (`movl %esi,
/// %esi` overwritten with a 2-byte nop): the wrapped i64 parameter's upper
/// half reaches the result. Since lane X3 an i32 ARGUMENT is homed and loaded
/// at 32 bits, so the upper half that survives to the extension is the one a
/// free `i32.wrap_i64` leaves — the `w` probe.
#[test]
fn potency_a_dropped_re_zeroing_reds() {
    let g = unary("i64.extend_i32_u", T::I32, T::I64);
    let (_, obj) = compile_x86(&g.wat()).expect("extend_i32_u compiles");
    let f = obj.func("w").unwrap().clone();
    let body = &obj.text[f.offset as usize..(f.offset + f.size) as usize];
    let hits: Vec<usize> = body
        .windows(2)
        .enumerate()
        .filter(|(_, w)| *w == [0x89, 0xF6])
        .map(|(i, _)| i)
        .collect();
    assert_eq!(hits.len(), 1, "the `movl %esi, %esi` of `w`");
    let mut bad = obj.clone();
    let at = f.offset as usize + hits[0];
    bad.text[at..at + 2].copy_from_slice(&[0x66, 0x90]);
    let p = g.probes.iter().find(|p| p.name == "w").unwrap();
    let expect = p.vectors.iter().filter(|v| v[0] >> 32 != 0).count();
    assert!(expect >= 40);
    assert_eq!(disagreements(&g, "w", &g.wat(), &bad), expect);
    assert_eq!(disagreements(&g, "w", &g.wat(), &obj), 0);
}

/// The re-zeroing of `i64.extend_i32_u` ELIDED when the value is already in
/// its register — the "drop a redundant `mov r, r`" peephole. The image is
/// mutated by overwriting the `movl %eax, %eax` of the wrapped-temporary probe
/// with a 2-byte nop. Every vector whose i64 has a nonzero upper half must
/// red; on wrapped PARAMETERS and on i32-built temporaries the same peephole
/// is invisible, which is why the `wt` shape exists (cold review F1).
#[test]
fn potency_an_elided_rezeroing_of_a_wrapped_temporary_reds() {
    let g = unary("i64.extend_i32_u", T::I32, T::I64);
    let (_, obj) = compile_x86(&g.wat()).expect("extend_i32_u compiles");
    let f = obj.func("wt").unwrap().clone();
    let body = &obj.text[f.offset as usize..(f.offset + f.size) as usize];
    // `movl %esi, %esi` = 89 F6, once in `wt` (since lane X3 the value is in
    // the first temporary, `rsi`, and a frame epilogue follows).
    let hits: Vec<usize> = body
        .windows(2)
        .enumerate()
        .filter(|(_, w)| *w == [0x89, 0xF6])
        .map(|(i, _)| i)
        .collect();
    assert_eq!(hits.len(), 1, "the lowering of `wt` moved");
    let at = hits[0];
    let mut bad = obj.clone();
    bad.text[f.offset as usize + at..f.offset as usize + at + 2].copy_from_slice(&[0x66, 0x90]);
    let p = g.probes.iter().find(|p| p.name == "wt").unwrap();
    let expect = p.vectors.iter().filter(|v| v[0] >> 32 != 0).count();
    assert!(expect >= 40, "too few vectors with a nonzero upper half");
    assert_eq!(disagreements(&g, "wt", &g.wat(), &bad), expect);
    assert_eq!(disagreements(&g, "wt", &g.wat(), &obj), 0);
}
