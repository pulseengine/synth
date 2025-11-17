//! Benchmark Suite for Code Generation Quality
//!
//! Compares generated ARM code against typical native code sizes and counts

use synth_backend::ArmEncoder;
use synth_synthesis::{InstructionSelector, PeepholeOptimizer, RuleDatabase, WasmOp};

/// Benchmark result
#[derive(Debug)]
struct BenchmarkResult {
    name: String,
    wasm_ops: usize,
    arm_instructions: usize,
    optimized_instructions: usize,
    code_bytes: usize,
    native_estimate_bytes: usize,
    optimization_reduction: f64,
    size_ratio: f64,
}

impl BenchmarkResult {
    fn print(&self) {
        println!("\n{}", "=".repeat(70));
        println!("Benchmark: {}", self.name);
        println!("{}", "=".repeat(70));
        println!("  WASM operations:        {}", self.wasm_ops);
        println!("  ARM instructions:       {}", self.arm_instructions);
        println!("  After optimization:     {}", self.optimized_instructions);
        println!("  Generated code size:    {} bytes", self.code_bytes);
        println!("  Native estimate:        {} bytes", self.native_estimate_bytes);
        println!("  Optimization reduction: {:.1}%", self.optimization_reduction);
        println!("  Size ratio (gen/native):{:.2}x", self.size_ratio);
        println!("{}", "=".repeat(70));
    }
}

fn benchmark(name: &str, wasm_ops: Vec<WasmOp>, native_estimate_bytes: usize) -> BenchmarkResult {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");

    let optimizer = PeepholeOptimizer::new();
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let (optimized_ops, _) = optimizer.optimize_with_stats(&ops);

    let encoder = ArmEncoder::new_arm32();
    let code = encoder.encode_sequence(&optimized_ops).expect("Encoding failed");

    let optimization_reduction = if arm_instrs.len() > 0 {
        ((arm_instrs.len() - optimized_ops.len()) as f64 / arm_instrs.len() as f64) * 100.0
    } else {
        0.0
    };

    let size_ratio = if native_estimate_bytes > 0 {
        code.len() as f64 / native_estimate_bytes as f64
    } else {
        0.0
    };

    BenchmarkResult {
        name: name.to_string(),
        wasm_ops: wasm_ops.len(),
        arm_instructions: arm_instrs.len(),
        optimized_instructions: optimized_ops.len(),
        code_bytes: code.len(),
        native_estimate_bytes,
        optimization_reduction,
        size_ratio,
    }
}

#[test]
fn benchmark_arithmetic_operations() {
    // Basic arithmetic: (a + b) * (c - d)
    let wasm_ops = vec![
        WasmOp::I32Const(10),
        WasmOp::I32Const(20),
        WasmOp::I32Add,
        WasmOp::I32Const(50),
        WasmOp::I32Const(30),
        WasmOp::I32Sub,
        WasmOp::I32Mul,
    ];

    // Native ARM: ~7 instructions (4 MOV + ADD + SUB + MUL) = ~28 bytes
    let result = benchmark("Arithmetic Operations", wasm_ops, 28);
    result.print();

    assert!(result.code_bytes <= 100); // Reasonable upper bound
    assert!(result.optimized_instructions <= 10);
}

#[test]
fn benchmark_bitwise_operations() {
    // Bitwise: (a & b) | (c ^ d)
    let wasm_ops = vec![
        WasmOp::I32Const(0xFF00),
        WasmOp::I32Const(0x00FF),
        WasmOp::I32And,
        WasmOp::I32Const(0xAAAA),
        WasmOp::I32Const(0x5555),
        WasmOp::I32Xor,
        WasmOp::I32Or,
    ];

    // Native: ~7 instructions = ~28 bytes
    let result = benchmark("Bitwise Operations", wasm_ops, 28);
    result.print();

    assert!(result.code_bytes <= 100);
}

#[test]
fn benchmark_shift_operations() {
    // Shifts: (a << 2) + (b >> 3) + (c >>> 4)
    let wasm_ops = vec![
        WasmOp::I32Const(100),
        WasmOp::I32Const(2),
        WasmOp::I32Shl,
        WasmOp::I32Const(200),
        WasmOp::I32Const(3),
        WasmOp::I32ShrS,
        WasmOp::I32Add,
        WasmOp::I32Const(300),
        WasmOp::I32Const(4),
        WasmOp::I32ShrU,
        WasmOp::I32Add,
    ];

    // Native: ~11 instructions = ~44 bytes
    let result = benchmark("Shift Operations", wasm_ops, 44);
    result.print();

    assert!(result.code_bytes <= 120);
}

#[test]
fn benchmark_division_operations() {
    // Division: (a / b) + (c % d)
    let wasm_ops = vec![
        WasmOp::I32Const(1000),
        WasmOp::I32Const(7),
        WasmOp::I32DivU,
        WasmOp::I32Const(100),
        WasmOp::I32Const(13),
        WasmOp::I32RemU,
        WasmOp::I32Add,
    ];

    // Native: ~7 instructions (2 MOV + UDIV + 2 MOV + UDIV + ADD) = ~28 bytes
    let result = benchmark("Division Operations", wasm_ops, 28);
    result.print();

    assert!(result.code_bytes <= 100);
}

#[test]
fn benchmark_bit_manipulation() {
    // Bit manipulation: clz(a) + ctz(b) + rotl(c, 4)
    let wasm_ops = vec![
        WasmOp::I32Const(0x00001000),
        WasmOp::I32Clz,
        WasmOp::I32Const(0x10000000),
        WasmOp::I32Ctz,
        WasmOp::I32Add,
        WasmOp::I32Const(0x12345678),
        WasmOp::I32Const(4),
        WasmOp::I32Rotl,
        WasmOp::I32Add,
    ];

    // Native: ~9 instructions = ~36 bytes
    let result = benchmark("Bit Manipulation", wasm_ops, 36);
    result.print();

    assert!(result.code_bytes <= 120);
}

#[test]
fn benchmark_comparison_operations() {
    // Comparisons: (a == b) && (c < d) && (e >= f)
    let wasm_ops = vec![
        WasmOp::I32Const(10),
        WasmOp::I32Const(10),
        WasmOp::I32Eq,
        WasmOp::I32Const(5),
        WasmOp::I32Const(15),
        WasmOp::I32LtS,
        WasmOp::I32And,
        WasmOp::I32Const(20),
        WasmOp::I32Const(15),
        WasmOp::I32GeS,
        WasmOp::I32And,
    ];

    // Native: ~11 instructions = ~44 bytes
    let result = benchmark("Comparison Operations", wasm_ops, 44);
    result.print();

    assert!(result.code_bytes <= 120);
}

#[test]
fn benchmark_memory_operations() {
    // Memory: load, modify, store
    let wasm_ops = vec![
        WasmOp::I32Const(0x20000000),
        WasmOp::I32Load { offset: 0, align: 4 },
        WasmOp::I32Const(1),
        WasmOp::I32Add,
        WasmOp::I32Const(0x20000000),
        WasmOp::I32Store { offset: 0, align: 4 },
    ];

    // Native: ~6 instructions (MOV + LDR + MOV + ADD + MOV + STR) = ~24 bytes
    let result = benchmark("Memory Operations", wasm_ops, 24);
    result.print();

    assert!(result.code_bytes <= 80);
}

#[test]
fn benchmark_loop_construct() {
    // Simple counting loop
    let wasm_ops = vec![
        WasmOp::I32Const(10),
        WasmOp::LocalSet(0),
        WasmOp::Loop,
        WasmOp::LocalGet(0),
        WasmOp::I32Const(1),
        WasmOp::I32Sub,
        WasmOp::LocalTee(0),
        WasmOp::I32Const(0),
        WasmOp::I32GtU,
        WasmOp::BrIf(0),
        WasmOp::End,
    ];

    // Native: ~7 instructions = ~28 bytes
    let result = benchmark("Loop Construct", wasm_ops, 28);
    result.print();

    assert!(result.code_bytes <= 100);
}

#[test]
fn benchmark_embedded_gpio_pattern() {
    // Common embedded pattern: read-modify-write GPIO
    let wasm_ops = vec![
        WasmOp::I32Const(0x40020000),  // GPIO base
        WasmOp::I32Load { offset: 0, align: 4 },  // Read current value
        WasmOp::I32Const(0x20),        // Bit mask
        WasmOp::I32Or,                 // Set bit
        WasmOp::I32Const(0x40020000),  // GPIO base
        WasmOp::I32Store { offset: 0, align: 4 },  // Write back
    ];

    // Native: ~6 instructions = ~24 bytes
    let result = benchmark("Embedded GPIO Pattern", wasm_ops, 24);
    result.print();

    assert!(result.code_bytes <= 80);
}

#[test]
fn benchmark_fixed_point_math() {
    // Fixed-point: (a * b) >> 16 (Q16.16 multiplication)
    let wasm_ops = vec![
        WasmOp::I32Const(65536),   // 1.0 in Q16.16
        WasmOp::I32Const(131072),  // 2.0 in Q16.16
        WasmOp::I32Mul,
        WasmOp::I32Const(16),
        WasmOp::I32ShrS,           // Shift to normalize
    ];

    // Native: ~5 instructions = ~20 bytes
    let result = benchmark("Fixed-Point Math", wasm_ops, 20);
    result.print();

    assert!(result.code_bytes <= 60);
}

#[test]
fn benchmark_summary() {
    println!("\n{}", "=".repeat(70));
    println!("BENCHMARK SUMMARY");
    println!("{}", "=".repeat(70));

    let benchmarks = vec![
        ("Arithmetic", vec![
            WasmOp::I32Const(10), WasmOp::I32Const(20), WasmOp::I32Add,
        ], 12),
        ("Bitwise", vec![
            WasmOp::I32Const(0xFF), WasmOp::I32Const(0xAA), WasmOp::I32And,
        ], 12),
        ("Division", vec![
            WasmOp::I32Const(100), WasmOp::I32Const(7), WasmOp::I32DivU,
        ], 12),
        ("Bit Manipulation", vec![
            WasmOp::I32Const(0x1000), WasmOp::I32Clz,
        ], 8),
        ("Memory", vec![
            WasmOp::I32Const(0x20000000),
            WasmOp::I32Load { offset: 0, align: 4 },
        ], 8),
    ];

    let mut total_code = 0;
    let mut total_native = 0;
    let mut total_reduction = 0.0;

    for (name, ops, native) in benchmarks {
        let result = benchmark(name, ops, native);
        total_code += result.code_bytes;
        total_native += result.native_estimate_bytes;
        total_reduction += result.optimization_reduction;
        println!("  {:20} {:3} bytes  (native ~{:3} bytes, {:.1}% opt)",
            result.name, result.code_bytes, result.native_estimate_bytes,
            result.optimization_reduction);
    }

    let avg_reduction = total_reduction / 5.0;
    let overall_ratio = total_code as f64 / total_native as f64;

    println!("{}", "-".repeat(70));
    println!("  Total generated:     {} bytes", total_code);
    println!("  Total native est:    {} bytes", total_native);
    println!("  Average optimization:{:.1}%", avg_reduction);
    println!("  Overall size ratio:  {:.2}x", overall_ratio);
    println!("{}", "=".repeat(70));

    // Quality assertions
    assert!(overall_ratio < 5.0, "Code should be within 5x of native");
    assert!(avg_reduction >= 0.0, "Optimization should not make code worse");
}

#[test]
fn benchmark_code_density() {
    // Measure code density: operations per byte
    let test_cases = vec![
        ("Dense arithmetic", vec![
            WasmOp::I32Const(1), WasmOp::I32Const(2), WasmOp::I32Add,
            WasmOp::I32Const(3), WasmOp::I32Mul,
        ]),
        ("Dense bitwise", vec![
            WasmOp::I32Const(0xFF), WasmOp::I32Const(0xAA), WasmOp::I32And,
            WasmOp::I32Const(0x55), WasmOp::I32Or,
        ]),
    ];

    println!("\n{}", "=".repeat(70));
    println!("CODE DENSITY ANALYSIS");
    println!("{}", "=".repeat(70));

    for (name, ops) in test_cases {
        let result = benchmark(name, ops.clone(), 0);
        let density = ops.len() as f64 / result.code_bytes as f64;
        println!("  {:20} {:.3} ops/byte ({} ops, {} bytes)",
            name, density, ops.len(), result.code_bytes);

        assert!(density > 0.01, "Code density should be reasonable");
    }

    println!("{}", "=".repeat(70));
}
