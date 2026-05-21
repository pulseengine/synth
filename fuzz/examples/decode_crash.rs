//! One-shot decoder for fuzz crash artifacts.
use arbitrary::{Arbitrary, Unstructured};
use synth_fuzz::{FuzzInput, lower_arbitrary_to_wasm_ops};

fn main() {
    let path = std::env::args().nth(1).expect("usage: decode_crash <path>");
    let bytes = std::fs::read(&path).expect("read");
    let mut u = Unstructured::new(&bytes);
    let input = FuzzInput::arbitrary(&mut u).expect("decode");
    println!("FuzzInput {{");
    println!("    num_params: {},", input.num_params);
    println!("    ops: [");
    for op in &input.ops {
        println!("        {:?},", op);
    }
    println!("    ],");
    println!("}}");
    let np = input.num_params.min(4);
    let wasm_ops = lower_arbitrary_to_wasm_ops(&input.ops, np);
    println!("\nLowered to {} WasmOps:", wasm_ops.len());
    for (i, op) in wasm_ops.iter().enumerate() {
        println!("  [{i}] {op:?}");
    }
}
