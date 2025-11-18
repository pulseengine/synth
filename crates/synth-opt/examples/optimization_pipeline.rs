//! Optimization Pipeline Example
//!
//! This example demonstrates how to use the Synth optimization framework
//! to optimize IR code through multiple passes.

use synth_cfg::CfgBuilder;
use synth_opt::{
    AlgebraicSimplification, CommonSubexpressionElimination, ConstantFolding, DeadCodeElimination,
    Instruction, Opcode, PassManager, PeepholeOptimization, Reg,
};

fn main() {
    println!("=== Synth Optimization Pipeline Example ===\n");

    // Build a simple CFG with one basic block
    let mut builder = CfgBuilder::new();
    for _ in 0..15 {
        builder.add_instruction();
    }
    let mut cfg = builder.build();

    // Create a program with optimization opportunities
    let mut instructions = vec![
        // 1. Redundant const (peephole will eliminate)
        Instruction {
            id: 0,
            opcode: Opcode::Const {
                dest: Reg(0),
                value: 100,
            },
            block_id: 0,
            is_dead: false,
        },
        Instruction {
            id: 1,
            opcode: Opcode::Const {
                dest: Reg(0),
                value: 5,
            },
            block_id: 0,
            is_dead: false,
        },
        // 2. Constant expressions (will be folded)
        Instruction {
            id: 2,
            opcode: Opcode::Const {
                dest: Reg(1),
                value: 10,
            },
            block_id: 0,
            is_dead: false,
        },
        Instruction {
            id: 3,
            opcode: Opcode::Const {
                dest: Reg(2),
                value: 20,
            },
            block_id: 0,
            is_dead: false,
        },
        Instruction {
            id: 4,
            opcode: Opcode::Add {
                dest: Reg(3),
                src1: Reg(1),
                src2: Reg(2),
            },
            block_id: 0,
            is_dead: false,
        },
        // 3. Algebraic identity (x + 0 = x)
        Instruction {
            id: 5,
            opcode: Opcode::Const {
                dest: Reg(4),
                value: 0,
            },
            block_id: 0,
            is_dead: false,
        },
        Instruction {
            id: 6,
            opcode: Opcode::Add {
                dest: Reg(5),
                src1: Reg(3),
                src2: Reg(4),
            },
            block_id: 0,
            is_dead: false,
        },
        // 4. Multiplication by zero
        Instruction {
            id: 7,
            opcode: Opcode::Mul {
                dest: Reg(6),
                src1: Reg(0),
                src2: Reg(4),
            },
            block_id: 0,
            is_dead: false,
        },
        // 5. Common subexpression
        Instruction {
            id: 8,
            opcode: Opcode::Add {
                dest: Reg(7),
                src1: Reg(1),
                src2: Reg(2),
            },
            block_id: 0,
            is_dead: false,
        },
        // 6. Self-subtraction (x - x = 0)
        Instruction {
            id: 9,
            opcode: Opcode::Sub {
                dest: Reg(8),
                src1: Reg(3),
                src2: Reg(3),
            },
            block_id: 0,
            is_dead: false,
        },
    ];

    println!("Original program:");
    print_program(&instructions);

    // Create optimization pipeline
    let mut manager = PassManager::new()
        .add_pass(PeepholeOptimization::new())
        .add_pass(ConstantFolding::new())
        .add_pass(AlgebraicSimplification::new())
        .add_pass(CommonSubexpressionElimination::new())
        .add_pass(DeadCodeElimination::new())
        .with_max_iterations(10);

    // Run optimizations
    println!("\n=== Running Optimization Pipeline ===");
    let result = manager.run(&mut cfg, &mut instructions);

    println!("\nOptimization Results:");
    println!("  Changed: {}", result.changed);
    println!("  Removed: {} instructions", result.removed_count);
    println!("  Modified: {} instructions", result.modified_count);
    println!("  Added: {} instructions", result.added_count);

    println!("\nOptimized program:");
    print_program(&instructions);

    println!("\n=== Optimizations Applied ===");
    println!("1. Peephole: Eliminated redundant const to r0");
    println!("2. Constant Folding: 10 + 20 = 30");
    println!("3. Algebraic: r3 + 0 simplified");
    println!("4. Algebraic: r0 * 0 = 0");
    println!("5. CSE: Duplicate add eliminated");
    println!("6. Algebraic: r3 - r3 = 0");

    println!("\n=== Benefits ===");
    let original_count = instructions.len();
    let optimized_count = instructions.iter().filter(|i| !i.is_dead).count();
    let reduction = ((original_count - optimized_count) as f64 / original_count as f64) * 100.0;
    println!(
        "Code size: {} → {} instructions ({:.1}% reduction)",
        original_count, optimized_count, reduction
    );
}

fn print_program(instructions: &[Instruction]) {
    for (i, inst) in instructions.iter().enumerate() {
        if inst.is_dead {
            println!("  {:2}: {:?} [DEAD]", i, inst.opcode);
        } else {
            println!("  {:2}: {:?}", i, inst.opcode);
        }
    }
}
