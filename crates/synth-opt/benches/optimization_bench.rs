use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use synth_cfg::CfgBuilder;
use synth_opt::*;

/// Create a complex program with many optimization opportunities
fn create_complex_program(size: usize) -> (synth_cfg::Cfg, Vec<Instruction>) {
    let mut builder = CfgBuilder::new();
    for _ in 0..(size * 2) {
        builder.add_instruction();
    }
    let cfg = builder.build();

    let mut instructions = Vec::new();
    for i in 0..size {
        // Add constant
        instructions.push(Instruction {
            id: i * 2,
            opcode: Opcode::Const {
                dest: Reg(i as u32 * 2),
                value: (i as i32) * 10,
            },
            block_id: 0,
            is_dead: false,
        });

        // Add operation (with opportunity for constant folding)
        if i > 0 {
            instructions.push(Instruction {
                id: i * 2 + 1,
                opcode: Opcode::Add {
                    dest: Reg(i as u32 * 2 + 1),
                    src1: Reg((i as u32 - 1) * 2),
                    src2: Reg(i as u32 * 2),
                },
                block_id: 0,
                is_dead: false,
            });
        }
    }

    (cfg, instructions)
}

fn bench_constant_folding(c: &mut Criterion) {
    let mut group = c.benchmark_group("constant_folding");

    for size in [10, 50, 100].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let (mut cfg, mut instructions) = create_complex_program(size);
                let mut pass = ConstantFolding::new();
                black_box(pass.run(&mut cfg, &mut instructions))
            });
        });
    }

    group.finish();
}

fn bench_cse(c: &mut Criterion) {
    let mut group = c.benchmark_group("cse");

    for size in [10, 50, 100].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let (mut cfg, mut instructions) = create_complex_program(size);
                let mut pass = CommonSubexpressionElimination::new();
                black_box(pass.run(&mut cfg, &mut instructions))
            });
        });
    }

    group.finish();
}

fn bench_algebraic_simplification(c: &mut Criterion) {
    let mut group = c.benchmark_group("algebraic_simplification");

    for size in [10, 50, 100].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let (mut cfg, mut instructions) = create_complex_program(size);
                let mut pass = AlgebraicSimplification::new();
                black_box(pass.run(&mut cfg, &mut instructions))
            });
        });
    }

    group.finish();
}

fn bench_dce(c: &mut Criterion) {
    let mut group = c.benchmark_group("dce");

    for size in [10, 50, 100].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let (mut cfg, mut instructions) = create_complex_program(size);
                let mut pass = DeadCodeElimination::new();
                black_box(pass.run(&mut cfg, &mut instructions))
            });
        });
    }

    group.finish();
}

fn bench_full_pipeline(c: &mut Criterion) {
    let mut group = c.benchmark_group("full_pipeline");

    for size in [10, 50, 100].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter(|| {
                let (mut cfg, mut instructions) = create_complex_program(size);

                let mut manager = PassManager::new()
                    .add_pass(PeepholeOptimization::new())
                    .add_pass(ConstantFolding::new())
                    .add_pass(AlgebraicSimplification::new())
                    .add_pass(StrengthReduction::new())
                    .add_pass(CopyPropagation::new())
                    .add_pass(InstructionCombining::new())
                    .add_pass(CommonSubexpressionElimination::new())
                    .add_pass(DeadCodeElimination::new())
                    .with_max_iterations(5);

                black_box(manager.run(&mut cfg, &mut instructions))
            });
        });
    }

    group.finish();
}

fn bench_strength_reduction(c: &mut Criterion) {
    c.bench_function("strength_reduction", |b| {
        b.iter(|| {
            let mut builder = CfgBuilder::new();
            for _ in 0..10 {
                builder.add_instruction();
            }
            let mut cfg = builder.build();

            let mut instructions = vec![
                Instruction {
                    id: 0,
                    opcode: Opcode::Const { dest: Reg(0), value: 8 },
                    block_id: 0,
                    is_dead: false,
                },
                Instruction {
                    id: 1,
                    opcode: Opcode::Const { dest: Reg(1), value: 16 },
                    block_id: 0,
                    is_dead: false,
                },
                Instruction {
                    id: 2,
                    opcode: Opcode::Mul {
                        dest: Reg(2),
                        src1: Reg(10),
                        src2: Reg(0),
                    },
                    block_id: 0,
                    is_dead: false,
                },
                Instruction {
                    id: 3,
                    opcode: Opcode::Mul {
                        dest: Reg(3),
                        src1: Reg(11),
                        src2: Reg(1),
                    },
                    block_id: 0,
                    is_dead: false,
                },
            ];

            let mut pass = StrengthReduction::new();
            black_box(pass.run(&mut cfg, &mut instructions))
        });
    });
}

criterion_group!(
    benches,
    bench_constant_folding,
    bench_cse,
    bench_algebraic_simplification,
    bench_dce,
    bench_full_pipeline,
    bench_strength_reduction,
);
criterion_main!(benches);
