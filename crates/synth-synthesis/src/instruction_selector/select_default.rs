//! The pattern-match / fallback selection path — `select()` and
//! `select_default`.
//!
//! This is the LEGACY layer of the two-selector split (#197): a blind
//! per-op lowering with its own register allocator and no virtual-stack
//! model. Production ARM codegen does NOT enter through here —
//! `arm_backend.rs` calls `select_with_stack` (the direct path, forced by
//! `--relocatable`) exclusively, and `select_with_stack` matches all covered
//! ops before its `_ =>` fallthrough delegates to `select_default`. This
//! path is reachable in full only via the `pub fn select()` API used by
//! tests and benchmarks.
//!
//! Extracted verbatim from `instruction_selector.rs` (RQ-58-SPLIT, #242) —
//! a pure relocation, byte-identical output. The shared lowering core
//! (operand/stack machinery, bounds-check emission, VFP lowering, config)
//! stays in the parent module.

use super::*;

impl InstructionSelector {
    /// Select ARM instructions for a sequence of WASM operations
    pub fn select(&mut self, wasm_ops: &[WasmOp]) -> Result<Vec<ArmInstruction>> {
        let mut arm_instructions = Vec::new();
        let mut index = 0;

        while index < wasm_ops.len() {
            let remaining = &wasm_ops[index..];
            let matches = self.matcher.match_sequence(remaining);

            if let Some(best_match) = matches.first() {
                // Apply the rule to generate ARM instructions
                let arm_ops =
                    self.apply_replacement(&best_match.rule.replacement, &best_match.bindings)?;

                for op in arm_ops {
                    arm_instructions.push(ArmInstruction {
                        op,
                        source_line: Some(index),
                    });
                }

                index += best_match.length;
            } else {
                // No rule matched - generate default instruction(s)
                let arm_ops = self.select_default(&wasm_ops[index])?;
                for op in arm_ops {
                    arm_instructions.push(ArmInstruction {
                        op,
                        source_line: Some(index),
                    });
                }
                index += 1;
            }
        }

        Ok(arm_instructions)
    }

    /// Apply a replacement pattern to generate ARM instructions
    fn apply_replacement(
        &mut self,
        replacement: &Replacement,
        _bindings: &Bindings,
    ) -> Result<Vec<ArmOp>> {
        match replacement {
            Replacement::Identity => {
                // For identity replacement, generate a default instruction
                Ok(vec![ArmOp::Mov {
                    rd: Reg::R0,
                    op2: Operand2::Reg(Reg::R0),
                }])
            }

            Replacement::ArmInstr(op) => {
                // Single ARM instruction
                Ok(vec![op.clone()])
            }

            Replacement::ArmSequence(ops) => {
                // Sequence of ARM instructions
                Ok(ops.clone())
            }

            Replacement::Var(var_name) => Err(synth_core::Error::synthesis(format!(
                "Replacement::Var({var_name}) not implemented — would silently emit NOP"
            ))),

            Replacement::Inline => Err(synth_core::Error::synthesis(
                "Replacement::Inline not implemented — would silently emit NOP".to_string(),
            )),
        }
    }

    /// #709: the `i32.trunc_f32_{s,u}` domain guard (WASM Core §4.3.3), as a
    /// sequence of `ArmOp`s to prepend before the saturating VCVT. Mirrors the
    /// execution-oracle'd guard in the free-function `try_lower_f32`; see there
    /// for the condition-code / NaN reasoning. Trap unless the operand is in the
    /// exactly-representable valid range (signed: `-2^31 <= x < 2^31`; unsigned:
    /// `-1.0 < x < 2^32`). Ordered compares (F32Lt=MI, F32Ge=GE, F32Gt=GT) each
    /// yield 0 on NaN, so a NaN fails the in-range test and falls to the UDF.
    fn f32_trunc_range_guard(&mut self, rd: Reg, sm: VfpReg, signed: bool) -> Vec<ArmOp> {
        let (hi, lo) = if signed {
            (2147483648.0_f32, -2147483648.0_f32) // 2^31, -2^31
        } else {
            (4294967296.0_f32, -1.0_f32) // 2^32, -1.0
        };
        let s_hi = self.alloc_vfp_reg();
        let s_lo = self.alloc_vfp_reg();
        let lower = if signed {
            ArmOp::F32Ge {
                rd,
                sn: sm,
                sm: s_lo,
            } // inclusive x >= -2^31
        } else {
            ArmOp::F32Gt {
                rd,
                sn: sm,
                sm: s_lo,
            } // strict x > -1.0
        };
        vec![
            // Upper bound: trap unless x < hi (also traps NaN).
            ArmOp::F32Const {
                sd: s_hi,
                value: hi,
            },
            ArmOp::F32Lt {
                rd,
                sn: sm,
                sm: s_hi,
            },
            ArmOp::Cmp {
                rn: rd,
                op2: Operand2::Imm(0),
            },
            ArmOp::BCondOffset {
                cond: Condition::NE,
                offset: 0,
            },
            ArmOp::Udf { imm: 0 },
            // Lower bound: trap unless x >= lo (signed) / x > lo (unsigned).
            ArmOp::F32Const {
                sd: s_lo,
                value: lo,
            },
            lower,
            ArmOp::Cmp {
                rn: rd,
                op2: Operand2::Imm(0),
            },
            ArmOp::BCondOffset {
                cond: Condition::NE,
                offset: 0,
            },
            ArmOp::Udf { imm: 0 },
        ]
    }

    /// Select default ARM instruction(s) for a WASM operation (no pattern match)
    /// Returns a sequence of instructions (may include bounds checking for memory ops)
    pub(super) fn select_default(&mut self, wasm_op: &WasmOp) -> Result<Vec<ArmOp>> {
        use WasmOp::*;

        let rd = self.regs.alloc_reg();
        let rn = self.regs.alloc_reg();
        let rm = self.regs.alloc_reg();

        let instrs = match wasm_op {
            // VCR-SEL-001 / RQ-58-RETIRE (#242): the tier-A i32 ALU ops (and
            // I32Rotl below) lower through the Rocq-proved rule table
            // (`crate::sel_dsl::generated::rule_*`) as the ONLY path — the
            // hand-written arms the rules superseded were byte-identical by
            // construction (mirror-pinned since the flip) and are DELETED.
            // Every `rule_*` has its 1:1 Qed theorem in
            // coq/Synth/Synth/VcrSelRules.v.
            I32Add => crate::sel_dsl::generated::rule_i32_add(rd, rn, rm),

            I32Sub => crate::sel_dsl::generated::rule_i32_sub(rd, rn, rm),

            I32Mul => crate::sel_dsl::generated::rule_i32_mul(rd, rn, rm),

            I32And => crate::sel_dsl::generated::rule_i32_and(rd, rn, rm),

            I32Or => crate::sel_dsl::generated::rule_i32_or(rd, rn, rm),

            I32Xor => crate::sel_dsl::generated::rule_i32_xor(rd, rn, rm),

            // Shifts: WASM pops both value (rn) and shift amount (rm) from stack.
            // #682: ARMv7-M register shifts use Rm[7:0] (>= 32 yields 0/sign)
            // while WASM requires amount mod 32 — the Rocq-proved masked rules
            // mask into R12 first (encoder scratch, never allocatable per #212,
            // so no liveness hazard; the same pattern the optimized path always
            // used).
            I32Shl => crate::sel_dsl::generated::rule_i32_shl(rd, rn, rm, Reg::R12)
                .map_err(synth_core::Error::synthesis)?,
            I32ShrS => crate::sel_dsl::generated::rule_i32_shr_s(rd, rn, rm, Reg::R12)
                .map_err(synth_core::Error::synthesis)?,
            I32ShrU => crate::sel_dsl::generated::rule_i32_shr_u(rd, rn, rm, Reg::R12)
                .map_err(synth_core::Error::synthesis)?,

            // Rotate operations: shift amount from stack register
            I32Rotl => {
                // Rotate left by N = Rotate right by (32 - N)
                // RSB rtmp, rm, #32; ROR rd, rn, rtmp
                // Tier-B rule: carries the explicit `rs <> rn` scratch
                // non-aliasing side condition (hypothesis of
                // rule_i32_rotl_correct) — Ok-or-Err, never a silent
                // misassemble.
                let rtmp = self.regs.alloc_reg();
                crate::sel_dsl::generated::rule_i32_rotl(rd, rn, rm, rtmp)
                    .map_err(synth_core::Error::synthesis)?
            }

            I32Rotr => crate::sel_dsl::generated::rule_i32_rotr(rd, rn, rm),

            // Bit count operations — Rocq-proved rules are the only path
            // (RQ-58-RETIRE): clz single-CLZ; ctz the two-instruction RBIT+CLZ
            // scratch=dest shape; popcnt the pseudo-op.
            I32Clz => crate::sel_dsl::generated::rule_i32_clz(rd, rm),

            I32Ctz => crate::sel_dsl::generated::rule_i32_ctz(rd, rm),

            I32Popcnt => crate::sel_dsl::generated::rule_i32_popcnt(rd, rm),

            I32Const(val) => {
                let uval = *val as u32;
                let inverted = !uval;
                if uval <= 0xFFFF {
                    // 0..65535: MOVW handles the full 16-bit range
                    vec![ArmOp::Movw {
                        rd,
                        imm16: uval as u16,
                    }]
                } else if inverted <= 0xFFFF {
                    // Simple bit-inverted patterns: MOVW inverted + MVN
                    // e.g., -1 (0xFFFFFFFF) -> MOVW rd, #0; MVN rd, rd
                    // e.g., -2 (0xFFFFFFFE) -> MOVW rd, #1; MVN rd, rd
                    vec![
                        ArmOp::Movw {
                            rd,
                            imm16: inverted as u16,
                        },
                        ArmOp::Mvn {
                            rd,
                            op2: Operand2::Reg(rd),
                        },
                    ]
                } else {
                    // Full 32-bit range: MOVW low16 + MOVT high16
                    vec![
                        ArmOp::Movw {
                            rd,
                            imm16: (uval & 0xFFFF) as u16,
                        },
                        ArmOp::Movt {
                            rd,
                            imm16: ((uval >> 16) & 0xFFFF) as u16,
                        },
                    ]
                }
            }

            I32Load { offset, .. } => {
                // WASM memory access: address from stack (rn) + static offset
                // R11 is the dedicated memory base register for memory 0
                // Effective address = R11 + rn + offset
                self.generate_load_with_bounds_check(rd, rn, *offset as i32, 4)
            }

            I32Store { offset, .. } => {
                // WASM memory access: address from stack (rn) + static offset
                // R11 is the dedicated memory base register for memory 0
                // Effective address = R11 + rn + offset
                self.generate_store_with_bounds_check(rd, rn, *offset as i32, 4)
            }

            // Sub-word loads (i32)
            I32Load8S { offset, .. } => {
                self.generate_subword_load_with_bounds_check(rd, rn, *offset as i32, 1, true)
            }
            I32Load8U { offset, .. } => {
                self.generate_subword_load_with_bounds_check(rd, rn, *offset as i32, 1, false)
            }
            I32Load16S { offset, .. } => {
                self.generate_subword_load_with_bounds_check(rd, rn, *offset as i32, 2, true)
            }
            I32Load16U { offset, .. } => {
                self.generate_subword_load_with_bounds_check(rd, rn, *offset as i32, 2, false)
            }

            // Sub-word stores (i32)
            I32Store8 { offset, .. } => {
                self.generate_subword_store_with_bounds_check(rd, rn, *offset as i32, 1)
            }
            I32Store16 { offset, .. } => {
                self.generate_subword_store_with_bounds_check(rd, rn, *offset as i32, 2)
            }

            // i64 sub-word loads — load sub-word, extend to i64 register pair
            I64Load8S { offset, .. } => {
                // LDRSB R0, [R11, rn, #offset]; ASR R1, R0, #31 (sign-extend to hi)
                let mut ops = self.generate_subword_load_with_bounds_check(
                    Reg::R0,
                    rn,
                    *offset as i32,
                    1,
                    true,
                );
                ops.push(ArmOp::Asr {
                    rd: Reg::R1,
                    rn: Reg::R0,
                    shift: 31,
                });
                ops
            }
            I64Load8U { offset, .. } => {
                // LDRB R0, [R11, rn, #offset]; MOV R1, #0
                let mut ops = self.generate_subword_load_with_bounds_check(
                    Reg::R0,
                    rn,
                    *offset as i32,
                    1,
                    false,
                );
                ops.push(ArmOp::Mov {
                    rd: Reg::R1,
                    op2: Operand2::Imm(0),
                });
                ops
            }
            I64Load16S { offset, .. } => {
                let mut ops = self.generate_subword_load_with_bounds_check(
                    Reg::R0,
                    rn,
                    *offset as i32,
                    2,
                    true,
                );
                ops.push(ArmOp::Asr {
                    rd: Reg::R1,
                    rn: Reg::R0,
                    shift: 31,
                });
                ops
            }
            I64Load16U { offset, .. } => {
                let mut ops = self.generate_subword_load_with_bounds_check(
                    Reg::R0,
                    rn,
                    *offset as i32,
                    2,
                    false,
                );
                ops.push(ArmOp::Mov {
                    rd: Reg::R1,
                    op2: Operand2::Imm(0),
                });
                ops
            }
            I64Load32S { offset, .. } => {
                // LDR R0, [R11, rn, #offset]; ASR R1, R0, #31
                let mut ops = self.generate_load_with_bounds_check(Reg::R0, rn, *offset as i32, 4);
                ops.push(ArmOp::Asr {
                    rd: Reg::R1,
                    rn: Reg::R0,
                    shift: 31,
                });
                ops
            }
            I64Load32U { offset, .. } => {
                // LDR R0, [R11, rn, #offset]; MOV R1, #0
                let mut ops = self.generate_load_with_bounds_check(Reg::R0, rn, *offset as i32, 4);
                ops.push(ArmOp::Mov {
                    rd: Reg::R1,
                    op2: Operand2::Imm(0),
                });
                ops
            }

            // i64 sub-word stores — store low N bits from i64 register pair
            I64Store8 { offset, .. } => {
                // STRB R0, [R11, rn, #offset] (low byte of low word)
                self.generate_subword_store_with_bounds_check(Reg::R0, rn, *offset as i32, 1)
            }
            I64Store16 { offset, .. } => {
                // STRH R0, [R11, rn, #offset] (low halfword of low word)
                self.generate_subword_store_with_bounds_check(Reg::R0, rn, *offset as i32, 2)
            }
            I64Store32 { offset, .. } => {
                // STR R0, [R11, rn, #offset] (low word)
                self.generate_store_with_bounds_check(Reg::R0, rn, *offset as i32, 4)
            }

            // Memory management
            MemorySize(mem_idx) => {
                // On embedded with fixed memory, return memory size in pages.
                // R10 holds memory size in bytes; divide by 65536 (page size) via LSR #16.
                // #406: R10 is MEMORY 0's size — reading it for memory k > 0
                // silently returned the wrong memory's size. Decline; the
                // per-memory lowering lives in select_with_stack.
                if *mem_idx != 0 {
                    return Err(synth_core::Error::synthesis(format!(
                        "memory.size on memory {mem_idx}: select_default has no \
                         per-memory size lowering (R10 is memory 0's size \
                         register) — multi-memory is lowered only by \
                         select_with_stack on --relocatable (#406)"
                    )));
                }
                vec![ArmOp::MemorySize { rd }]
            }
            MemoryGrow(mem_idx) => {
                // On embedded with fixed memory, always return -1 (cannot grow).
                // #406: `-1` is memory-agnostic, but keep the blind path
                // memory-0-only — a multi-memory module belongs to
                // select_with_stack (--relocatable).
                if *mem_idx != 0 {
                    return Err(synth_core::Error::synthesis(format!(
                        "memory.grow on memory {mem_idx}: multi-memory is lowered \
                         only by select_with_stack on --relocatable (#406)"
                    )));
                }
                vec![ArmOp::MemoryGrow { rd, rn }]
            }

            // VCR-MEM-002 phase 1 (#406): select_default is the blind-alloc
            // fallback — it does not track the operand stack, and it has no
            // per-memory base plumbing. The real multi-memory lowering lives
            // in select_with_stack (--relocatable); here we loud-decline
            // (the GI-FPU-001/#372 contract), never alias memory 0.
            MultiMemory { memory, op } => {
                return Err(synth_core::Error::synthesis(format!(
                    "multi-memory: {op:?} on memory {memory} is lowered only by \
                     the stack-tracking selector (select_with_stack) on the \
                     --relocatable path — select_default would alias it onto \
                     memory 0's base (#406)"
                )));
            }

            // FIXME: select_default LocalGet/Set ignores index (hardcoded SP+0).
            // Currently unreachable because select_with_stack handles these ops.
            // See issue #72.
            LocalGet(_index) => vec![ArmOp::Ldr {
                rd,
                addr: MemAddr::imm(Reg::SP, 0), // Simplified - would use proper frame offset
            }],

            // FIXME: select_default LocalGet/Set ignores index (hardcoded SP+0).
            // Currently unreachable because select_with_stack handles these ops.
            // See issue #72.
            LocalSet(_index) => vec![ArmOp::Str {
                rd,
                addr: MemAddr::imm(Reg::SP, 0),
            }],

            Call(func_idx) => {
                if *func_idx < self.num_imports {
                    // Import call — dispatch through Meld runtime
                    // R0 = import index, then BL __meld_dispatch_import
                    vec![
                        ArmOp::Mov {
                            rd: Reg::R0,
                            op2: Operand2::Imm(*func_idx as i32),
                        },
                        ArmOp::Bl {
                            label: "__meld_dispatch_import".to_string(),
                        },
                    ]
                } else {
                    // Local function call
                    vec![ArmOp::Bl {
                        label: format!("func_{}", func_idx),
                    }]
                }
            }

            CallIndirect {
                type_index,
                table_index,
            } => {
                // Table index is on top of stack (in rn), call target via table lookup.
                // #642/#650: same guard preconditions as the select_with_stack
                // arm — WASM §4.4.8 requires OOB/type-mismatch traps, so
                // without a compile-time table size (for the encoder's bounds
                // guard), a constant table base offset, and a verified
                // closed-world type verdict for THAT table, decline loudly
                // rather than emit an unchecked indirect branch.
                // #275: the SELF-CONTAINED funcref-table lowering (PC-relative
                // flash table) is implemented only by `select_with_stack` —
                // this legacy/demo arm emits the R11 dispatch, which would be
                // the #717 linear-memory collision on a self-contained image.
                // Decline loudly rather than emit it.
                if self.self_contained_funcref_table {
                    return Err(synth_core::Error::synthesis(
                        "call_indirect: the self-contained funcref-table dispatch \
                         is a select_with_stack lowering; this selector path \
                         would emit the colliding R11 dispatch — declining (#275)"
                            .to_string(),
                    ));
                }
                let (table_size, table_byte_offset, null_check, type_check) =
                    self.resolve_call_indirect_guards(*table_index, *type_index)?;
                vec![ArmOp::CallIndirect {
                    rd,
                    type_idx: *type_index,
                    table_index_reg: rn, // Table index from stack
                    table_size,
                    table_byte_offset,
                    // #664: trap on a null (zero-linked) slot at runtime.
                    null_check,
                    // #676: heterogeneous table — runtime type check
                    // against the type-id sidecar.
                    type_check,
                }]
            }

            // Control flow — labels and branches are emitted here.
            // Full structured control flow is handled in select_with_stack;
            // select_default emits a reasonable per-instruction lowering.
            Block => {
                let label = self.alloc_label("block_end");
                vec![ArmOp::Label { name: label }]
            }
            Loop => {
                let label = self.alloc_label("loop_start");
                vec![ArmOp::Label { name: label }]
            }
            Br(depth) => vec![ArmOp::B {
                label: format!("br_target_{}", depth),
            }],
            BrIf(depth) => {
                // Pop condition from stack (in rn), branch if non-zero
                vec![
                    ArmOp::Cmp {
                        rn,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::Bcc {
                        cond: Condition::NE,
                        label: format!("br_if_target_{}", depth),
                    },
                ]
            }
            Return => vec![ArmOp::Bx { rm: Reg::LR }],

            // Locals
            LocalTee(_index) => {
                // Tee is like set but keeps value on stack
                vec![ArmOp::Str {
                    rd,
                    addr: MemAddr::imm(Reg::SP, 0),
                }]
            }

            // Comparisons
            I32Eq => vec![ArmOp::Cmp {
                rn,
                op2: Operand2::Reg(rm),
            }],
            I32Ne => vec![ArmOp::Cmp {
                rn,
                op2: Operand2::Reg(rm),
            }],
            I32LtS | I32LtU | I32LeS | I32LeU | I32GtS | I32GtU | I32GeS | I32GeU => {
                vec![ArmOp::Cmp {
                    rn,
                    op2: Operand2::Reg(rm),
                }]
            }

            // Division and remainder (ARMv7-M+)
            // WASM requires trap on divide-by-zero. ARM SDIV/UDIV silently return 0,
            // so we emit an explicit zero-check: CMP rm, #0 / BNE skip / UDF #0.
            // FIXME: select_default I32DivS missing INT_MIN/-1 overflow trap.
            // Currently unreachable because select_with_stack handles this op.
            // See issue #72.
            I32DivS => {
                let seq = vec![
                    // Trap if divisor == 0
                    ArmOp::Cmp {
                        rn: rm,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::BCondOffset {
                        cond: Condition::NE,
                        offset: 0,
                    },
                    ArmOp::Udf { imm: 0 },
                    // Signed division
                    ArmOp::Sdiv { rd, rn, rm },
                ];
                contracts::division::verify_trap_guard_length(seq.len());
                seq
            }
            I32DivU => {
                let seq = vec![
                    // Trap if divisor == 0
                    ArmOp::Cmp {
                        rn: rm,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::BCondOffset {
                        cond: Condition::NE,
                        offset: 0,
                    },
                    ArmOp::Udf { imm: 0 },
                    // Unsigned division
                    ArmOp::Udiv { rd, rn, rm },
                ];
                contracts::division::verify_trap_guard_length(seq.len());
                seq
            }
            I32RemS => {
                // Signed remainder: quotient = SDIV tmp, rn, rm
                // remainder = MLS rd, tmp, rm, rn  (rd = rn - tmp * rm)
                let rtmp = self.regs.alloc_reg();
                let seq = vec![
                    // Trap if divisor == 0
                    ArmOp::Cmp {
                        rn: rm,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::BCondOffset {
                        cond: Condition::NE,
                        offset: 0,
                    },
                    ArmOp::Udf { imm: 0 },
                    ArmOp::Sdiv { rd: rtmp, rn, rm },
                    ArmOp::Mls {
                        rd,
                        rn: rtmp,
                        rm,
                        ra: rn,
                    },
                ];
                contracts::division::verify_trap_guard_length(seq.len());
                seq
            }
            I32RemU => {
                // Unsigned remainder: quotient = UDIV tmp, rn, rm
                // remainder = MLS rd, tmp, rm, rn  (rd = rn - tmp * rm)
                let rtmp = self.regs.alloc_reg();
                let seq = vec![
                    // Trap if divisor == 0
                    ArmOp::Cmp {
                        rn: rm,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::BCondOffset {
                        cond: Condition::NE,
                        offset: 0,
                    },
                    ArmOp::Udf { imm: 0 },
                    ArmOp::Udiv { rd: rtmp, rn, rm },
                    ArmOp::Mls {
                        rd,
                        rn: rtmp,
                        rm,
                        ra: rn,
                    },
                ];
                contracts::division::verify_trap_guard_length(seq.len());
                seq
            }

            // Sign extension operations — Rocq-proved rules, the only path
            // (increment 6, RQ-59-SUBTRACT)
            I32Extend8S => crate::sel_dsl::generated::rule_i32_extend8_s(rd, rm),
            I32Extend16S => crate::sel_dsl::generated::rule_i32_extend16_s(rd, rm),

            // Comparison: equal to zero (unary)
            I32Eqz => vec![ArmOp::Cmp {
                rn,
                op2: Operand2::Imm(0),
            }],

            // Structural control flow delimiters — handled structurally in select_with_stack
            Nop => vec![ArmOp::Nop],
            End => vec![ArmOp::Nop],
            Drop => vec![ArmOp::Nop],
            If => {
                // In select_default (non-stack mode), emit a placeholder CMP + BEQ
                let else_label = self.alloc_label("else");
                vec![
                    ArmOp::Cmp {
                        rn,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::Bcc {
                        cond: Condition::EQ,
                        label: else_label,
                    },
                ]
            }
            Else => {
                // Jump over else block (end of then block)
                let end_label = self.alloc_label("if_end");
                vec![
                    ArmOp::B {
                        label: end_label.clone(),
                    },
                    ArmOp::Label { name: end_label },
                ]
            }

            // Trap: unreachable should generate an undefined instruction
            Unreachable => vec![ArmOp::Udf { imm: 0 }],

            // br_table: emit a jump table via TBB/TBH or cascading branches
            BrTable { targets, default } => {
                // Emit a cascading compare-and-branch sequence
                // index is in rn (from stack)
                let mut instrs = Vec::new();
                for (i, target) in targets.iter().enumerate() {
                    // CMP rn, #i
                    instrs.push(ArmOp::Cmp {
                        rn,
                        op2: Operand2::Imm(i as i32),
                    });
                    // BEQ to target label
                    instrs.push(ArmOp::Bcc {
                        cond: Condition::EQ,
                        label: format!("br_table_target_{}", target),
                    });
                }
                // Default: unconditional branch
                instrs.push(ArmOp::B {
                    label: format!("br_table_target_{}", default),
                });
                instrs
            }
            GlobalGet(index) => {
                // WASM globals are stored in a globals table in memory.
                // R9 is the dedicated globals base register (set up by runtime startup).
                // #643: slot offsets are the SUM of earlier globals' widths
                // (i64/f64 slots are 8 bytes) — `idx * 4` only when every
                // earlier global is i32/f32. This blind (0,1)-stack-effect
                // path has no register-pair representation for the value, so
                // a 64-bit global access is DECLINED loudly rather than
                // truncated to one word (`select_with_stack` lowers the pair).
                if self.global_slot_width(*index) != 4 {
                    return Err(synth_core::Error::synthesis(format!(
                        "global.get {index} reads a {}-byte (i64/f64/v128) global — \
                         the single-register selector path cannot lower a pair; \
                         refusing to truncate to 32 bits (#643)",
                        self.global_slot_width(*index)
                    )));
                }
                vec![ArmOp::Ldr {
                    rd,
                    addr: MemAddr::imm(Reg::R9, self.global_slot_offset(*index)),
                }]
            }
            GlobalSet(index) => {
                // Store value from source register to the global's slot.
                // R9 is the dedicated globals base register.
                // #643: type-aware offset + loud decline for 64-bit globals
                // (see GlobalGet above — storing one word dropped the hi half).
                if self.global_slot_width(*index) != 4 {
                    return Err(synth_core::Error::synthesis(format!(
                        "global.set {index} writes a {}-byte (i64/f64/v128) global — \
                         the single-register selector path cannot lower a pair; \
                         refusing to drop the high word (#643)",
                        self.global_slot_width(*index)
                    )));
                }
                vec![ArmOp::Str {
                    rd,
                    addr: MemAddr::imm(Reg::R9, self.global_slot_offset(*index)),
                }]
            }
            Select => {
                // WASM select: pops condition, val2, val1 from stack;
                // pushes val1 if condition != 0, else val2.
                // CMP rcond, #0; MOV rd, rval1; IT EQ; MOVEQ rd, rval2 —
                // from the Rocq-proved rule (increment 5, RQ-58-SELDSL),
                // which carries the rd <> rm side condition (the EQ override
                // must not read a value the MOV just destroyed) Ok-or-Err.
                let rcond = self.regs.alloc_reg();
                crate::sel_dsl::generated::rule_i32_select_default(rd, rn, rm, rcond)
                    .map_err(synth_core::Error::synthesis)?
            }

            // ===== i64 operations using register pairs on 32-bit ARM =====
            // Convention: i64 operand 1 in (R0,R1), operand 2 in (R2,R3), result in (R0,R1)
            I64Const(val) => {
                vec![ArmOp::I64Const {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    value: *val,
                }]
            }

            I64ExtendI32S => {
                vec![ArmOp::I64ExtendI32S {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rn: Reg::R0,
                }]
            }

            I64ExtendI32U => {
                vec![ArmOp::I64ExtendI32U {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rn: Reg::R0,
                }]
            }

            I32WrapI64 => {
                // Just take the low 32 bits (R0) — effectively a no-op if result is in R0
                vec![ArmOp::I32WrapI64 {
                    rd: Reg::R0,
                    rnlo: Reg::R0,
                }]
            }

            // Narrow i64 sign-extends — Rocq-proved rules, the only path
            // (increment 6, RQ-59-SUBTRACT). The fixed (R0, R1, R0) shape
            // satisfies the rd_hi <> rd_lo side condition.
            I64Extend8S | I64Extend16S | I64Extend32S => {
                crate::sel_dsl::i64_extend_narrow_rule(wasm_op, Reg::R0, Reg::R1, Reg::R0)
                    .expect("narrow i64 sign-extend op has a generated rule")
                    .map_err(synth_core::Error::synthesis)?
            }

            // i64 arithmetic: ADDS/ADC for add, SUBS/SBC for sub — the
            // Rocq-proved pair rules are the only path (RQ-58-RETIRE). The
            // fixed R0:R1 += R2:R3 in-place shape satisfies all three pair
            // aliasing side conditions (rd_hi≠rd_lo, rd_lo≠rn_hi,
            // rd_lo≠rm_hi), so the Err arm is unreachable here but stays
            // loud, never silent.
            I64Add => crate::sel_dsl::generated::rule_i64_add(
                Reg::R0,
                Reg::R1,
                Reg::R0,
                Reg::R1,
                Reg::R2,
                Reg::R3,
            )
            .map_err(synth_core::Error::synthesis)?,

            I64Sub => crate::sel_dsl::generated::rule_i64_sub(
                Reg::R0,
                Reg::R1,
                Reg::R0,
                Reg::R1,
                Reg::R2,
                Reg::R3,
            )
            .map_err(synth_core::Error::synthesis)?,

            // i64 bitwise: operate on each half independently
            I64And => crate::sel_dsl::generated::rule_i64_and(
                Reg::R0,
                Reg::R1,
                Reg::R0,
                Reg::R1,
                Reg::R2,
                Reg::R3,
            )
            .map_err(synth_core::Error::synthesis)?,

            I64Or => crate::sel_dsl::generated::rule_i64_or(
                Reg::R0,
                Reg::R1,
                Reg::R0,
                Reg::R1,
                Reg::R2,
                Reg::R3,
            )
            .map_err(synth_core::Error::synthesis)?,

            I64Xor => crate::sel_dsl::generated::rule_i64_xor(
                Reg::R0,
                Reg::R1,
                Reg::R0,
                Reg::R1,
                Reg::R2,
                Reg::R3,
            )
            .map_err(synth_core::Error::synthesis)?,

            // i64 comparisons: compare register pairs, result 0/1 in R0.
            // i64.eqz is the SetCondZ-shape rule (no side conditions — the
            // pseudo-op reads both halves before writing).
            I64Eqz => crate::sel_dsl::generated::rule_i64_eqz(Reg::R0, Reg::R0, Reg::R1),

            // Binary i64 comparisons: one I64SetCond pseudo-op over the fixed
            // (R0:R1, R2:R3) pairs, from the generated Rocq-proved rule — the
            // only path (RQ-58-RETIRE).
            I64Eq | I64Ne | I64LtS | I64LtU | I64LeS | I64LeU | I64GtS | I64GtU | I64GeS
            | I64GeU => crate::sel_dsl::i64_setcond_rule(
                wasm_op,
                Reg::R0,
                Reg::R0,
                Reg::R1,
                Reg::R2,
                Reg::R3,
            )
            .expect("binary i64 comparison has a generated rule"),

            // i64 multiply / shifts: single pseudo-ops over the fixed
            // (R0:R1, R2:R3) pairs — from the Rocq-proved rules, the only
            // path (RQ-58-SELDSL wires select_default too; the in-place
            // R0:R1 shape satisfies the rd_hi <> rd_lo side condition, and
            // the Err arm stays loud, never silent).
            I64Mul | I64Shl | I64ShrU | I64ShrS => crate::sel_dsl::i64_pair_bin_rule(
                wasm_op,
                Reg::R0,
                Reg::R1,
                Reg::R0,
                Reg::R1,
                Reg::R2,
                Reg::R3,
            )
            .expect("binary i64 pair op has a generated rule")
            .map_err(synth_core::Error::synthesis)?,

            // i64 rotates: amount is the single low-half register R2.
            I64Rotl | I64Rotr => {
                crate::sel_dsl::i64_rot_rule(wasm_op, Reg::R0, Reg::R1, Reg::R0, Reg::R1, Reg::R2)
                    .expect("i64 rotate op has a generated rule")
                    .map_err(synth_core::Error::synthesis)?
            }

            // i64 bit manipulation: single pseudo-op, count into R0.
            I64Clz | I64Ctz | I64Popcnt => {
                crate::sel_dsl::i64_unary_count_rule(wasm_op, Reg::R0, Reg::R0, Reg::R1)
                    .expect("i64 bit-count op has a generated rule")
            }

            // i64 division/remainder
            I64DivS => {
                vec![ArmOp::I64DivS {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    rmlo: Reg::R2,
                    rmhi: Reg::R3,
                    // #494: select_default never consumes fact marks — full guards.
                    elide_zero_guard: false,
                    elide_overflow_guard: false,
                }]
            }

            I64DivU => {
                vec![ArmOp::I64DivU {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    rmlo: Reg::R2,
                    rmhi: Reg::R3,
                    elide_zero_guard: false,
                }]
            }

            I64RemS => {
                vec![ArmOp::I64RemS {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    rmlo: Reg::R2,
                    rmhi: Reg::R3,
                    elide_zero_guard: false,
                }]
            }

            I64RemU => {
                vec![ArmOp::I64RemU {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    rmlo: Reg::R2,
                    rmhi: Reg::R3,
                    elide_zero_guard: false,
                }]
            }

            // i64 memory operations (8-byte access, bounds-checked like i32)
            I64Load { offset, .. } => self.generate_i64_load_with_bounds_check(rn, *offset as i32),

            I64Store { offset, .. } => {
                self.generate_i64_store_with_bounds_check(rn, *offset as i32)
            }

            // ===== F32 operations =====
            // Path A: no FPU → error
            // Path B: FPU present → generate VFP instructions
            // Path C: unsupported ops → specific error
            F32Add if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Add { sd, sn, sm }]
            }
            F32Sub if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Sub { sd, sn, sm }]
            }
            F32Mul if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Mul { sd, sn, sm }]
            }
            F32Div if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Div { sd, sn, sm }]
            }

            F32Abs if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Abs { sd, sm }]
            }
            F32Neg if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Neg { sd, sm }]
            }
            F32Sqrt if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Sqrt { sd, sm }]
            }

            F32Eq if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Eq { rd, sn, sm }]
            }
            F32Ne if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Ne { rd, sn, sm }]
            }
            F32Lt if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Lt { rd, sn, sm }]
            }
            F32Le if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Le { rd, sn, sm }]
            }
            F32Gt if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Gt { rd, sn, sm }]
            }
            F32Ge if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Ge { rd, sn, sm }]
            }

            F32Const(val) if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                vec![ArmOp::F32Const { sd, value: *val }]
            }

            F32Load { offset, .. } if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let addr_reg = self.regs.alloc_reg();
                vec![ArmOp::F32Load {
                    sd,
                    addr: MemAddr::reg_imm(Reg::R11, addr_reg, *offset as i32),
                }]
            }
            F32Store { offset, .. } if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let addr_reg = self.regs.alloc_reg();
                vec![ArmOp::F32Store {
                    sd,
                    addr: MemAddr::reg_imm(Reg::R11, addr_reg, *offset as i32),
                }]
            }

            F32ConvertI32S if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                vec![ArmOp::F32ConvertI32S { sd, rm }]
            }
            F32ConvertI32U if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                vec![ArmOp::F32ConvertI32U { sd, rm }]
            }

            F32ReinterpretI32 if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                vec![ArmOp::F32ReinterpretI32 { sd, rm }]
            }
            I32ReinterpretF32 if self.fpu.is_some() => {
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::I32ReinterpretF32 { rd, sm }]
            }

            // #709: domain guard before the saturating VCVT (see the identical,
            // execution-oracle'd guard in `try_lower_f32`). This `select_default`
            // path is the legacy pattern-matcher's fallback and is NOT reached by
            // the shipping compile path (`select_with_stack`), so it is untested
            // by the #709 differential — guarded here for soundness parity only.
            I32TruncF32S if self.fpu.is_some() => {
                let sm = self.alloc_vfp_reg();
                let mut seq = self.f32_trunc_range_guard(rd, sm, true);
                seq.push(ArmOp::I32TruncF32S { rd, sm });
                seq
            }
            I32TruncF32U if self.fpu.is_some() => {
                let sm = self.alloc_vfp_reg();
                let mut seq = self.f32_trunc_range_guard(rd, sm, false);
                seq.push(ArmOp::I32TruncF32U { rd, sm });
                seq
            }

            // #782a: the NONTRAPPING trunc_sat forms — bare saturating VCVT,
            // deliberately WITHOUT the #709 range guard (§4.3.2 trunc_sat:
            // NaN → 0, out-of-range saturates; VCVT round-toward-zero does
            // exactly that). Guard-free is the CORRECT lowering here, not a
            // soundness hole.
            I32TruncSatF32S if self.fpu.is_some() => {
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::I32TruncF32S { rd, sm }]
            }
            I32TruncSatF32U if self.fpu.is_some() => {
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::I32TruncF32U { rd, sm }]
            }

            // #782: i64-target trunc_sat — SELECTOR ASYMMETRY. The shipping
            // path `select_with_stack` LOWERS all four i64 forms (v0.49 finale,
            // `lower_i64_trunc_sat_from_f64`, branch-free FP decompose). This
            // register-blind `select_default` fallback has no i64 register-pair
            // machinery, so it still LOUD-declines here (decline > wrong). Both
            // CLI paths (self-contained `--all-exports` and `--relocatable`)
            // route these ops through `select_with_stack`, so this arm is not
            // reached for a normal compile; it remains an honest safety net.
            op @ (I64TruncSatF32S | I64TruncSatF32U) if self.fpu.is_some() => {
                return Err(synth_core::Error::synthesis(format!(
                    "{op:?}: select_default has no i64 register-pair path — the \
                     shipping select_with_stack selector lowers it (#782)"
                )));
            }
            // #869: same selector asymmetry for the TRAPPING f32->i64
            // truncations — `select_with_stack` lowers them (i64 domain guard
            // + promote + #782 decompose); this register-blind fallback
            // loud-declines (decline > wrong).
            op @ (I64TruncF32S | I64TruncF32U) if self.fpu.is_some() => {
                return Err(synth_core::Error::synthesis(format!(
                    "{op:?}: select_default has no i64 register-pair path — the \
                     shipping select_with_stack selector lowers it (#869)"
                )));
            }

            // F32 rounding — LOUD-DECLINED on ARM32 (v0.54 L2, #851; the same
            // move #538 m4 made for F32Min/F32Max). The legacy `ArmOp::F32
            // {Ceil,Floor,Trunc,Nearest}` pseudo-op expands to an FPSCR-RMode
            // set + `VCVT.S32.F32` + `VCVT.F32.S32` ROUND-TRIP THROUGH A
            // 32-BIT INTEGER (see `encode_thumb_f32_rounding` /
            // `encode_arm_f32_rounding`). VCVT SATURATES, so outside i32 range
            // the result is wrong, not merely imprecise: `ceil(1e30)` would
            // give 2147483648.0, `ceil(±inf)` a finite bound and `ceil(NaN)`
            // 0.0, where WASM §4.3.3 returns 1e30 / ±inf / NaN. Those inputs
            // were unreachable while the decoder dropped the op; now that it
            // delivers them (so aarch64 can lower its one-instruction FRINT),
            // ARM32 must honest-reject rather than expose the latent #709-class
            // miscompile. The fix is the f32 twin of the shipping F64 rounding
            // path (`VRINT{P,M,Z,N}.F32`, FPv5) — a later increment.
            op @ (F32Ceil | F32Floor | F32Trunc | F32Nearest) if self.fpu.is_some() => {
                return Err(synth_core::Error::synthesis(format!(
                    "{op:?} not supported on ARM32: the available lowering is a \
                     saturating VCVT round-trip through i32, which is not \
                     WASM-correct for |x| >= 2^31, ±inf or NaN — declined until \
                     the VRINT.F32 lowering lands"
                )));
            }
            // F32 min/max — LOUD-DECLINED on ARM32 (#538 m4): the legacy
            // `ArmOp::F32Min/F32Max` pseudo-op encodes a naive VCMP +
            // IT-conditional VMOV select, which returns the WRONG operand for
            // NaN mixes (WASM requires NaN propagation) and for ±0 pairs
            // (WASM: min(+0,-0) = -0). These ops were previously unreachable
            // (dropped at decode); now that the decoder delivers them for the
            // aarch64 backend, ARM32 must honest-reject rather than expose the
            // latent miscompile. The fix is the f32 twin of
            // `encode_thumb_f64_minmax` (VMINNM/VMAXNM + IT VS VADD fix-up) —
            // a later increment.
            op @ (F32Min | F32Max) if self.fpu.is_some() => {
                return Err(synth_core::Error::synthesis(format!(
                    "{op:?} not supported on ARM32: the available lowering is not \
                     WASM NaN/±0-correct — declined until the VMINNM+fix-up twin \
                     of F64Min/F64Max lands"
                )));
            }
            // F32 copysign — emit ArmOp variant, encoder expands to VABS + sign extraction
            F32Copysign if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Copysign { sd, sn, sm }]
            }

            // #869: lowered by the shipping `select_with_stack` (exact
            // two-word f64 build + round-to-odd fixup + demote); this
            // register-blind fallback keeps the honest decline.
            op @ (F32ConvertI64S | F32ConvertI64U) if self.fpu.is_some() => {
                return Err(synth_core::Error::synthesis(format!(
                    "{op:?}: select_default has no i64 register-pair path — the \
                     shipping select_with_stack selector lowers it (#869)"
                )));
            }

            op @ F32DemoteF64 if self.fpu.is_some() => {
                return Err(synth_core::Error::synthesis(format!(
                    "{op:?} not supported on single-precision target {}",
                    self.target_name
                )));
            }

            // Path A: all F32 ops with no FPU → error
            op @ (F32Add
            | F32Sub
            | F32Mul
            | F32Div
            | F32Eq
            | F32Ne
            | F32Lt
            | F32Le
            | F32Gt
            | F32Ge
            | F32Abs
            | F32Neg
            | F32Ceil
            | F32Floor
            | F32Trunc
            | F32Nearest
            | F32Sqrt
            | F32Min
            | F32Max
            | F32Copysign
            | F32Const(_)
            | F32Load { .. }
            | F32Store { .. }
            | F32ConvertI32S
            | F32ConvertI32U
            | F32ConvertI64S
            | F32ConvertI64U
            | F32DemoteF64
            | F32ReinterpretI32
            | I32ReinterpretF32
            | I32TruncF32S
            | I32TruncF32U
            | I32TruncSatF32S
            | I32TruncSatF32U
            | I64TruncSatF32S
            | I64TruncSatF32U
            | I64TruncF32S
            | I64TruncF32U) => {
                return Err(synth_core::Error::synthesis(format!(
                    "target {} has no FPU; cannot compile {op:?}",
                    self.target_name
                )));
            }

            // ===== F64 operations =====
            // Path A: target has double-precision FPU (e.g., Cortex-M7DP) → generate VFP-D
            // Path B: no DP FPU (no FPU or single-precision only) → error
            //
            // F64 values live in VFP D-registers (D0..D15). Each D-register
            // aliases a pair of S-registers, so the encoder reuses the same
            // VFP register file. Allocation follows the same wrap-around
            // policy as f32 (alloc_vfp_dreg).

            // F64 Arithmetic
            F64Add if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Add { dd, dn, dm }]
            }
            F64Sub if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Sub { dd, dn, dm }]
            }
            F64Mul if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Mul { dd, dn, dm }]
            }
            F64Div if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Div { dd, dn, dm }]
            }

            // F64 Math Functions (unary)
            F64Abs if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Abs { dd, dm }]
            }
            F64Neg if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Neg { dd, dm }]
            }
            F64Sqrt if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Sqrt { dd, dm }]
            }

            // F64 Comparisons (result in integer register)
            F64Eq if self.has_double_fpu() => {
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Eq { rd, dn, dm }]
            }
            F64Ne if self.has_double_fpu() => {
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Ne { rd, dn, dm }]
            }
            F64Lt if self.has_double_fpu() => {
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Lt { rd, dn, dm }]
            }
            F64Le if self.has_double_fpu() => {
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Le { rd, dn, dm }]
            }
            F64Gt if self.has_double_fpu() => {
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Gt { rd, dn, dm }]
            }
            F64Ge if self.has_double_fpu() => {
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Ge { rd, dn, dm }]
            }

            // F64 Constants and Memory
            F64Const(val) if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                vec![ArmOp::F64Const { dd, value: *val }]
            }
            F64Load { offset, .. } if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let addr_reg = self.regs.alloc_reg();
                vec![ArmOp::F64Load {
                    dd,
                    addr: MemAddr::reg_imm(Reg::R11, addr_reg, *offset as i32),
                }]
            }
            F64Store { offset, .. } if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let addr_reg = self.regs.alloc_reg();
                vec![ArmOp::F64Store {
                    dd,
                    addr: MemAddr::reg_imm(Reg::R11, addr_reg, *offset as i32),
                }]
            }

            // F64 Conversions (i32 ↔ f64, f32 → f64, bitcasts)
            F64ConvertI32S if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                vec![ArmOp::F64ConvertI32S { dd, rm }]
            }
            F64ConvertI32U if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                vec![ArmOp::F64ConvertI32U { dd, rm }]
            }
            F64PromoteF32 if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F64PromoteF32 { dd, sm }]
            }
            F64ReinterpretI64 if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                // i64 lives in a register pair (rmlo, rmhi). Use the
                // existing integer allocator for both halves.
                let rmlo = self.regs.alloc_reg();
                let rmhi = self.regs.alloc_reg();
                vec![ArmOp::F64ReinterpretI64 { dd, rmlo, rmhi }]
            }
            I64ReinterpretF64 if self.has_double_fpu() => {
                let dm = self.alloc_vfp_dreg();
                let rdlo = self.regs.alloc_reg();
                let rdhi = self.regs.alloc_reg();
                vec![ArmOp::I64ReinterpretF64 { rdlo, rdhi, dm }]
            }
            I32TruncF64S if self.has_double_fpu() => {
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::I32TruncF64S { rd, dm }]
            }
            I32TruncF64U if self.has_double_fpu() => {
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::I32TruncF64U { rd, dm }]
            }

            // #782a: nontrapping trunc_sat from f64 — bare saturating
            // VCVT.{S32,U32}.F64, guard-free BY DESIGN (§4.3.2: NaN → 0,
            // out-of-range saturates — exactly what the VCVT does).
            I32TruncSatF64S if self.has_double_fpu() => {
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::I32TruncF64S { rd, dm }]
            }
            I32TruncSatF64U if self.has_double_fpu() => {
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::I32TruncF64U { rd, dm }]
            }

            // F64 rounding pseudo-ops — emit ArmOp variants; encoder expands
            // them into FPSCR-rounding-mode + VCVT sequences.
            F64Ceil if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Ceil { dd, dm }]
            }
            F64Floor if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Floor { dd, dm }]
            }
            F64Trunc if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Trunc { dd, dm }]
            }
            F64Nearest if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Nearest { dd, dm }]
            }
            // F64 min/max — emit ArmOp variants, encoder expands to VCMP + conditional VMOV
            F64Min if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Min { dd, dn, dm }]
            }
            F64Max if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Max { dd, dn, dm }]
            }
            // F64 copysign — emit ArmOp variant, encoder expands to bitwise sequence
            F64Copysign if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Copysign { dd, dn, dm }]
            }

            // F64 i64 conversions: i64 register pairs are not implemented in
            // this register-blind `select_default` fallback. Surface a typed
            // error. NOTE (#782/#869): ALL of these forms ARE lowered on the
            // shipping `select_with_stack` path (trunc_sat via the v0.49
            // word-decompose; the trapping `I64TruncF64*` via the i64 domain
            // guard + decompose and `F64ConvertI64*` via the exact two-word
            // build, both #869). They decline here only because
            // select_default lacks the pair machinery, and a normal compile
            // never routes them through this arm.
            op @ (F64ConvertI64S | F64ConvertI64U | I64TruncF64S | I64TruncF64U
            | I64TruncSatF64S | I64TruncSatF64U)
                if self.has_double_fpu() =>
            {
                return Err(synth_core::Error::synthesis(format!(
                    "{op:?}: select_default has no i64 register-pair path — the \
                     shipping select_with_stack selector lowers it (#869)"
                )));
            }

            // Path B: F64 op but target lacks double-precision FPU.
            // The validate_instructions feature gate at codegen time emits
            // a "requires double-precision FPU" error for any leaked F64
            // ArmOp; this path catches the op *before* selection and gives
            // a target-specific message.
            op @ (F64Add
            | F64Sub
            | F64Mul
            | F64Div
            | F64Eq
            | F64Ne
            | F64Lt
            | F64Le
            | F64Gt
            | F64Ge
            | F64Abs
            | F64Neg
            | F64Ceil
            | F64Floor
            | F64Trunc
            | F64Nearest
            | F64Sqrt
            | F64Min
            | F64Max
            | F64Copysign
            | F64Const(_)
            | F64Load { .. }
            | F64Store { .. }
            | F64ConvertI32S
            | F64ConvertI32U
            | F64ConvertI64S
            | F64ConvertI64U
            | F64PromoteF32
            | F64ReinterpretI64
            | I64ReinterpretF64
            | I64TruncF64S
            | I64TruncF64U
            | I32TruncF64S
            | I32TruncF64U
            | I32TruncSatF64S
            | I32TruncSatF64U
            | I64TruncSatF64S
            | I64TruncSatF64U) => {
                let msg = if self.fpu.is_some() {
                    // Single-precision FPU target (e.g., Cortex-M4F): VFP-D
                    // instructions exist as encodings but the hardware lacks
                    // the double-precision unit to execute them.
                    format!(
                        "target {} lacks double-precision FPU; cannot compile {op:?}",
                        self.target_name
                    )
                } else {
                    format!(
                        "target {} has no FPU; cannot compile {op:?}",
                        self.target_name
                    )
                };
                return Err(synth_core::Error::synthesis(msg));
            }

            // ===== v128 SIMD operations =====
            // Path A: Helium present → generate MVE instructions
            // Path B: no Helium → error

            // v128 Constants
            V128Const(bytes) if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveConst { qd, bytes: *bytes }]
            }

            // v128 Load/Store
            V128Load { offset, .. } if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveLoad {
                    qd,
                    addr: MemAddr::reg_imm(Reg::R11, rn, *offset as i32),
                }]
            }
            V128Store { offset, .. } if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveStore {
                    qd,
                    addr: MemAddr::reg_imm(Reg::R11, rn, *offset as i32),
                }]
            }

            // v128 Bitwise
            V128And if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveAnd { qd, qn, qm }]
            }
            V128Or if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveOrr { qd, qn, qm }]
            }
            V128Xor if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveEor { qd, qn, qm }]
            }
            V128Not if self.has_helium => {
                let qd = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveMvn { qd, qm }]
            }
            V128AndNot if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveBic { qd, qn, qm }]
            }

            // i8x16 arithmetic
            I8x16Add if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveAddI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16Sub if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveSubI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16Neg if self.has_helium => {
                let qd = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveNegI {
                    qd,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16Splat if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveDup {
                    qd,
                    rn,
                    size: MveSize::S8,
                }]
            }
            I8x16ExtractLaneS(lane) | I8x16ExtractLaneU(lane) if self.has_helium => {
                let qn = self.alloc_qreg();
                vec![ArmOp::MveExtractLane {
                    rd,
                    qn,
                    lane: *lane,
                    size: MveSize::S8,
                }]
            }
            I8x16ReplaceLane(lane) if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveInsertLane {
                    qd,
                    rn,
                    lane: *lane,
                    size: MveSize::S8,
                }]
            }

            // i8x16 comparisons
            I8x16Eq if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpEqI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16Ne if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpNeI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16LtS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLtS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16LtU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLtU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16GtS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGtS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16GtU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGtU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16LeS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLeS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16LeU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLeU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16GeS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGeS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16GeU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGeU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }

            // i16x8 arithmetic
            I16x8Add if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveAddI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8Sub if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveSubI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8Mul if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveMulI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8Neg if self.has_helium => {
                let qd = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveNegI {
                    qd,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8Splat if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveDup {
                    qd,
                    rn,
                    size: MveSize::S16,
                }]
            }
            I16x8ExtractLaneS(lane) | I16x8ExtractLaneU(lane) if self.has_helium => {
                let qn = self.alloc_qreg();
                vec![ArmOp::MveExtractLane {
                    rd,
                    qn,
                    lane: *lane,
                    size: MveSize::S16,
                }]
            }
            I16x8ReplaceLane(lane) if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveInsertLane {
                    qd,
                    rn,
                    lane: *lane,
                    size: MveSize::S16,
                }]
            }

            // i16x8 comparisons
            I16x8Eq if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpEqI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8Ne if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpNeI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8LtS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLtS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8LtU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLtU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8GtS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGtS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8GtU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGtU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8LeS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLeS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8LeU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLeU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8GeS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGeS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8GeU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGeU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }

            // i32x4 arithmetic
            I32x4Add if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveAddI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4Sub if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveSubI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4Mul if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveMulI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4Neg if self.has_helium => {
                let qd = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveNegI {
                    qd,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4Splat if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveDup {
                    qd,
                    rn,
                    size: MveSize::S32,
                }]
            }
            I32x4ExtractLane(lane) if self.has_helium => {
                let qn = self.alloc_qreg();
                vec![ArmOp::MveExtractLane {
                    rd,
                    qn,
                    lane: *lane,
                    size: MveSize::S32,
                }]
            }
            I32x4ReplaceLane(lane) if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveInsertLane {
                    qd,
                    rn,
                    lane: *lane,
                    size: MveSize::S32,
                }]
            }

            // i32x4 comparisons
            I32x4Eq if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpEqI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4Ne if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpNeI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4LtS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLtS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4LtU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLtU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4GtS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGtS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4GtU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGtU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4LeS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLeS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4LeU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLeU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4GeS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGeS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4GeU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGeU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }

            // i64x2 arithmetic (MVE supports 32-bit element sizes natively;
            // 64-bit uses pairs of 32-bit ops or widening instructions)
            I64x2Add if self.has_helium => {
                // VADD.I32 operates on 32-bit lanes; i64x2 is two 64-bit values.
                // Pseudo-op: encoder expands to ADDS/ADC pairs per lane.
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveAddI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2Sub if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveSubI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2Neg if self.has_helium => {
                let qd = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveNegI {
                    qd,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2Splat if self.has_helium => {
                // Splat 64-bit value: duplicate low 32 bits to lanes 0,2
                // and high 32 bits to lanes 1,3
                let qd = self.alloc_qreg();
                vec![ArmOp::MveDup {
                    qd,
                    rn,
                    size: MveSize::S32,
                }]
            }
            I64x2ExtractLane(lane) if self.has_helium => {
                let qn = self.alloc_qreg();
                vec![ArmOp::MveExtractLane {
                    rd,
                    qn,
                    lane: *lane,
                    size: MveSize::S32,
                }]
            }
            I64x2ReplaceLane(lane) if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveInsertLane {
                    qd,
                    rn,
                    lane: *lane,
                    size: MveSize::S32,
                }]
            }

            // i64x2 comparisons and mul — emit as pseudo-ops for now
            I64x2Mul if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveMulI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2Eq if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpEqI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2Ne if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpNeI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2LtS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLtS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2GtS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGtS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2LeS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLeS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2GeS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGeS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }

            // f32x4 floating-point SIMD
            F32x4Add if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveAddF32 { qd, qn, qm }]
            }
            F32x4Sub if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveSubF32 { qd, qn, qm }]
            }
            F32x4Mul if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveMulF32 { qd, qn, qm }]
            }
            F32x4Div if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveDivF32 { qd, qn, qm }]
            }
            F32x4Abs if self.has_helium => {
                let qd = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveAbsF32 { qd, qm }]
            }
            F32x4Neg if self.has_helium => {
                let qd = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveNegF32 { qd, qm }]
            }
            F32x4Sqrt if self.has_helium => {
                let qd = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveSqrtF32 { qd, qm }]
            }
            F32x4Eq if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpEqF32 { qd, qn, qm }]
            }
            F32x4Ne if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpNeF32 { qd, qn, qm }]
            }
            F32x4Lt if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLtF32 { qd, qn, qm }]
            }
            F32x4Le if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLeF32 { qd, qn, qm }]
            }
            F32x4Gt if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGtF32 { qd, qn, qm }]
            }
            F32x4Ge if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGeF32 { qd, qn, qm }]
            }
            F32x4Splat if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveDupF32 { qd, rn }]
            }
            F32x4ExtractLane(lane) if self.has_helium => {
                let qn = self.alloc_qreg();
                vec![ArmOp::MveExtractLaneF32 {
                    rd,
                    qn,
                    lane: *lane,
                }]
            }
            F32x4ReplaceLane(lane) if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveReplaceLaneF32 {
                    qd,
                    rn,
                    lane: *lane,
                }]
            }

            // i8x16.shuffle / i8x16.swizzle — complex, not yet implemented
            op @ (I8x16Shuffle(_) | I8x16Swizzle) if self.has_helium => {
                return Err(synth_core::Error::synthesis(format!(
                    "{op:?} not yet implemented for Helium MVE"
                )));
            }

            // All SIMD ops without Helium → error
            op @ (V128Const(_)
            | V128Load { .. }
            | V128Store { .. }
            | V128And
            | V128Or
            | V128Xor
            | V128Not
            | V128AndNot
            | I8x16Add
            | I8x16Sub
            | I8x16Neg
            | I8x16Eq
            | I8x16Ne
            | I8x16LtS
            | I8x16LtU
            | I8x16GtS
            | I8x16GtU
            | I8x16LeS
            | I8x16LeU
            | I8x16GeS
            | I8x16GeU
            | I8x16Splat
            | I8x16ExtractLaneS(_)
            | I8x16ExtractLaneU(_)
            | I8x16ReplaceLane(_)
            | I8x16Shuffle(_)
            | I8x16Swizzle
            | I16x8Add
            | I16x8Sub
            | I16x8Mul
            | I16x8Neg
            | I16x8Eq
            | I16x8Ne
            | I16x8LtS
            | I16x8LtU
            | I16x8GtS
            | I16x8GtU
            | I16x8LeS
            | I16x8LeU
            | I16x8GeS
            | I16x8GeU
            | I16x8Splat
            | I16x8ExtractLaneS(_)
            | I16x8ExtractLaneU(_)
            | I16x8ReplaceLane(_)
            | I32x4Add
            | I32x4Sub
            | I32x4Mul
            | I32x4Neg
            | I32x4Eq
            | I32x4Ne
            | I32x4LtS
            | I32x4LtU
            | I32x4GtS
            | I32x4GtU
            | I32x4LeS
            | I32x4LeU
            | I32x4GeS
            | I32x4GeU
            | I32x4Splat
            | I32x4ExtractLane(_)
            | I32x4ReplaceLane(_)
            | I64x2Add
            | I64x2Sub
            | I64x2Mul
            | I64x2Neg
            | I64x2Eq
            | I64x2Ne
            | I64x2LtS
            | I64x2GtS
            | I64x2LeS
            | I64x2GeS
            | I64x2Splat
            | I64x2ExtractLane(_)
            | I64x2ReplaceLane(_)
            | F32x4Add
            | F32x4Sub
            | F32x4Mul
            | F32x4Div
            | F32x4Abs
            | F32x4Neg
            | F32x4Sqrt
            | F32x4Eq
            | F32x4Ne
            | F32x4Lt
            | F32x4Le
            | F32x4Gt
            | F32x4Ge
            | F32x4Splat
            | F32x4ExtractLane(_)
            | F32x4ReplaceLane(_)) => {
                return Err(synth_core::Error::synthesis(format!(
                    "SIMD operation {op:?} requires Helium MVE (Cortex-M55), \
                     but target {} does not have Helium",
                    self.target_name
                )));
            }

            // Bulk memory (#374). `select_default` is the blind-alloc fallback —
            // it round-robins rd/rn/rm without tracking the operand stack, so it
            // cannot correctly pop the 3 operands (dst, src/val, len) a copy/fill
            // needs. The real lowering lives in `select_with_stack`; here we
            // honestly loud-skip (the GI-FPU-001 / #372 contract) rather than emit
            // a wrong 3-operand sequence from mis-allocated registers.
            MemoryCopy | MemoryFill => {
                return Err(synth_core::Error::synthesis(format!(
                    "bulk-memory {wasm_op:?} is lowered only by the stack-tracking \
                     selector (select_with_stack); select_default cannot pop its \
                     3 operands"
                )));
            }
        };
        Ok(instrs)
    }
}
