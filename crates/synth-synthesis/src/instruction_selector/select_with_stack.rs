//! The direct selection path — `select_with_stack`.
//!
//! This is the PRODUCTION layer of the two-selector split (#197): the
//! virtual-stack-tracking, AAPCS-compliant selector that `arm_backend.rs`
//! calls exclusively and that `--relocatable` forces. It models the WASM
//! operand stack explicitly, allocates from the shared register pool,
//! handles structured control flow (block/loop/if/else/br/br_if/br_table/
//! return/call), spilling, and frame layout. Ops it does not cover fall
//! through its `_ =>` arm to the legacy pattern-match path
//! (`select_default`, the sibling module).
//!
//! Extracted verbatim from `instruction_selector.rs` (RQ-58-SPLIT, #242) —
//! a pure relocation, byte-identical output. The shared lowering core
//! (operand/stack machinery, bounds-check emission, VFP lowering, call
//! marshalling, config) stays in the parent module.

use super::*;

impl InstructionSelector {
    /// This method properly tracks the WASM virtual stack and generates code that
    /// uses r0-r3 for the first 4 parameters per AAPCS. Handles WASM structured
    /// control flow (block, loop, if/else, br, br_if, br_table, return, call).
    pub fn select_with_stack(
        &mut self,
        wasm_ops: &[WasmOp],
        num_params: u32,
    ) -> Result<Vec<ArmInstruction>> {
        use WasmOp::*;

        // Pre-flight: catch obvious wasm stack underflow as a typed error
        // before we walk the ops. The fuzz harness `wasm_ops_lower_or_error`
        // intentionally feeds malformed `Vec<WasmOp>` and expects `Err`, not
        // a panic deep in the selector's pop sequence (see PR #117).
        synth_core::wasm_stack_check::check_no_underflow(wasm_ops)?;

        // #1093 pre-flight: a PARAMETER-taking block type declines as a typed
        // error, never a panic — block params pop BELOW the #313 frame-entry
        // checkpoint, so `Else`'s `split_off` panics (and the else-less shape
        // is silently wrong). Guards direct library callers who set
        // `block_arity`; the CLI paths are declined in `compile_wasm_to_arm`.
        // Mechanism + measured matrix: `synth_core::find_param_block_type`.
        if let Some((what, ord, arity)) =
            synth_core::find_param_block_type(wasm_ops, &self.block_arity)
        {
            return Err(synth_core::Error::synthesis(
                synth_core::param_block_decline_msg("the ARM selector", what, ord, arity),
            ));
        }

        // #359/#503: AAPCS stack arguments. We pass args past r0..r3 on the
        // outgoing stack and read incoming stack-passed params from the
        // caller's stack. The incoming-param homing (`compute_local_layout` →
        // `incoming_params`, offset `frame_size+24+nsaa_k`) and the outgoing
        // store (`emit_stack_args`, offset `(k-4)*4`) are both GENERIC in the
        // param/arg index — no fixed ≤8 structure — so an arbitrary scalar count
        // lowers correctly. The real bound is the 12-bit `[sp,#imm]` immediate
        // (0..4095), enforced over the finalized layout at the homing site
        // (incoming, below) and at `emit_stack_args` (outgoing). #503 lifts the
        // old conservative `num_params > 8` / `arg_count > 8` refusals — they
        // dropped legitimate falcon helpers (10- and 25-param functions) that the
        // generic machinery handles. The 12-bit guards remain the Ok-or-Err
        // backstop (#180/#185): never silently emit an out-of-range encoding.
        //
        // #503-i64 (the falcon func_58/func_163 remainder): a 64-bit param that
        // AAPCS passes ON THE STACK is now lowered too. `aapcs_param_layout`
        // (declared widths — op-stream inference can't see an unused i64 param)
        // assigns every param either a register (pair, even-aligned, for a wide
        // one) or an NSAA stack offset (8-byte-aligned for a wide one; a narrow
        // param AFTER any stack-spilled param is itself stack-passed — AAPCS
        // C.5, no register back-fill: the pre-fix `index_to_reg` fallback read
        // such a param from a WRONG register, e.g. p3 of `(i64 i32 i32 i32)`
        // from R3 = p2). Wide incoming slots are read/written with
        // I64Ldr/I64Str through `layout.incoming_params`.
        //
        // #518 Ok-or-Err (#180/#185): the ONE remaining decline — an i64/f64
        // param that is REGISTER-resident in a function that FRAME-BACKS its
        // params: `has_call` (params spill to the frame to survive the call's
        // caller-saved clobber, #204/#193) or the pair-exhaustion retry
        // (`param_backing_on_exhaustion`). There the `param_slots` path would
        // size the i64 param's slot from `i64_set`, which does not include
        // params, dropping the high half. A STACK-passed wide param is exempt:
        // it lives in the caller's frame (never in a clobberable register), so
        // it needs no backing slot and survives calls by construction. Falls
        // back to a loud skip (warning + absent symbol), never wrong code.
        // (Empty `params_i64` ⇒ all-i32 ⇒ this is a no-op and every existing
        // fixture stays byte-identical.)
        // GI-FPU-002 phase 3 (#369): on a DOUBLE-precision target an f64 param
        // is homed in a VFP D-register (AAPCS-VFP), so the core walk skips it —
        // exactly like an f32 param. Everywhere else (soft-float; and m4f,
        // where the function declines below) the slice is empty and the f64
        // keeps its core-pair treatment via `params_i64`.
        let params_f64_vfp: Vec<bool> = if matches!(self.fpu, Some(FPUPrecision::Double)) {
            self.params_f64.clone()
        } else {
            Vec::new()
        };
        let param_layout = aapcs_param_layout(
            num_params,
            &self.params_i64,
            &self.params_f32,
            &params_f64_vfp,
        );
        let has_reg_i64_param = (0..num_params).any(|i| {
            self.params_i64.get(i as usize).copied().unwrap_or(false)
                && param_layout.regs.contains_key(&i)
        });
        if has_reg_i64_param {
            // #837: the frame-backing-with-CALL case is now LOWERED. A
            // register-resident i64/f64 param in a function that contains a call
            // homes its AAPCS even-aligned pair (R0:R1 or R2:R3) into an 8-byte
            // frame slot in the prologue (`param_slots` now sizes it from the
            // DECLARED width, above), survives the call's caller-saved clobber
            // in the frame, and is reloaded as a pair via `I64Ldr` after — the
            // store/reload machinery (prologue homing, LocalGet/Set/Tee) was
            // already `is_i64`-aware; only the slot width was wrong. The
            // past-R3 STACK-passed wide param never reached this guard
            // (`param_layout.regs` excludes it) — it flows through
            // `incoming_params` and has compiled since #503-i64.
            //
            // The one residual that still LOUD-DECLINES by name (decline >
            // guess): the register-pair-exhaustion RETRY
            // (`param_backing_on_exhaustion`) forces param backing on a
            // call-FREE function whose i64-param homing across the retry's
            // spill choreography is UNVERIFIED by a red→green fixture — kept
            // declining until it has its own execution oracle rather than
            // silently enabled.
            if self.param_backing_on_exhaustion {
                return Err(synth_core::Error::synthesis(
                    "#518/#837: an i64/f64 param in the register-pair-exhaustion \
                     retry (force_param_backing on a call-free function) is not \
                     yet lowered — the frame-backing-with-call case is handled, \
                     but the exhaustion retry lacks an execution oracle"
                        .to_string(),
                ));
            }
        }

        // #359: size of the outgoing stack-argument region = the max over all
        // Call/CallIndirect sites of `max(0, arg_count - 4) * 4`, rounded up to 8.
        // Reserved at the BOTTOM of the frame (offset 0) by `compute_local_layout`.
        // 0 when every call passes <=4 args — the frame is then byte-identical to
        // the pre-#359 layout. `saturating_sub` avoids the u32 underflow that would
        // otherwise inflate the region for every small-arg call.
        let mut max_stack_args: u32 = 0;
        for op in wasm_ops {
            let arg_count = match op {
                Call(func_idx) => {
                    // Meld dispatch imports take no AAPCS args (index in R0).
                    let is_import = *func_idx < self.num_imports;
                    if is_import && !self.relocatable {
                        0
                    } else {
                        self.func_arg_counts
                            .get(*func_idx as usize)
                            .copied()
                            .unwrap_or(0)
                    }
                }
                CallIndirect { type_index, .. } => self
                    .type_arg_counts
                    .get(*type_index as usize)
                    .copied()
                    .unwrap_or(0),
                _ => continue,
            };
            // #503: no conservative >8 cap — `emit_stack_args` is generic in the
            // arg index and its 12-bit `[sp,#imm]` guard is the real backstop.
            max_stack_args = max_stack_args.max(arg_count.saturating_sub(4));
        }
        let outgoing_arg_bytes = ((max_stack_args as i32) * 4 + 7) & !7;

        let mut instructions = Vec::new();

        // Function prologue: save callee-saved registers and LR, then
        // allocate the local-variable frame.
        //
        // AAPCS requires 8-byte aligned SP at call sites. Pushing an even
        // number of registers (6: R4-R8, LR) maintains alignment, and the
        // frame_size below is rounded to 8 to preserve it.
        instructions.push(ArmInstruction {
            op: ArmOp::Push {
                regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::LR],
            },
            source_line: None,
        });

        // GI-FPU-002 phase 3 (#369): does any direct call in this function
        // cross a FLOAT ABI boundary (float args or a float result)? Such a
        // call needs the VFP call-spill area (arg staging + result liveness)
        // even when the caller's own op stream has no float-scope op — the
        // signature tables live on `self`, so the flag is computed here and
        // passed into the free layout function.
        let calls_float_boundary = wasm_ops.iter().any(|op| {
            let WasmOp::Call(fi) = op else { return false };
            let i = *fi as usize;
            self.callee_ret_f32.get(i).copied().unwrap_or(false)
                || self.callee_ret_f64.get(i).copied().unwrap_or(false)
                || self
                    .callee_params_f32
                    .get(i)
                    .is_some_and(|p| p.iter().any(|&f| f))
                || self
                    .callee_params_f64
                    .get(i)
                    .is_some_and(|p| p.iter().any(|&f| f))
        });

        // #1069 (RQ-60-VFPPRESSURE increment 1): the AEABI conversion route —
        // active only on a single-precision FPU target under `--relocatable`
        // (the linker is what resolves the `__aeabi_*` symbols; see the
        // rationale block above `is_aeabi_i64_f32_routed_op`). A routed op
        // emits a `bl`, so the layout must reserve the call machinery's frame
        // areas exactly as for a wasm call.
        let aeabi_route = matches!(self.fpu, Some(FPUPrecision::Single)) && self.relocatable;
        let aeabi_builtin_calls = aeabi_route && wasm_ops.iter().any(is_aeabi_i64_f32_routed_op);

        // Compute non-param local layout (offsets + total frame size).
        let layout = compute_local_layout(
            wasm_ops,
            num_params,
            &self.params_i64,
            &self.params_f32,
            &params_f64_vfp,
            &self.func_ret_i64,
            &self.type_ret_i64,
            &self.func_arg_counts,
            &self.type_arg_counts,
            // #881: the VFP spill rung hands out slots from the same shared
            // pool, so it must force the area exactly like the integer rung.
            // #1069: the frame-home lever hands out PERMANENT slots from the
            // same pool — listed here defensively even though the backend
            // only ever sets it together with the VFP rung flag (a caller
            // setting it alone would otherwise get slots aliasing the #204
            // param homes: a silent miscompile, not a decline).
            self.spill_on_exhaustion || self.vfp_spill_on_exhaustion || self.vfp_frame_home_locals,
            self.param_backing_on_exhaustion,
            calls_float_boundary,
            aeabi_builtin_calls,
            outgoing_arg_bytes,
            self.i64_spill_slots,
        );
        // #359 Ok-or-Err (#180/#185): an incoming stack-passed param is read via
        // `ldr rd,[sp,#off]` where `off = frame_size + 24 + nsaa_k` and
        // `frame_size` is unbounded (a function with a large locals frame). The
        // Thumb-2 `ldr [sp,#imm]` immediate is 12-bit (0..4095); refuse rather
        // than silently emit an out-of-range encoding. Checked once here over the
        // finalized layout instead of at each use site. A wide (i64/f64) param's
        // hi half is read 4 bytes above its lo, so its bound is `off + 4`.
        if let Some(max_off) = layout
            .incoming_params
            .values()
            .map(|&(off, is_wide)| off + if is_wide { 4 } else { 0 })
            .max()
            && max_off > 4095
        {
            return Err(synth_core::Error::synthesis(format!(
                "#503: incoming stack-param offset {max_off} exceeds the 12-bit \
                 [sp,#imm] range (frame too large for the stack-argument path)"
            )));
        }
        // Allocate stack space for non-param locals so they don't alias the
        // callee-saved-register spill area (which immediately follows SP
        // after Push above).
        if layout.frame_size > 0 {
            instructions.push(ArmInstruction {
                op: ArmOp::Sub {
                    rd: Reg::SP,
                    rn: Reg::SP,
                    op2: Operand2::Imm(layout.frame_size),
                },
                source_line: None,
            });
        }

        // #457/#990: WASM zero-initializes non-param locals, so a local read
        // NOT DOMINATED by a write must observe 0 — not the caller garbage the
        // old param-count inference exposed (the local was homed in a parameter
        // register), and not stale frame memory (#990: a `local.set` on one arm
        // of a `br_if` precedes the merge-point read in op order but the branch
        // jumps past it — the pre-#990 linear rule leaked previous-frame stack
        // bytes there). Zero the frame slot of every such local once at entry;
        // an i64 local zeroes both words of its 8-byte slot. Locals whose
        // defining write dominates every read (the straight-line common case)
        // are untouched, so those functions keep a byte-identical prologue.
        // R4 is a safe scratch: it is pushed above, no
        // body value lives in it yet, and a promoted local homed in R4 is
        // write-before-read by construction (`compute_local_promotion` declines
        // read-first locals).
        let rbw_zero_init: Vec<(i32, bool)> = read_before_write_locals(wasm_ops, num_params)
            .iter()
            .filter_map(|idx| layout.locals.get(idx).copied())
            .collect();
        if !rbw_zero_init.is_empty() {
            instructions.push(ArmInstruction {
                op: ArmOp::Mov {
                    rd: Reg::R4,
                    op2: Operand2::Imm(0),
                },
                source_line: None,
            });
            for (off, is_i64) in rbw_zero_init {
                instructions.push(ArmInstruction {
                    op: ArmOp::Str {
                        rd: Reg::R4,
                        addr: MemAddr::imm(Reg::SP, off),
                    },
                    source_line: None,
                });
                if is_i64 {
                    instructions.push(ArmInstruction {
                        op: ArmOp::Str {
                            rd: Reg::R4,
                            addr: MemAddr::imm(Reg::SP, off + 4),
                        },
                        source_line: None,
                    });
                }
            }
        }

        // Virtual operand stack: each entry is a register-resident or spilled
        // value (#171). i64 values track only the lo register/slot.
        let mut stack: Vec<StackVal> = Vec::new();
        // i64 register-pair spill slots (#171), reused across the function.
        // Pool size follows `self.i64_spill_slots` (#587 pool-grow rung) and
        // must match the area `compute_local_layout` reserved above.
        let mut spill = SpillState::with_slots(layout.i64_spill_base, self.i64_spill_slots);
        spill.spill_on_exhaustion = self.spill_on_exhaustion;
        spill.vfp_spill_on_exhaustion = self.vfp_spill_on_exhaustion;
        spill.vfp_frame_home_locals = self.vfp_frame_home_locals;
        spill.area_reserved = layout.spill_area_reserved;
        // Next available register for temporaries (start after params)
        let mut next_temp = num_params.min(4) as u8;

        // Control flow tracking
        let mut cf = ControlFlowManager::new();
        cf.enter_function();
        // Stack of open control constructs for branch target resolution.
        // For blocks/ifs: label is the end label; for loops: the start label.
        // #509: each entry also carries the blocktype arity (from the decoder's
        // ordinal side-table) and the block's designated result register — see
        // [`BlockLabel`].
        let mut block_labels: Vec<BlockLabel> = Vec::new();
        // #509: ordinal of the NEXT Block/Loop/If op in the stream — the key
        // into `self.block_arity` (ordinal-keyed so op-stream rewrites that
        // don't touch control ops, e.g. the #539 memory.grow fold, stay
        // aligned).
        let mut ctrl_ord: usize = 0;
        // Stack of (else_label, end_label) for if/else blocks
        let mut if_labels: Vec<(String, String)> = Vec::new();
        // #313: per-if-block operand-stack checkpoint (vstack depth captured at
        // `If`, after popping the condition). The result arity of an
        // `if (result …)` is observable as (vstack depth − checkpoint).
        let mut if_checkpoints: Vec<usize> = Vec::new();
        // #313: per-if-block reservation of the THEN-arm's result registers.
        // Captured at `Else` (the then-arm's results, popped off and truncated
        // back to the checkpoint so the else-arm starts from the same stack
        // shape) and threaded into the temp/pair/reload allocators across the
        // else-arm — exactly as those result regs were protected in the buggy
        // code by sitting on the vstack. Popped at the matching `End`, where
        // the else-arm's result registers are reconciled INTO the then-arm's
        // (a `mov R_then, R_else` on the else path when they differ). Each
        // inner `Vec` is one if-block's then-arm results, top-most-last.
        let mut if_then_results: Vec<Vec<StackVal>> = Vec::new();

        // Map of local index -> register
        let mut local_to_reg: std::collections::HashMap<u32, Reg> =
            std::collections::HashMap::new();
        // First 4 params are in r0-r3.
        // #518: register homes follow the AAPCS core-register assignment
        // (`aapcs_param_regs`) — an i64 param takes an even-aligned pair, so e.g.
        // `(i32, i64)` puts the i64 in R2:R3, not the sequential R1:R2 that the
        // old `index_to_reg(i)` mapping wrongly used. For an all-i32 signature
        // this is identical to `index_to_reg(i)`, so non-i64-param functions are
        // byte-identical. (Frame-backing i64 params are declined above, so any
        // `param_slots` entry reached here is i32 — its sequential `index_to_reg`
        // already equals the AAPCS reg; left unchanged to minimise the diff.)
        // #204/#193: a param the function reads is spilled to a frame slot at
        // entry and accessed only through it, so it can never be clobbered in
        // its home register between reads. Params with no slot (unused) stay
        // register-backed via local_to_reg.
        let param_aapcs = &param_layout.regs;
        for i in 0..num_params.min(4) {
            if let Some(&(off, is_i64)) = layout.param_slots.get(&i) {
                // #503-i64: `param_slots` only contains REGISTER-resident
                // params now, so the AAPCS map has this index. #719 phase 2:
                // the home must come from the AAPCS-VFP-aware map, NOT the raw
                // `index_to_reg(i)` — under mixed f32/int params the integer
                // pool skips f32 indices (e.g. `(f32, i32)` homes the i32 in
                // R0, not R1), and backing the wrong register fed the callee
                // caller garbage (caught by the xhome execution differential).
                // For an all-i32 signature the two maps are identical, so
                // every previously-compiling function is byte-identical.
                let reg = param_aapcs.get(&i).copied().ok_or_else(|| {
                    synth_core::Error::synthesis(format!(
                        "param {i} has a frame-backing slot but no AAPCS home \
                         register (compiler bug: param_slots/aapcs mismatch)"
                    ))
                })?;
                let op = if is_i64 {
                    ArmOp::I64Str {
                        rdlo: reg,
                        rdhi: i64_pair_hi(reg)?,
                        addr: MemAddr::imm(Reg::SP, off),
                    }
                } else {
                    ArmOp::Str {
                        rd: reg,
                        addr: MemAddr::imm(Reg::SP, off),
                    }
                };
                instructions.push(ArmInstruction {
                    op,
                    source_line: None,
                });
            } else if let Some(&reg) = param_aapcs.get(&i) {
                local_to_reg.insert(i, reg);
            }
            // else: stack-passed (index < 4 only when a wide param
            // even-align-spilled, #503-i64) — reads/writes route through
            // `layout.incoming_params`; there is no register home.
        }

        let mut i64_locals = infer_i64_locals(
            wasm_ops,
            &self.func_ret_i64,
            &self.type_ret_i64,
            &self.func_arg_counts,
            &self.type_arg_counts,
        );
        // #518: an i64/f64 PARAM is 64-bit by signature even if it is only READ
        // (never `local.set`/`tee`), which `infer_i64_locals` — driven by
        // LocalSet/Tee/Call result widths — cannot see. Seed those indices so a
        // `LocalGet` of an i64 param pushes a `StackVal::i64` (whose hi register
        // is reserved via `i64_pair_hi`) instead of an i32 entry that left the hi
        // unreserved — the exact direct-path #518 mechanism (a following
        // `i64.const` was then allocated into the param's hi register).
        // GI-FPU-002 phase 3 (#369): a D-HOMED f64 param (double-precision
        // target) is NOT a core-register pair — `params_i64` lumps i64/f64 by
        // width, but its home is the VFP D-register, so seeding it here would
        // make `LocalGet` push a phantom core pair. Skip the VFP-homed ones.
        for (k, &wide) in self.params_i64.iter().take(num_params as usize).enumerate() {
            if wide && !params_f64_vfp.get(k).copied().unwrap_or(false) {
                i64_locals.insert(k as u32);
            }
        }

        // VCR-RA local promotion (#390, #242): choose non-param i32 locals to keep
        // in callee-saved registers (r4..r8) instead of frame slots, and seed them
        // into `local_to_reg` BEFORE the `param_regs` snapshot below. That makes the
        // existing machinery do the work: `LocalGet` reads the register via the
        // `local_to_reg.get` branch; the #193 param-reservation (param_last_read)
        // protects the promoted register from temp/pair/reload allocation until its
        // last read; and `free_callee_saved` won't hand it out as call scratch. The
        // only new lowering is the `LocalSet`/`LocalTee` promotion arm (mov reg,val).
        // Off ⇒ empty map ⇒ frame-slot path unchanged (frozen gates green).
        let promoted = if self.local_promote {
            compute_local_promotion(wasm_ops, num_params, &i64_locals)
        } else {
            std::collections::HashMap::new()
        };
        for (&local_idx, &reg) in &promoted {
            local_to_reg.insert(local_idx, reg);
        }

        // #193/#210: a register-backed param (call-free function — call functions
        // frame-back via param_slots) lives in r0..r3 and is NOT on the operand
        // stack, so the temp/pair allocators (which avoid only `stack_live_regs`)
        // can hand its register out for a temp/constant/reload under pressure,
        // clobbering it before a later read. gale's `control_step_decide`:
        // `coolant_c`=param2=r2, the constant 80 lands in r2 → `subs r3,r2,r2`.
        // Snapshot the register-backed params + each one's last read so every
        // allocation reserves a param whose value is still needed.
        let param_regs: Vec<(u32, Reg)> = local_to_reg.iter().map(|(&p, &r)| (p, r)).collect();
        let mut param_last_read: std::collections::HashMap<u32, usize> =
            std::collections::HashMap::new();
        for (i, op) in wasm_ops.iter().enumerate() {
            if let LocalGet(p) | LocalTee(p) = op
                && param_regs.iter().any(|(pp, _)| pp == p)
            {
                param_last_read.insert(*p, i);
            }
        }
        // #663: the linear scan above is blind to loop BACK-EDGES — a param
        // read inside a `Loop..End` span is re-executed every iteration, so
        // its value is live until the loop exits, not until the (linearly)
        // last read. Pre-fix, a parameter-bounded counting loop lost the
        // bound's reservation right after the loop-top compare, and the
        // induction increment was allocated into the bound's home register
        // (`adds r0, r7, #1` clobbered n in r0 → loop exited after one
        // iteration). Extend each last read to the End of every enclosing
        // loop, iterating to fixpoint so a read in an inner loop extends to
        // the outermost enclosing loop's End (its back-edge re-executes the
        // read too). Spans are contiguous and properly nested, so extending
        // only the maximum read index is sound: any earlier read's enclosing
        // loop that ends after the max read must also contain the max read.
        let loop_spans: Vec<(usize, usize)> = {
            let mut spans = Vec::new();
            let mut open: Vec<(bool, usize)> = Vec::new(); // (is_loop, start)
            for (i, op) in wasm_ops.iter().enumerate() {
                match op {
                    WasmOp::Loop => open.push((true, i)),
                    WasmOp::Block | WasmOp::If => open.push((false, i)),
                    WasmOp::End => {
                        if let Some((true, start)) = open.pop() {
                            spans.push((start, i));
                        }
                    }
                    _ => {}
                }
            }
            // A loop left open at stream end (implicit function-body End)
            // conservatively extends to the last op.
            for (is_loop, start) in open {
                if is_loop {
                    spans.push((start, wasm_ops.len().saturating_sub(1)));
                }
            }
            spans
        };
        for last in param_last_read.values_mut() {
            let mut changed = true;
            while changed {
                changed = false;
                for &(start, end) in &loop_spans {
                    if *last > start && *last < end {
                        *last = end;
                        changed = true;
                    }
                }
            }
        }
        let live_param_regs = |at: usize| -> Vec<Reg> {
            let mut out = Vec::new();
            for (p, r) in &param_regs {
                if param_last_read.get(p).is_some_and(|&last| last >= at) {
                    out.push(*r);
                    // #518: an i64 param occupies a register PAIR (lo in `r`, hi in
                    // `i64_pair_hi(r)`). Reserve the hi half too — otherwise a
                    // constant/temp allocated into it clobbers the param's high
                    // word before the i64 op reads it (the direct-path #518 bug:
                    // `movw r1,#K` overwrote R1 = hi of an i64 param in R0:R1).
                    if i64_locals.contains(p)
                        && let Ok(hi) = i64_pair_hi(*r)
                    {
                        out.push(hi);
                    }
                }
            }
            out
        };

        // GI-FPU-002 (#619/#369): hard-float (AAPCS-VFP) f32 setup. Snapshot the
        // FPU capability + f32-param mask, seed each f32 param's home S-register,
        // and apply the phase-1 honest decline guards. Inert (all-false / empty)
        // for every function without an f32 param or f32 op — the integer path
        // is byte-identical.
        let fpu = self.fpu;
        let params_f32 = self.params_f32.clone();
        let mut vfp_used = [false; 16];
        let mut vfp_home = [false; 16];
        let mut f32_home: std::collections::HashMap<u32, VfpReg> = std::collections::HashMap::new();
        {
            let has_f32_param =
                (0..num_params).any(|i| params_f32.get(i as usize).copied().unwrap_or(false));
            let has_f32_op = wasm_ops.iter().any(is_scope_f32_op);
            let has_any_f32 = has_f32_param || has_f32_op;
            if has_any_f32 {
                // Honest reject on a non-FPU target (m0/m3/r5) — GI-FPU-001
                // capability contract. `fpu.is_none()` ⇒ no VFP.
                if fpu.is_none() {
                    return Err(synth_core::Error::synthesis(format!(
                        "GI-FPU-002: scalar f32 requires a hardware FPU target \
                         (cortex-m4f/m7/m7dp); '{}' has none — refusing to emit \
                         soft-float f32 (declining the function, #619/#369)",
                        self.target_name
                    )));
                }
                // #719: mixed f32 + integer params are now lowered — AAPCS-VFP's
                // independent core (R0..R3) and VFP (S0..S15) argument pools are
                // modelled by `aapcs_param_layout`/`compute_local_layout` skipping
                // f32 params in the core walk (so `(f32, i32)` maps i32→R0, not
                // R1) while the f32-home seed below assigns S(k) from the VFP
                // pool. No decline here anymore.
                //
                // #719 phase 2: f32 values LIVE ACROSS A CALL are now spilled and
                // reloaded around each `bl` (S0..S15 are caller-saved) via the
                // VFP call-spill area (`layout.vfp_spill_base`) — the exact analogue
                // of the #188 integer caller-saved preservation, emitted at the
                // Call/CallIndirect sites below. Two float-ABI-at-the-call cases
                // that this increment does NOT marshal still decline SOUNDLY through
                // pre-existing guards (never a miscompile):
                //  * passing an f32 as a call ARGUMENT — `pop_call_args`→`pop_operand`
                //    rejects a `Float` operand (an integer op never pops an f32).
                //  * a call that RETURNS f32/f64 — its result is pushed as an
                //    integer-tagged R0; any later f32 op `pop_float`s it → Err, and
                //    an f32/f64 function return is caught by the epilogue
                //    `ret_f32`/`ret_f64` soundness guard above.
            }
            // GI-FPU-002 phase 2 (#369): scalar f64 capability gates. The
            // lowered f64 subset needs DOUBLE-precision VFP (cortex-m7dp);
            // m4f/m7 are single-precision (VCVT.F64/VADD.F64 would be
            // UNDEFINED), and m0/m3/r5 have no FPU — honest-reject all three.
            // #1069: the i64<->f32 conversion members are in the f64-scope set
            // only because their m7dp INLINE lowering runs on f64 machinery —
            // their WASM types carry no f64. When the AEABI route is active
            // (single-precision + `--relocatable`) they lower through core-
            // register builtin calls instead, so they no longer force the
            // decline; every genuinely-f64 op still does.
            let has_f64_op = wasm_ops
                .iter()
                .any(|op| is_scope_f64_op(op) && !(aeabi_route && is_aeabi_i64_f32_routed_op(op)));
            if has_f64_op && !matches!(fpu, Some(FPUPrecision::Double)) {
                // Name the closable gap precisely: a single-precision decline
                // whose ONLY f64-scope ops are the routable conversions is one
                // `--relocatable` (+ AEABI runtime) away from compiling.
                let only_routable = fpu.is_some()
                    && !self.relocatable
                    && !wasm_ops
                        .iter()
                        .any(|op| is_scope_f64_op(op) && !is_aeabi_i64_f32_routed_op(op));
                return Err(synth_core::Error::synthesis(format!(
                    "GI-FPU-002 phase 2: scalar f64 requires a double-precision \
                     FPU target (cortex-m7dp); '{}' {} — refusing to emit f64 \
                     (declining the function, #369){}",
                    self.target_name,
                    if fpu.is_some() {
                        "has a single-precision FPU (f32 only)"
                    } else {
                        "has no FPU"
                    },
                    if only_routable {
                        ". Every f64-scope op here is an i64<->f32 conversion: \
                         compile with --relocatable to route them through the \
                         AEABI builtins (__aeabi_l2f/ul2f/f2lz/f2ulz, linked \
                         from the embedder's runtime — #1069)"
                    } else {
                        ""
                    }
                )));
            }
            // GI-FPU-002 phase 3 (#369): f64 PARAMS. On a DOUBLE-precision
            // target the param is homed in its AAPCS-VFP D-register (seeded
            // below via `vfp_param_layout`). On a SINGLE-precision target
            // (m4f/m7) the AAPCS-VFP caller still puts it in D0.., but every
            // f64 OP declines there — decline the function symmetrically
            // rather than home a value nothing can use (and the legacy
            // i64-pair reading of R0:R1 would be a silent wrong-argument
            // miscompile). Soft-float targets (no FPU) genuinely pass f64 in
            // core registers, so the i64-pair treatment is ABI-correct there
            // and stays.
            if matches!(fpu, Some(FPUPrecision::Single))
                && (0..num_params)
                    .any(|i| self.params_f64.get(i as usize).copied().unwrap_or(false))
            {
                return Err(synth_core::Error::synthesis(format!(
                    "GI-FPU-002 phase 3: an f64 parameter arrives in a VFP \
                     D-register under AAPCS-VFP, but '{}' has a \
                     single-precision FPU — no f64 op can consume it; \
                     declining loudly (#369)",
                    self.target_name
                )));
            }
        }
        // GI-FPU-002 phase 3 (#369): seed the float-param homes from the
        // AAPCS-VFP argument layout — f32 params in S-registers, f64 params
        // (double-precision targets only; `params_f64_vfp` is empty otherwise)
        // in D-registers, with back-fill allocation: `(f32, f64, f32)` homes
        // S0, D1(=S2:S3), S1. For an f32-only signature this degenerates to
        // the sequential `S0, S1, …` seeding it replaces (byte-identical).
        let mut f64_home: std::collections::HashMap<u32, VfpReg> = std::collections::HashMap::new();
        // #1069 (RQ-60-VFPPRESSURE increment 2): FRAME-homed float locals —
        // local index -> permanent [SP,#slot] byte offset. Populated ONLY
        // under the LAST-resort `vfp_frame_home_locals` lever (set by the
        // backend after the plain #881 rung also exhausted), when a fresh
        // local home would pin a register above the S7/D3 cap (or the file
        // is already exhausted): the local then lives in the frame from its
        // first def, `local.set` stores, `local.get` loads. Empty in every
        // default AND every plain-rung compile, so both are byte-identical
        // by construction.
        let mut f32_frame: std::collections::HashMap<u32, i32> = std::collections::HashMap::new();
        let mut f64_frame: std::collections::HashMap<u32, i32> = std::collections::HashMap::new();
        if fpu.is_some() {
            let seeds = vfp_param_layout(num_params, &params_f32, &params_f64_vfp)
                .map_err(|e| synth_core::Error::synthesis(format!("GI-FPU-002 phase 3: {e}")))?;
            for (i, home) in seeds {
                if let Some(d) = vfp_d_index(home) {
                    vfp_used[2 * d] = true;
                    vfp_used[2 * d + 1] = true;
                    vfp_home[2 * d] = true;
                    vfp_home[2 * d + 1] = true;
                    f64_home.insert(i, home);
                } else if let Some(s) = vfp_s_index(home) {
                    vfp_used[s] = true;
                    vfp_home[s] = true;
                    f32_home.insert(i, home);
                }
            }
        }

        // #881: straight-line floor for the VFP spill rung — the operand-stack
        // depth at the last control-flow boundary. Entries below it were pushed
        // before a branch/label and are never spill victims (a conditionally-
        // executed spill store would not dominate its reload). Only consulted
        // when `vfp_spill_on_exhaustion` is set.
        let mut vfp_cf_floor: usize = 0;
        for (idx, op) in wasm_ops.iter().enumerate() {
            // Param registers still live at this op — reserved from temp/pair/
            // reload allocation so a constant/result/reload never clobbers a live
            // param (#193).
            let mut live_params = live_param_regs(idx);
            // #313: while inside the else-arm of one or more if-blocks, the
            // then-arm result registers of each enclosing if-block must be
            // protected from the allocators exactly as they were when they sat
            // on the vstack in the buggy code (this is what makes the else-arm
            // allocate byte-identically). Reserve them — and the conventional
            // hi register of any i64 result — for the duration of the else-arm.
            for results in &if_then_results {
                for v in results {
                    if let StackVal::Reg { reg, is_i64 } = v {
                        live_params.push(*reg);
                        if *is_i64 && let Ok(hi) = i64_pair_hi(*reg) {
                            live_params.push(hi);
                        }
                    }
                }
            }
            // #509: the designated result register of every open, branched-to
            // value block is reserved for the block's extent — a temp/const/
            // reload allocated into it would be clobbered by the edge moves
            // into the join. Blocks never branched to have no `result_reg`, so
            // existing code allocates byte-identically.
            for bl in &block_labels {
                if let Some(r) = bl.result_reg {
                    live_params.push(r);
                }
            }
            // #881 (VCR-RA-004): the VFP pressure guard — rung-only (inert in
            // every default compile). Control ops reset the straight-line
            // floor (reloading a spilled top first, so End/Else result
            // handling always sees a register-resident value); float-demand
            // ops get their spilled operands reloaded and conservative
            // register headroom freed by spilling the deepest segment-local
            // VFP values (farthest next use under LIFO stack discipline).
            if spill.vfp_spill_on_exhaustion && fpu.is_some() {
                // Keep the floor meaningful as the stack shrinks.
                vfp_cf_floor = vfp_cf_floor.min(stack.len());
                match op {
                    WasmOp::Block
                    | WasmOp::Loop
                    | WasmOp::If
                    | WasmOp::Else
                    | WasmOp::End
                    | WasmOp::Br(_)
                    | WasmOp::BrIf(_)
                    | WasmOp::BrTable { .. } => {
                        if !stack.is_empty() {
                            vfp_reload_spilled(
                                stack.len() - 1,
                                &mut stack,
                                vfp_cf_floor,
                                1,
                                &mut vfp_used,
                                &vfp_home,
                                &mut spill,
                                &mut instructions,
                                idx,
                            )?;
                        }
                        vfp_cf_floor = stack.len();
                    }
                    _ => {
                        // #1069: a `local.get` of a FRAME-homed float local
                        // loads into a fresh S-reg / aligned D-pair — demand
                        // headroom for it. `vfp_op_demand` cannot know
                        // residence; both maps are empty unless the rung
                        // frame-homed a local, so this override is inert for
                        // every pre-#1069 rung compile.
                        let frame_local_demand = if let WasmOp::LocalGet(i) = op {
                            if f32_frame.contains_key(i) {
                                Some((0, 1, 0))
                            } else if f64_frame.contains_key(i) {
                                Some((0, 0, 1))
                            } else {
                                None
                            }
                        } else {
                            None
                        };
                        let (window, need_s, need_pairs) =
                            frame_local_demand.unwrap_or_else(|| vfp_op_demand(op));
                        if window + need_s + need_pairs > 0 {
                            let lo = stack.len().saturating_sub(window);
                            for pos in lo..stack.len() {
                                vfp_reload_spilled(
                                    pos,
                                    &mut stack,
                                    vfp_cf_floor,
                                    window,
                                    &mut vfp_used,
                                    &vfp_home,
                                    &mut spill,
                                    &mut instructions,
                                    idx,
                                )?;
                            }
                            vfp_ensure_headroom(
                                need_s,
                                need_pairs,
                                &mut stack,
                                vfp_cf_floor,
                                window,
                                &mut vfp_used,
                                &vfp_home,
                                &mut spill,
                                &mut instructions,
                                idx,
                            )?;
                        }
                    }
                }
            }
            // #1069 (RQ-60-VFPPRESSURE increment 1): intercept the AEABI-routed
            // i64<->f32 conversions BEFORE `try_lower_f32` — its arms for these
            // ops run on DOUBLE-precision machinery (D-temps, VCVT.F64), which
            // the preamble gate only lets through here when the route is
            // active. Single-precision + `--relocatable` only; m7dp keeps the
            // #869 inline lowering byte-identically.
            if aeabi_route && is_aeabi_i64_f32_routed_op(op) {
                self.lower_aeabi_i64_f32(
                    op,
                    idx,
                    &mut stack,
                    &mut next_temp,
                    &mut instructions,
                    &mut spill,
                    &mut vfp_used,
                    &vfp_home,
                    &layout,
                    &local_to_reg,
                    &live_params,
                    &mut cf,
                )?;
                continue;
            }
            // GI-FPU-002 (#619/#369): intercept in-scope scalar f32 ops (and f32
            // param local.get) before the integer match. Gated on FPU presence;
            // integer modules never construct an f32 stack entry, so this is
            // inert for them (byte-identical). `Ok(false)` ⇒ not an f32 op.
            if fpu.is_some()
                && try_lower_f32(
                    op,
                    idx,
                    &params_f32,
                    &mut f32_home,
                    &mut f32_frame,
                    &mut vfp_used,
                    &mut vfp_home,
                    &mut stack,
                    &mut next_temp,
                    &mut spill,
                    &mut instructions,
                    &live_params,
                )?
            {
                continue;
            }
            // GI-FPU-002 phase 2 (#369): intercept in-scope scalar f64 ops
            // BEFORE the integer match — the main match's `_ =>` arm falls
            // back to the register-blind `select_default`, which would
            // miscompile them. Gated on double-precision VFP (the preamble
            // honest-rejects any f64 op on m4f/m7/m3, so this arm is
            // unreachable there); F64Load/F64Store fall through to their
            // dedicated main-match arms below.
            if matches!(fpu, Some(FPUPrecision::Double))
                && try_lower_f64(
                    op,
                    idx,
                    &params_f64_vfp,
                    &mut f64_home,
                    &mut f64_frame,
                    &mut vfp_used,
                    &mut vfp_home,
                    &mut stack,
                    &mut next_temp,
                    &mut spill,
                    &mut instructions,
                    &live_params,
                )?
            {
                continue;
            }
            match op {
                LocalGet(local_idx) => {
                    // Get the register for this local. Cases:
                    //  1. Incoming stack-passed param (#359/#503) — load from the
                    //     caller's frame (i32 single Ldr; i64/f64 pair via I64Ldr).
                    //  2. Param in register — use the cached mapping.
                    //  3. Spilled i64 local — load both halves via I64Ldr.
                    //  4. Spilled i32 local — single Ldr.
                    let (reg, val_is_i64) =
                        if let Some(&(off, is_wide)) = layout.incoming_params.get(local_idx) {
                            // #359/#503: read the incoming stack-passed param into
                            // fresh temp(s) pushed on the vstack — NOT register-
                            // homed. A wide param loads its 8-byte NSAA slot into
                            // a consecutive pair (#503-i64).
                            if is_wide {
                                let (dst_lo, dst_hi) = alloc_consecutive_pair(
                                    &mut next_temp,
                                    &mut stack,
                                    &mut instructions,
                                    &mut spill,
                                    &[],
                                    &live_params,
                                    idx,
                                )?;
                                instructions.push(ArmInstruction {
                                    op: ArmOp::I64Ldr {
                                        rdlo: dst_lo,
                                        rdhi: dst_hi,
                                        addr: MemAddr::imm(Reg::SP, off),
                                    },
                                    source_line: Some(idx),
                                });
                                (dst_lo, true)
                            } else {
                                let dst = alloc_temp_or_spill(
                                    &mut next_temp,
                                    &mut stack,
                                    &mut instructions,
                                    &mut spill,
                                    &live_params,
                                    idx,
                                )?;
                                instructions.push(ArmInstruction {
                                    op: ArmOp::Ldr {
                                        rd: dst,
                                        addr: MemAddr::imm(Reg::SP, off),
                                    },
                                    source_line: Some(idx),
                                });
                                (dst, false)
                            }
                        } else if let Some(&(off, is_i64)) = layout.param_slots.get(local_idx) {
                            // #204/#193: frame-backed param — reload from its slot.
                            if is_i64 {
                                let (dst_lo, dst_hi) = alloc_consecutive_pair(
                                    &mut next_temp,
                                    &mut stack,
                                    &mut instructions,
                                    &mut spill,
                                    &[],
                                    &live_params,
                                    idx,
                                )?;
                                instructions.push(ArmInstruction {
                                    op: ArmOp::I64Ldr {
                                        rdlo: dst_lo,
                                        rdhi: dst_hi,
                                        addr: MemAddr::imm(Reg::SP, off),
                                    },
                                    source_line: Some(idx),
                                });
                                (dst_lo, true)
                            } else {
                                let dst = alloc_temp_or_spill(
                                    &mut next_temp,
                                    &mut stack,
                                    &mut instructions,
                                    &mut spill,
                                    &live_params,
                                    idx,
                                )?;
                                instructions.push(ArmInstruction {
                                    op: ArmOp::Ldr {
                                        rd: dst,
                                        addr: MemAddr::imm(Reg::SP, off),
                                    },
                                    source_line: Some(idx),
                                });
                                (dst, false)
                            }
                        } else if let Some(&r) = local_to_reg.get(local_idx) {
                            (r, i64_locals.contains(local_idx))
                        } else if let Some(&(off, true)) = layout.locals.get(local_idx) {
                            // i64 local — load both 32-bit halves into a consecutive
                            // register pair via the I64Ldr pseudo-op. Convention
                            // matches I64Const: push only dst_lo on the stack;
                            // dst_hi is recovered later via i64_pair_hi(lo).
                            // The pair MUST be consecutive in ALLOCATABLE_REGS
                            // — i64_pair_hi assumes that. Two separate calls to
                            // alloc_temp_safe can return non-consecutive registers
                            // when something in between is live, breaking the
                            // pair convention.
                            let (dst_lo, dst_hi) = alloc_consecutive_pair(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &[],
                                &live_params,
                                idx,
                            )?;
                            instructions.push(ArmInstruction {
                                op: ArmOp::I64Ldr {
                                    rdlo: dst_lo,
                                    rdhi: dst_hi,
                                    addr: MemAddr::imm(Reg::SP, off),
                                },
                                source_line: Some(idx),
                            });
                            (dst_lo, true)
                        } else if let Some(&(off, false)) = layout.locals.get(local_idx) {
                            // i32 local: single 4-byte load from the locals frame.
                            let dst = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &live_params,
                                idx,
                            )?;
                            instructions.push(ArmInstruction {
                                op: ArmOp::Ldr {
                                    rd: dst,
                                    addr: MemAddr::imm(Reg::SP, off),
                                },
                                source_line: Some(idx),
                            });
                            (dst, false)
                        } else {
                            // #378 honesty: a local absent from the computed frame
                            // layout is either malformed wasm (out-of-range index,
                            // which validation should have rejected) or a
                            // layout-computation bug. Either way, FAIL HONESTLY —
                            // a loud `Err` loud-skips the function — rather than
                            // GUESS a frame offset `(local_idx-4)*4` and silently
                            // miscompile. Same never-guess contract as GI-FPU-001
                            // (decoder) and #180/#185 (encoder Ok-or-Err).
                            return Err(synth_core::Error::synthesis(format!(
                                "local.get {local_idx} (op {idx}) is absent from the \
                                 computed frame layout — refusing to guess a stack \
                                 offset (would silently miscompile)"
                            )));
                        };
                    stack.push(StackVal::Reg {
                        reg,
                        is_i64: val_is_i64,
                    });
                }

                I32Const(val) => {
                    let dst = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let uval = *val as u32;
                    // #237: under the native-pointer ABI, when a stack-pointer
                    // global establishes a real static-data base, a const at/above
                    // it is a wasm pointer (e.g. a `&static_spinlock` argument),
                    // not a scalar — emit it as `__synth_wasm_data + uval` so it
                    // resolves at link time independent of any runtime base. This
                    // is gated on `sp_global`: without one the base is 0 and every
                    // const (including stored *values*) would look like an address,
                    // which is unsound — those modules use the positional
                    // load/store promotion only.
                    if self.sp_global.is_some()
                        && let Some(addend) = self.static_data_addend(uval)
                    {
                        Self::emit_wasm_data_addr(&mut instructions, dst, addend, idx);
                        cf.add_instruction();
                        stack.push(StackVal::i32(dst));
                        continue;
                    }
                    let inverted = !uval;
                    if uval <= 0xFFFF {
                        // 0..65535: MOVW handles the full 16-bit range
                        instructions.push(ArmInstruction {
                            op: ArmOp::Movw {
                                rd: dst,
                                imm16: uval as u16,
                            },
                            source_line: Some(idx),
                        });
                    } else if inverted <= 0xFFFF {
                        // Bit-inverted pattern: MOVW inverted + MVN
                        instructions.push(ArmInstruction {
                            op: ArmOp::Movw {
                                rd: dst,
                                imm16: inverted as u16,
                            },
                            source_line: Some(idx),
                        });
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mvn {
                                rd: dst,
                                op2: Operand2::Reg(dst),
                            },
                            source_line: Some(idx),
                        });
                    } else {
                        // Full 32-bit: MOVW low16 + MOVT high16
                        instructions.push(ArmInstruction {
                            op: ArmOp::Movw {
                                rd: dst,
                                imm16: (uval & 0xFFFF) as u16,
                            },
                            source_line: Some(idx),
                        });
                        instructions.push(ArmInstruction {
                            op: ArmOp::Movt {
                                rd: dst,
                                imm16: ((uval >> 16) & 0xFFFF) as u16,
                            },
                            source_line: Some(idx),
                        });
                    }
                    stack.push(StackVal::i32(dst));
                }

                I32Add => {
                    // Immediate folding (#250 pattern): const operand 0..=0xFFF
                    // (the ADDW range, #253) whose `movw` is at the tail →
                    // `add rd, a, #C`, drop the materialization.
                    let fold_imm = foldable_addsub_imm(wasm_ops, idx).filter(|_| {
                        matches!(
                            instructions.last().map(|i| (&i.op, i.source_line)),
                            Some((ArmOp::Movw { .. }, Some(sl))) if sl == idx - 1
                        )
                    });
                    let (a, op2) = if let Some(c) = fold_imm {
                        let _b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        Self::drop_prev_const_materialization(&mut instructions, idx - 1);
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Imm(c))
                    } else {
                        let b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Reg(b))
                    };
                    // Result goes in r0 for return value (or temp if not last op)
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    // Both emission paths are Rocq-proved rules (increment 5,
                    // RQ-58-SELDSL): the folded form `rule_i32_add_imm`, the
                    // reg-reg form `rule_i32_add` — the hand-written
                    // ArmOp::Add construction is deleted.
                    let rule_ops = match op2 {
                        Operand2::Imm(c) => crate::sel_dsl::generated::rule_i32_add_imm(dst, a, c),
                        Operand2::Reg(b) => crate::sel_dsl::generated::rule_i32_add(dst, a, b),
                        Operand2::RegShift { .. } => {
                            unreachable!("i32.add operand2 is Imm or Reg by construction")
                        }
                    };
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                    }
                    stack.push(StackVal::i32(dst));
                }

                I32Sub => {
                    // Immediate folding: `i32.sub` is `a - b`; when b is a const
                    // 0..=0xFFF (SUBW range, #253) with its `movw` at the tail,
                    // fold to `sub rd, a, #C` and drop the materialization.
                    let fold_imm = foldable_addsub_imm(wasm_ops, idx).filter(|_| {
                        matches!(
                            instructions.last().map(|i| (&i.op, i.source_line)),
                            Some((ArmOp::Movw { .. }, Some(sl))) if sl == idx - 1
                        )
                    });
                    let (a, op2) = if let Some(c) = fold_imm {
                        let _b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        Self::drop_prev_const_materialization(&mut instructions, idx - 1);
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Imm(c))
                    } else {
                        let b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Reg(b))
                    };
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    // Rocq-proved rules on both paths (increment 5,
                    // RQ-58-SELDSL): rule_i32_sub_imm / rule_i32_sub.
                    let rule_ops = match op2 {
                        Operand2::Imm(c) => crate::sel_dsl::generated::rule_i32_sub_imm(dst, a, c),
                        Operand2::Reg(b) => crate::sel_dsl::generated::rule_i32_sub(dst, a, b),
                        Operand2::RegShift { .. } => {
                            unreachable!("i32.sub operand2 is Imm or Reg by construction")
                        }
                    };
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                    }
                    stack.push(StackVal::i32(dst));
                }

                I32Mul => {
                    let b = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    // Rocq-proved rule as the only path (increment 5,
                    // RQ-58-SELDSL): the hand-written ArmOp::Mul construction
                    // is deleted.
                    for rule_op in crate::sel_dsl::generated::rule_i32_mul(dst, a, b) {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                    }
                    stack.push(StackVal::i32(dst));
                }

                I32And => {
                    // Immediate folding: when the second operand is a small const
                    // (`i32.const C`, 0..=0xFF) whose `movw` is cleanly at the tail
                    // (not spilled), fold it as `and rd, a, #C` and drop the
                    // materialization — eliminating the redundant const load
                    // (#209/#248). Bounded to 0..=0xFF by the encoder (#249).
                    let fold_imm = foldable_bitwise_imm(wasm_ops, idx).filter(|_| {
                        matches!(
                            instructions.last().map(|i| (&i.op, i.source_line)),
                            Some((ArmOp::Movw { .. }, Some(sl))) if sl == idx - 1
                        )
                    });
                    let (a, op2) = if let Some(c) = fold_imm {
                        let _b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        Self::drop_prev_const_materialization(&mut instructions, idx - 1);
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Imm(c))
                    } else {
                        let b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Reg(b))
                    };
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    // Rocq-proved rules on both paths (increment 5,
                    // RQ-58-SELDSL): rule_i32_and_imm / rule_i32_and.
                    let rule_ops = match op2 {
                        Operand2::Imm(c) => crate::sel_dsl::generated::rule_i32_and_imm(dst, a, c),
                        Operand2::Reg(b) => crate::sel_dsl::generated::rule_i32_and(dst, a, b),
                        Operand2::RegShift { .. } => {
                            unreachable!("i32.and operand2 is Imm or Reg by construction")
                        }
                    };
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                    }
                    stack.push(StackVal::i32(dst));
                }

                I32Or => {
                    // Immediate folding (same shape as I32And, #250): const
                    // operand 0..=0xFF whose `movw` is at the tail → `orr rd,a,#C`,
                    // drop the materialization. Encoder ORR-imm hardened in #251.
                    let fold_imm = foldable_bitwise_imm(wasm_ops, idx).filter(|_| {
                        matches!(
                            instructions.last().map(|i| (&i.op, i.source_line)),
                            Some((ArmOp::Movw { .. }, Some(sl))) if sl == idx - 1
                        )
                    });
                    let (a, op2) = if let Some(c) = fold_imm {
                        let _b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        Self::drop_prev_const_materialization(&mut instructions, idx - 1);
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Imm(c))
                    } else {
                        let b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Reg(b))
                    };
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    // Rocq-proved rules on both paths (increment 5,
                    // RQ-58-SELDSL): rule_i32_or_imm / rule_i32_or.
                    let rule_ops = match op2 {
                        Operand2::Imm(c) => crate::sel_dsl::generated::rule_i32_or_imm(dst, a, c),
                        Operand2::Reg(b) => crate::sel_dsl::generated::rule_i32_or(dst, a, b),
                        Operand2::RegShift { .. } => {
                            unreachable!("i32.or operand2 is Imm or Reg by construction")
                        }
                    };
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                    }
                    stack.push(StackVal::i32(dst));
                }

                I32Xor => {
                    // Immediate folding (same shape as I32And, #250): const
                    // operand 0..=0xFF whose `movw` is at the tail → `eor rd,a,#C`,
                    // drop the materialization. Encoder EOR-imm hardened in #251.
                    let fold_imm = foldable_bitwise_imm(wasm_ops, idx).filter(|_| {
                        matches!(
                            instructions.last().map(|i| (&i.op, i.source_line)),
                            Some((ArmOp::Movw { .. }, Some(sl))) if sl == idx - 1
                        )
                    });
                    let (a, op2) = if let Some(c) = fold_imm {
                        let _b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        Self::drop_prev_const_materialization(&mut instructions, idx - 1);
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Imm(c))
                    } else {
                        let b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Reg(b))
                    };
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    // Rocq-proved rules on both paths (increment 5,
                    // RQ-58-SELDSL): rule_i32_xor_imm / rule_i32_xor.
                    let rule_ops = match op2 {
                        Operand2::Imm(c) => crate::sel_dsl::generated::rule_i32_xor_imm(dst, a, c),
                        Operand2::Reg(b) => crate::sel_dsl::generated::rule_i32_xor(dst, a, b),
                        Operand2::RegShift { .. } => {
                            unreachable!("i32.xor operand2 is Imm or Reg by construction")
                        }
                    };
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                    }
                    stack.push(StackVal::i32(dst));
                }

                // Division operations with trap checks for divide-by-zero
                I32DivU => {
                    // #209 Opt 1: a statically-known nonzero divisor lets us
                    // strength-reduce the UDIV and drop the dead div-by-zero
                    // trap guard. Snapshot before popping (pop_operand mutates).
                    let cdiv = const_divisor(wasm_ops, idx);
                    let divisor = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?; // b (divisor)
                    let dividend = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?; // a (dividend)
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };

                    if cdiv == Some(1) {
                        // x / 1 == x (no trap possible). Identity move.
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mov {
                                rd: dst,
                                op2: Operand2::Reg(dividend),
                            },
                            source_line: Some(idx),
                        });
                    } else if let Some(k) = cdiv.and_then(pow2_shift_u) {
                        // x / 2^k == x >> k (unsigned). No guard, no UDIV.
                        instructions.push(ArmInstruction {
                            op: ArmOp::Lsr {
                                rd: dst,
                                rn: dividend,
                                shift: k,
                            },
                            source_line: Some(idx),
                        });
                    } else if let Some(d) = cdiv
                        .map(|c| c as u32)
                        .filter(|&u| u >= 3 && !u.is_power_of_two())
                    {
                        // #209 Opt 1b: non-power-of-two constant divisor →
                        // reciprocal-multiply (Granlund–Montgomery magic number).
                        // No UDIV, no trap guard. Computes the high word of
                        // `dividend * m` via UMULL, then an `a`-selected shift.
                        let (m, s, a) = magicu(d);
                        let mut reserved: Vec<Reg> = live_params.clone();
                        reserved.push(dividend);
                        reserved.push(dst);

                        // Scratch for the reciprocal-multiply: the magic
                        // constant + UMULL's outputs. The a==false path reuses
                        // `dst` as the throwaway low word (2 temps); a==true
                        // keeps `dividend` live past the UMULL (3 temps).
                        // Exhaustion here is recovered by the #320 spill retry
                        // — the historical v0.11.20 UDIV cost-gate is deleted
                        // (VCR-VER-001; it was already dead on the frozen
                        // suite).
                        // VCR-VER-001 (#242): the v0.11.20 cost-gate is GONE.
                        // The #320 spill-on-exhaustion retry recovers the
                        // pressure case the UDIV fallback guarded, and the
                        // fallback was already dead on the entire frozen suite
                        // (reverting it is byte-identical) — the first greedy
                        // patch deleted under the VCR program's exit criterion.
                        let rmag = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &reserved,
                            idx,
                        )?;
                        reserved.push(rmag);
                        let (rlo, rhi) = if a {
                            let rlo = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &reserved,
                                idx,
                            )?;
                            reserved.push(rlo);
                            let rhi = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &reserved,
                                idx,
                            )?;
                            (rlo, rhi)
                        } else {
                            // a==false: `dst` doubles as UMULL's RdLo.
                            let rhi = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &reserved,
                                idx,
                            )?;
                            (dst, rhi)
                        };
                        {
                            // #209 cleanup: the reciprocal-multiply reads the magic
                            // constant, never the divisor — so the divisor's eager
                            // materialization (the `i32.const` at idx-1, the only op
                            // tagged there) is dead on this path. Drop it. #581:
                            // materialization ops only — a spill store emitted while
                            // allocating the divisor's temp shares the tag but must
                            // survive (its slot is recorded as populated).
                            if idx >= 1 {
                                instructions.retain(|i| {
                                    i.source_line != Some(idx - 1)
                                        || !Self::is_const_materialization(&i.op)
                                });
                            }
                            // Materialize the magic constant m into rmag.
                            instructions.push(ArmInstruction {
                                op: ArmOp::Movw {
                                    rd: rmag,
                                    imm16: (m & 0xFFFF) as u16,
                                },
                                source_line: Some(idx),
                            });
                            instructions.push(ArmInstruction {
                                op: ArmOp::Movt {
                                    rd: rmag,
                                    imm16: ((m >> 16) & 0xFFFF) as u16,
                                },
                                source_line: Some(idx),
                            });
                            // UMULL rlo, rhi, dividend, rmag → rhi = umulhi(m, n)
                            instructions.push(ArmInstruction {
                                op: ArmOp::Umull {
                                    rdlo: rlo,
                                    rdhi: rhi,
                                    rn: dividend,
                                    rm: rmag,
                                },
                                source_line: Some(idx),
                            });
                            if a {
                                // q = (((n - hi) >> 1) + hi) >> (s-1); rlo as t.
                                instructions.push(ArmInstruction {
                                    op: ArmOp::Sub {
                                        rd: rlo,
                                        rn: dividend,
                                        op2: Operand2::Reg(rhi),
                                    },
                                    source_line: Some(idx),
                                });
                                instructions.push(ArmInstruction {
                                    op: ArmOp::Lsr {
                                        rd: rlo,
                                        rn: rlo,
                                        shift: 1,
                                    },
                                    source_line: Some(idx),
                                });
                                instructions.push(ArmInstruction {
                                    op: ArmOp::Add {
                                        rd: rlo,
                                        rn: rlo,
                                        op2: Operand2::Reg(rhi),
                                    },
                                    source_line: Some(idx),
                                });
                                // s >= 1 when a is set; s == 1 → final shift is 0.
                                if s == 1 {
                                    instructions.push(ArmInstruction {
                                        op: ArmOp::Mov {
                                            rd: dst,
                                            op2: Operand2::Reg(rlo),
                                        },
                                        source_line: Some(idx),
                                    });
                                } else {
                                    instructions.push(ArmInstruction {
                                        op: ArmOp::Lsr {
                                            rd: dst,
                                            rn: rlo,
                                            shift: s - 1,
                                        },
                                        source_line: Some(idx),
                                    });
                                }
                            } else if s == 0 {
                                // q = hi (no shift). LSR #0 is invalid, so MOV.
                                instructions.push(ArmInstruction {
                                    op: ArmOp::Mov {
                                        rd: dst,
                                        op2: Operand2::Reg(rhi),
                                    },
                                    source_line: Some(idx),
                                });
                            } else {
                                // q = hi >> s
                                instructions.push(ArmInstruction {
                                    op: ArmOp::Lsr {
                                        rd: dst,
                                        rn: rhi,
                                        shift: s,
                                    },
                                    source_line: Some(idx),
                                });
                            }
                        }
                    } else {
                        // A nonzero constant divisor can never trap; only emit
                        // the div-by-zero guard when the divisor is unknown or 0.
                        // #494 phase 2b: a certificate-discharged divisor-nonzero
                        // fact (UNSAT(P ∧ divisor == 0), proven by the fact-spec
                        // pass before selection) elides it too.
                        let needs_guard =
                            cdiv.is_none_or(|c| c == 0) && !self.fact_div_zero_elide.contains(&idx);
                        if needs_guard {
                            // CMP divisor, #0
                            instructions.push(ArmInstruction {
                                op: ArmOp::Cmp {
                                    rn: divisor,
                                    op2: Operand2::Imm(0),
                                },
                                source_line: Some(idx),
                            });
                            // BNE.N +0 (skip UDF if divisor != 0): offset=0 means
                            // skip to PC+4, which skips the 2-byte UDF.
                            instructions.push(ArmInstruction {
                                op: ArmOp::BCondOffset {
                                    cond: Condition::NE,
                                    offset: 0,
                                },
                                source_line: Some(idx),
                            });
                            // UDF #0 (triggers trap on divide by zero)
                            instructions.push(ArmInstruction {
                                op: ArmOp::Udf { imm: 0 },
                                source_line: Some(idx),
                            });
                        }
                        // UDIV dst, dividend, divisor
                        instructions.push(ArmInstruction {
                            op: ArmOp::Udiv {
                                rd: dst,
                                rn: dividend,
                                rm: divisor,
                            },
                            source_line: Some(idx),
                        });
                    }
                    stack.push(StackVal::i32(dst));
                }

                I32DivS => {
                    // #209 Opt 1: a known divisor lets us drop the dead trap
                    // guards — div-by-zero when C != 0, and the INT_MIN/-1
                    // overflow guard when C != -1 (overflow only at divisor -1).
                    let cdiv = const_divisor(wasm_ops, idx);
                    let divisor = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dividend = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };

                    if cdiv == Some(1) {
                        // x / 1 == x (INT_MIN/1 = INT_MIN, no overflow). Identity.
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mov {
                                rd: dst,
                                op2: Operand2::Reg(dividend),
                            },
                            source_line: Some(idx),
                        });
                        stack.push(StackVal::i32(dst));
                    } else {
                        // Trap check 1: divide by zero (dead for a nonzero const,
                        // or under a #494 certificate-discharged divisor-nonzero
                        // fact — UNSAT(P ∧ divisor == 0)).
                        let needs_dz_guard =
                            cdiv.is_none_or(|c| c == 0) && !self.fact_div_zero_elide.contains(&idx);
                        if needs_dz_guard {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Cmp {
                                    rn: divisor,
                                    op2: Operand2::Imm(0),
                                },
                                source_line: Some(idx),
                            });
                            instructions.push(ArmInstruction {
                                op: ArmOp::BCondOffset {
                                    cond: Condition::NE,
                                    offset: 0,
                                },
                                source_line: Some(idx),
                            });
                            instructions.push(ArmInstruction {
                                op: ArmOp::Udf { imm: 0 },
                                source_line: Some(idx),
                            });
                        }

                        // Trap check 2: signed overflow (INT_MIN / -1). Dead
                        // unless the divisor could be -1. #494 phase 2b: elidable
                        // ONLY under its OWN discharged obligation
                        // (UNSAT(P ∧ dividend == INT_MIN ∧ divisor == -1)) — a
                        // divisor-nonzero fact alone never elides it (#633/#634:
                        // nonzero does not exclude -1).
                        let needs_ovf_guard =
                            cdiv.is_none_or(|c| c == -1) && !self.fact_div_ovf_elide.contains(&idx);
                        if needs_ovf_guard {
                            // We need a temp register for INT_MIN (0x80000000)
                            let tmp = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &live_params,
                                idx,
                            )?;

                            // Load INT_MIN into tmp: MOVW tmp, #0; MOVT tmp, #0x8000
                            instructions.push(ArmInstruction {
                                op: ArmOp::Movw { rd: tmp, imm16: 0 },
                                source_line: Some(idx),
                            });
                            instructions.push(ArmInstruction {
                                op: ArmOp::Movt {
                                    rd: tmp,
                                    imm16: 0x8000,
                                },
                                source_line: Some(idx),
                            });
                            // CMP dividend, tmp (check if dividend == INT_MIN)
                            instructions.push(ArmInstruction {
                                op: ArmOp::Cmp {
                                    rn: dividend,
                                    op2: Operand2::Reg(tmp),
                                },
                                source_line: Some(idx),
                            });
                            // BNE.N +3 (skip overflow check if dividend != INT_MIN)
                            // Skip 8 bytes: CMN.W(4) + BNE(2) + UDF(2)
                            // Branch target = PC + (imm8 << 1) = B+4 + 6 = B+10 (SDIV)
                            instructions.push(ArmInstruction {
                                op: ArmOp::BCondOffset {
                                    cond: Condition::NE,
                                    offset: 3,
                                },
                                source_line: Some(idx),
                            });
                            // CMN divisor, #1 (divisor == -1: -1 + 1 = 0 sets Z)
                            // CMN.W is 4 bytes
                            instructions.push(ArmInstruction {
                                op: ArmOp::Cmn {
                                    rn: divisor,
                                    op2: Operand2::Imm(1),
                                },
                                source_line: Some(idx),
                            });
                            // BNE.N +0 (skip UDF if divisor != -1)
                            instructions.push(ArmInstruction {
                                op: ArmOp::BCondOffset {
                                    cond: Condition::NE,
                                    offset: 0,
                                },
                                source_line: Some(idx),
                            });
                            // UDF #1 (triggers trap on overflow)
                            instructions.push(ArmInstruction {
                                op: ArmOp::Udf { imm: 1 },
                                source_line: Some(idx),
                            });
                        }

                        // SDIV dst, dividend, divisor (safe to divide now)
                        instructions.push(ArmInstruction {
                            op: ArmOp::Sdiv {
                                rd: dst,
                                rn: dividend,
                                rm: divisor,
                            },
                            source_line: Some(idx),
                        });
                        stack.push(StackVal::i32(dst));
                    }
                }

                I32RemU => {
                    // #209 Opt 1: drop the dead div-by-zero guard for a nonzero
                    // constant divisor; fold `x % 1` to 0.
                    let cdiv = const_divisor(wasm_ops, idx);
                    let divisor = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dividend = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };

                    if cdiv == Some(1) {
                        // x % 1 == 0
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mov {
                                rd: dst,
                                op2: Operand2::Imm(0),
                            },
                            source_line: Some(idx),
                        });
                        stack.push(StackVal::i32(dst));
                    } else {
                        // Trap check: divide by zero (dead for a nonzero const,
                        // or under a #494 certificate-discharged divisor-nonzero
                        // fact).
                        let needs_guard =
                            cdiv.is_none_or(|c| c == 0) && !self.fact_div_zero_elide.contains(&idx);
                        if needs_guard {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Cmp {
                                    rn: divisor,
                                    op2: Operand2::Imm(0),
                                },
                                source_line: Some(idx),
                            });
                            instructions.push(ArmInstruction {
                                op: ArmOp::BCondOffset {
                                    cond: Condition::NE,
                                    offset: 0,
                                },
                                source_line: Some(idx),
                            });
                            instructions.push(ArmInstruction {
                                op: ArmOp::Udf { imm: 0 },
                                source_line: Some(idx),
                            });
                        }

                        // Remainder: dst = dividend - (dividend / divisor) * divisor
                        // quotient = UDIV tmp, dividend, divisor
                        let tmp = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::Udiv {
                                rd: tmp,
                                rn: dividend,
                                rm: divisor,
                            },
                            source_line: Some(idx),
                        });
                        // MLS dst, tmp, divisor, dividend (dst = dividend - tmp*divisor)
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mls {
                                rd: dst,
                                rn: tmp,
                                rm: divisor,
                                ra: dividend,
                            },
                            source_line: Some(idx),
                        });
                        stack.push(StackVal::i32(dst));
                    }
                }

                I32RemS => {
                    // #209 Opt 1: drop the dead div-by-zero guard for a nonzero
                    // constant divisor; fold `x % 1` to 0. (`x % -1 == 0` is left
                    // to SDIV+MLS, which already yields 0 for all dividends.)
                    let cdiv = const_divisor(wasm_ops, idx);
                    let divisor = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dividend = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };

                    if cdiv == Some(1) {
                        // x % 1 == 0
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mov {
                                rd: dst,
                                op2: Operand2::Imm(0),
                            },
                            source_line: Some(idx),
                        });
                        stack.push(StackVal::i32(dst));
                    } else {
                        // Trap check: divide by zero (rem_s doesn't trap on
                        // INT_MIN % -1). Dead for a nonzero constant divisor, or
                        // under a #494 certificate-discharged divisor-nonzero fact.
                        let needs_guard =
                            cdiv.is_none_or(|c| c == 0) && !self.fact_div_zero_elide.contains(&idx);
                        if needs_guard {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Cmp {
                                    rn: divisor,
                                    op2: Operand2::Imm(0),
                                },
                                source_line: Some(idx),
                            });
                            instructions.push(ArmInstruction {
                                op: ArmOp::BCondOffset {
                                    cond: Condition::NE,
                                    offset: 0,
                                },
                                source_line: Some(idx),
                            });
                            instructions.push(ArmInstruction {
                                op: ArmOp::Udf { imm: 0 },
                                source_line: Some(idx),
                            });
                        }

                        // Signed remainder: dst = dividend - (dividend/divisor)*divisor
                        let tmp = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::Sdiv {
                                rd: tmp,
                                rn: dividend,
                                rm: divisor,
                            },
                            source_line: Some(idx),
                        });
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mls {
                                rd: dst,
                                rn: tmp,
                                rm: divisor,
                                ra: dividend,
                            },
                            source_line: Some(idx),
                        });
                        stack.push(StackVal::i32(dst));
                    }
                }

                // #708 (phase 1b): `f32.load` — the VFP-load twin of the i32
                // load. VLDR takes only a `[Rn,#imm]` address (no index reg) and
                // the phase-1 selector does not model the static-data/native-
                // pointer address rewrites, so rather than reinvent the address
                // machinery we LOAD the 4-byte word with the PROVEN integer path
                // (`generate_load_with_bounds_check`: the `[R11,idx]`→absolute-
                // base rewrite + optional bounds guard) into a core register,
                // then bit-cast it into an S-register with `VMOV Sd,Rd`. A VLDR
                // would load the identical 4 bytes, so the result bit pattern is
                // exact. Honest-decline the native-pointer static-data address
                // mode (#359) we don't yet lower here — never a silent miscompile.
                F32Load { offset, .. } => {
                    if self.native_pointer_abi
                        && self.wasm_data_base > 0
                        && *offset >= self.wasm_data_base
                    {
                        return Err(synth_core::Error::synthesis(
                            "GI-FPU-002 phase 1b: f32.load from the static-data \
                             region under the native-pointer ABI is not yet \
                             lowered (#359 address relocation) — declining"
                                .to_string(),
                        ));
                    }
                    // The i32.load path (#95/#237) relocates a CONST effective
                    // address that lands in the static-data region; this f32.load
                    // arm only lowers the dynamic-index (branch-3) form, so a
                    // const static-data address would mis-address. Detect it with
                    // the same helpers and DECLINE loudly (never a silent
                    // miscompile). Dynamic-index loads — falcon's shape — are
                    // unaffected (`try_fold_const_addr` returns None).
                    if let Some(eff) = self.try_fold_const_addr(wasm_ops, idx, *offset)
                        && self.static_data_addend(eff).is_some()
                    {
                        return Err(synth_core::Error::synthesis(
                            "GI-FPU-002 phase 1b: f32.load from a constant \
                             static-data address is not yet lowered (#237 \
                             relocation) — declining"
                                .to_string(),
                        ));
                    }
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    // Core scratch for the loaded 32-bit word.
                    let dst = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let load_ops =
                        self.generate_load_with_bounds_check(dst, addr, *offset as i32, 4);
                    for op in load_ops {
                        instructions.push(ArmInstruction {
                            op,
                            source_line: Some(idx),
                        });
                    }
                    // Bit-cast the loaded word into an S-register (VMOV Sd,Rd).
                    let sd = alloc_vfp_temp(&mut vfp_used)?;
                    instructions.push(ArmInstruction {
                        op: ArmOp::F32ReinterpretI32 { sd, rm: dst },
                        source_line: Some(idx),
                    });
                    stack.push(StackVal::Float { sreg: sd });
                }

                // #719 (phase 1b): `f32.store` — the VFP-store twin of `f32.load`
                // (falcon has 10). VSTR takes only a `[Rn,#imm]` address, and the
                // phase-1 selector does not model the static-data/native-pointer
                // address rewrites, so we bit-cast the S-register value into a core
                // register (`VMOV Rn,Sn`, a reinterpret) and store it with the
                // PROVEN integer path (`generate_store_with_bounds_check`). A VSTR
                // would write the identical 4 bytes, so the stored word is exact.
                // Honest-decline the native-pointer static-data + const static-data
                // address modes we don't yet lower (symmetric to F32Load) — never
                // a silent miscompile; falcon's dynamic-index stores are unaffected.
                F32Store { offset, .. } => {
                    if self.native_pointer_abi
                        && self.wasm_data_base > 0
                        && *offset >= self.wasm_data_base
                    {
                        return Err(synth_core::Error::synthesis(
                            "GI-FPU-002 phase 1b: f32.store to the static-data \
                             region under the native-pointer ABI is not yet \
                             lowered (#359 address relocation) — declining"
                                .to_string(),
                        ));
                    }
                    if let Some(eff) = self.try_fold_const_addr_store(wasm_ops, idx, *offset)
                        && self.static_data_addend(eff).is_some()
                    {
                        return Err(synth_core::Error::synthesis(
                            "GI-FPU-002 phase 1b: f32.store to a constant \
                             static-data address is not yet lowered (#237 \
                             relocation) — declining"
                                .to_string(),
                        ));
                    }
                    // WASM f32.store pops: value (f32) first, then address (i32).
                    let sval = pop_float(&mut stack)?;
                    // Bit-cast the f32 value into a core register (VMOV Rn,Sn).
                    let value = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    instructions.push(ArmInstruction {
                        op: ArmOp::I32ReinterpretF32 {
                            rd: value,
                            sm: sval,
                        },
                        source_line: Some(idx),
                    });
                    free_vfp_temp(&mut vfp_used, &vfp_home, sval);
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let store_ops =
                        self.generate_store_with_bounds_check(value, addr, *offset as i32, 4);
                    for op in store_ops {
                        instructions.push(ArmInstruction {
                            op,
                            source_line: Some(idx),
                        });
                    }
                    // Store pushes nothing.
                }

                // GI-FPU-002 phase 2 (#369): `f64.load` — two PROVEN 4-byte
                // integer loads (lo word at `offset`, hi word at `offset+4`,
                // each with its own bounds guard, jointly covering the 8-byte
                // access) bit-cast into a D-register via `VMOV Dd, lo, hi`.
                // Same honest declines as `F32Load` for the address modes this
                // phase does not lower; additionally declines `--safety-bounds
                // mask`, whose masking MUTATES the address register in place,
                // so a second masked access off the same register would
                // re-mask an already-masked address (wrong effective address).
                F64Load { offset, .. } => {
                    if self.bounds_check == BoundsCheckConfig::Masking {
                        return Err(synth_core::Error::synthesis(
                            "GI-FPU-002 phase 2: f64.load under --safety-bounds                              mask is not lowered (the two-word access would                              re-mask its address register) — declining (#369)"
                                .to_string(),
                        ));
                    }
                    if self.native_pointer_abi
                        && self.wasm_data_base > 0
                        && *offset >= self.wasm_data_base
                    {
                        return Err(synth_core::Error::synthesis(
                            "GI-FPU-002 phase 2: f64.load from the static-data                              region under the native-pointer ABI is not yet                              lowered (#359 address relocation) — declining"
                                .to_string(),
                        ));
                    }
                    if let Some(eff) = self.try_fold_const_addr(wasm_ops, idx, *offset)
                        && self.static_data_addend(eff).is_some()
                    {
                        return Err(synth_core::Error::synthesis(
                            "GI-FPU-002 phase 2: f64.load from a constant                              static-data address is not yet lowered (#237                              relocation) — declining"
                                .to_string(),
                        ));
                    }
                    if *offset > (i32::MAX as u32) - 8 {
                        return Err(synth_core::Error::synthesis(
                            "GI-FPU-002 phase 2: f64.load static offset too                              large (hi-word offset would overflow) — declining"
                                .to_string(),
                        ));
                    }
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    // Two core scratches for the loaded words. Keep `addr` and
                    // `rlo` visibly live (placeholder stack entries) while
                    // allocating, so neither is handed out twice — the first
                    // load must not clobber the address the second one reads.
                    stack.push(StackVal::i32(addr));
                    let rlo = match alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    ) {
                        Ok(r) => r,
                        Err(e) => {
                            stack.pop();
                            return Err(e);
                        }
                    };
                    stack.push(StackVal::i32(rlo));
                    let rhi = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    );
                    stack.pop();
                    stack.pop();
                    let rhi = rhi?;
                    for (dst, off) in [(rlo, *offset as i32), (rhi, *offset as i32 + 4)] {
                        for op in self.generate_load_with_bounds_check(dst, addr, off, 4) {
                            instructions.push(ArmInstruction {
                                op,
                                source_line: Some(idx),
                            });
                        }
                    }
                    let dd = alloc_vfp_dtemp(&mut vfp_used)?;
                    instructions.push(ArmInstruction {
                        op: ArmOp::F64ReinterpretI64 {
                            dd,
                            rmlo: rlo,
                            rmhi: rhi,
                        },
                        source_line: Some(idx),
                    });
                    stack.push(StackVal::Double { dreg: dd });
                }

                // GI-FPU-002 phase 2 (#369): `f64.store` — `VMOV lo, hi, Dm`
                // then two PROVEN 4-byte integer stores. Mirrors `F64Load`'s
                // declines (masking / native-pointer static / const static
                // address / offset overflow).
                F64Store { offset, .. } => {
                    if self.bounds_check == BoundsCheckConfig::Masking {
                        return Err(synth_core::Error::synthesis(
                            "GI-FPU-002 phase 2: f64.store under --safety-bounds                              mask is not lowered (the two-word access would                              re-mask its address register) — declining (#369)"
                                .to_string(),
                        ));
                    }
                    if self.native_pointer_abi
                        && self.wasm_data_base > 0
                        && *offset >= self.wasm_data_base
                    {
                        return Err(synth_core::Error::synthesis(
                            "GI-FPU-002 phase 2: f64.store to the static-data                              region under the native-pointer ABI is not yet                              lowered (#359 address relocation) — declining"
                                .to_string(),
                        ));
                    }
                    if let Some(eff) = self.try_fold_const_addr_store(wasm_ops, idx, *offset)
                        && self.static_data_addend(eff).is_some()
                    {
                        return Err(synth_core::Error::synthesis(
                            "GI-FPU-002 phase 2: f64.store to a constant                              static-data address is not yet lowered (#237                              relocation) — declining"
                                .to_string(),
                        ));
                    }
                    if *offset > (i32::MAX as u32) - 8 {
                        return Err(synth_core::Error::synthesis(
                            "GI-FPU-002 phase 2: f64.store static offset too                              large (hi-word offset would overflow) — declining"
                                .to_string(),
                        ));
                    }
                    // WASM f64.store pops: value (f64) first, then address.
                    let dval = pop_double(&mut stack)?;
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    // Two core scratches for the value words; keep `addr` and
                    // `rlo` visibly live during allocation (see F64Load).
                    stack.push(StackVal::i32(addr));
                    let rlo = match alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    ) {
                        Ok(r) => r,
                        Err(e) => {
                            stack.pop();
                            return Err(e);
                        }
                    };
                    stack.push(StackVal::i32(rlo));
                    let rhi = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    );
                    stack.pop();
                    stack.pop();
                    let rhi = rhi?;
                    instructions.push(ArmInstruction {
                        op: ArmOp::I64ReinterpretF64 {
                            rdlo: rlo,
                            rdhi: rhi,
                            dm: dval,
                        },
                        source_line: Some(idx),
                    });
                    free_vfp_dtemp(&mut vfp_used, &vfp_home, dval);
                    for (src, off) in [(rlo, *offset as i32), (rhi, *offset as i32 + 4)] {
                        for op in self.generate_store_with_bounds_check(src, addr, off, 4) {
                            instructions.push(ArmInstruction {
                                op,
                                source_line: Some(idx),
                            });
                        }
                    }
                    // Store pushes nothing.
                }

                // Memory operations need stack-aware handling
                I32Load { offset, .. } => {
                    // Issue #95: fold `i32.const C; i32.load offset=O` to a
                    // single `LDR rd, [R11, #(C+O)]` when the effective offset
                    // fits in imm12. Drops the MOVW(+MOVT) const materialization.
                    let folded = self.try_fold_const_addr(wasm_ops, idx, *offset);
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    // Result goes in R0 if this is the last value-producing op (before End)
                    // Check if next op is End or if we're at the last position
                    let is_return_value = idx == wasm_ops.len() - 1
                        || (idx + 1 < wasm_ops.len() && matches!(wasm_ops[idx + 1], End));
                    let dst = if is_return_value {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };

                    if let Some(eff_offset) = folded {
                        Self::drop_prev_const_materialization(&mut instructions, idx - 1);
                        if let Some(addend) = self.static_data_addend(eff_offset) {
                            // #237: static → base-independent address in `dst`,
                            // then load `[dst]` (the load overwrites the address).
                            Self::emit_wasm_data_addr(&mut instructions, dst, addend, idx);
                            instructions.push(ArmInstruction {
                                op: ArmOp::Ldr {
                                    rd: dst,
                                    addr: MemAddr::imm(dst, 0),
                                },
                                source_line: Some(idx),
                            });
                        } else {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Ldr {
                                    rd: dst,
                                    addr: MemAddr::imm(Reg::R11, eff_offset as i32),
                                },
                                source_line: Some(idx),
                            });
                        }
                    } else if self.native_pointer_abi
                        && self.wasm_data_base > 0
                        && *offset >= self.wasm_data_base
                    {
                        // #359: a DYNAMIC-index access whose constant `offset`
                        // lands in the static-data region (e.g. an action→ret
                        // `.rodata` table at `[idx + 65536]`). The static path
                        // above relocates a constant address; this dynamic case
                        // was previously emitted as raw `[R11 + addr + offset]`,
                        // which mis-addresses the table once it's relocated to
                        // `__synth_wasm_data`/`__synth_wasm_seg_K` (under the
                        // native-pointer ABI R11/fp is 0, and #354 moves a
                        // high-offset segment out of line). Relocate the base to
                        // `__synth_wasm_data + offset` (the ELF builder retargets
                        // it to the owning segment symbol) and add the dynamic
                        // index: `__synth_wasm_data + offset + addr`.
                        let base = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &[live_params.as_slice(), &[addr, dst]].concat(),
                            idx,
                        )?;
                        Self::emit_wasm_data_addr(&mut instructions, base, *offset as i32, idx);
                        instructions.push(ArmInstruction {
                            op: ArmOp::Add {
                                rd: base,
                                rn: base,
                                op2: Operand2::Reg(addr),
                            },
                            source_line: Some(idx),
                        });
                        instructions.push(ArmInstruction {
                            op: ArmOp::Ldr {
                                rd: dst,
                                addr: MemAddr::imm(base, 0),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else {
                        // Generate load with optional bounds checking.
                        // #494 bounds-elision: a certificate-discharged mark
                        // for THIS op index strips the software guard.
                        let load_ops = self.apply_mem_bounds_elision(
                            idx,
                            self.generate_load_with_bounds_check(dst, addr, *offset as i32, 4),
                        );
                        for op in load_ops {
                            instructions.push(ArmInstruction {
                                op,
                                source_line: Some(idx),
                            });
                        }
                    }
                    stack.push(StackVal::i32(dst));
                }

                I32Store { offset, .. } => {
                    // Issue #95: fold `i32.const C; <pusher>; i32.store offset=O`
                    // to `STR val_reg, [R11, #(C+O)]` when effective offset fits.
                    let folded = self.try_fold_const_addr_store(wasm_ops, idx, *offset);
                    // WASM i32.store pops: value first, then address
                    let value = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;

                    if let Some(eff_offset) = folded {
                        Self::splice_out_addr_const_materialization(
                            &mut instructions,
                            idx - 2,
                            idx - 1,
                        );
                        if let Some(addend) = self.static_data_addend(eff_offset) {
                            // #237: static store — materialize the base-independent
                            // address into a scratch reg, then `STR value, [addr]`.
                            let a = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &live_params,
                                idx,
                            )?;
                            Self::emit_wasm_data_addr(&mut instructions, a, addend, idx);
                            instructions.push(ArmInstruction {
                                op: ArmOp::Str {
                                    rd: value,
                                    addr: MemAddr::imm(a, 0),
                                },
                                source_line: Some(idx),
                            });
                        } else {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Str {
                                    rd: value,
                                    addr: MemAddr::imm(Reg::R11, eff_offset as i32),
                                },
                                source_line: Some(idx),
                            });
                        }
                    } else if self.native_pointer_abi
                        && self.wasm_data_base > 0
                        && *offset >= self.wasm_data_base
                    {
                        // #359 (symmetric to I32Load): a dynamic-index store whose
                        // constant `offset` lands in the static-data region must
                        // relocate the base to `__synth_wasm_data + offset` (ELF
                        // builder retargets to the owning segment) + the dynamic
                        // index, not raw `[R11 + addr + offset]`.
                        let base = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &[live_params.as_slice(), &[addr, value]].concat(),
                            idx,
                        )?;
                        Self::emit_wasm_data_addr(&mut instructions, base, *offset as i32, idx);
                        instructions.push(ArmInstruction {
                            op: ArmOp::Add {
                                rd: base,
                                rn: base,
                                op2: Operand2::Reg(addr),
                            },
                            source_line: Some(idx),
                        });
                        instructions.push(ArmInstruction {
                            op: ArmOp::Str {
                                rd: value,
                                addr: MemAddr::imm(base, 0),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else {
                        // Generate store with optional bounds checking.
                        // #494 bounds-elision: a certificate-discharged mark
                        // for THIS op index strips the software guard.
                        let store_ops = self.apply_mem_bounds_elision(
                            idx,
                            self.generate_store_with_bounds_check(value, addr, *offset as i32, 4),
                        );
                        for op in store_ops {
                            instructions.push(ArmInstruction {
                                op,
                                source_line: Some(idx),
                            });
                        }
                    }
                    // Store doesn't push anything to stack
                }

                // Sub-word loads (i32) — like I32Load but with LDRB/LDRSB/LDRH/LDRSH
                I32Load8S { offset, .. }
                | I32Load8U { offset, .. }
                | I32Load16S { offset, .. }
                | I32Load16U { offset, .. } => {
                    // Issue #95: same const-address fold as I32Load.
                    let folded = self.try_fold_const_addr(wasm_ops, idx, *offset);
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let is_return_value = idx == wasm_ops.len() - 1
                        || (idx + 1 < wasm_ops.len() && matches!(wasm_ops[idx + 1], End));
                    let dst = if is_return_value {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };

                    let (access_size, sign_extend) = match op {
                        I32Load8S { .. } => (1, true),
                        I32Load8U { .. } => (1, false),
                        I32Load16S { .. } => (2, true),
                        I32Load16U { .. } => (2, false),
                        _ => unreachable!(),
                    };

                    if let Some(eff_offset) = folded {
                        Self::drop_prev_const_materialization(&mut instructions, idx - 1);
                        // #739: same static-region classification as I32Load —
                        // a folded const address in the static region must be
                        // relocated (`__synth_wasm_data + C`), never baked as a
                        // raw `[R11, #imm]` offset.
                        let mem = if let Some(addend) = self.static_data_addend(eff_offset) {
                            Self::emit_wasm_data_addr(&mut instructions, dst, addend, idx);
                            MemAddr::imm(dst, 0)
                        } else {
                            MemAddr::imm(Reg::R11, eff_offset as i32)
                        };
                        let arm_op = match (access_size, sign_extend) {
                            (1, false) => ArmOp::Ldrb { rd: dst, addr: mem },
                            (1, true) => ArmOp::Ldrsb { rd: dst, addr: mem },
                            (2, false) => ArmOp::Ldrh { rd: dst, addr: mem },
                            (2, true) => ArmOp::Ldrsh { rd: dst, addr: mem },
                            _ => unreachable!(),
                        };
                        instructions.push(ArmInstruction {
                            op: arm_op,
                            source_line: Some(idx),
                        });
                    } else if self.is_native_pointer_static_offset(*offset) {
                        // #739 (gale's gust:os buffer node): a DYNAMIC-index
                        // sub-word load whose constant memarg `offset` lands in
                        // the static-data region. Pre-fix this fell through to
                        // the raw `[R11 + addr + #offset]` path below, BAKING
                        // the 1 MiB-region linmem offset as an un-relocated
                        // `MOVW/MOVT ip` immediate — invisible to the #678
                        // `--shadow-stack-size` rebase (which walks relocations)
                        // → silent OOB on the shrunk reservation. Relocate the
                        // base to `__synth_wasm_data + offset` (the ELF builder
                        // retargets it to the owning segment symbol) and add the
                        // dynamic index — exactly the I32Load #359 branch, with
                        // the sub-word LDR form.
                        let base = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &[live_params.as_slice(), &[addr, dst]].concat(),
                            idx,
                        )?;
                        Self::emit_wasm_data_addr(&mut instructions, base, *offset as i32, idx);
                        instructions.push(ArmInstruction {
                            op: ArmOp::Add {
                                rd: base,
                                rn: base,
                                op2: Operand2::Reg(addr),
                            },
                            source_line: Some(idx),
                        });
                        let mem = MemAddr::imm(base, 0);
                        let arm_op = match (access_size, sign_extend) {
                            (1, false) => ArmOp::Ldrb { rd: dst, addr: mem },
                            (1, true) => ArmOp::Ldrsb { rd: dst, addr: mem },
                            (2, false) => ArmOp::Ldrh { rd: dst, addr: mem },
                            (2, true) => ArmOp::Ldrsh { rd: dst, addr: mem },
                            _ => unreachable!(),
                        };
                        instructions.push(ArmInstruction {
                            op: arm_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else {
                        // #494 bounds-elision: a certificate-discharged mark
                        // for THIS op index strips the software guard.
                        let load_ops = self.apply_mem_bounds_elision(
                            idx,
                            self.generate_subword_load_with_bounds_check(
                                dst,
                                addr,
                                *offset as i32,
                                access_size,
                                sign_extend,
                            ),
                        );
                        for arm_op in load_ops {
                            instructions.push(ArmInstruction {
                                op: arm_op,
                                source_line: Some(idx),
                            });
                        }
                    }
                    stack.push(StackVal::i32(dst));
                }

                // Sub-word stores (i32) — like I32Store but with STRB/STRH
                I32Store8 { offset, .. } | I32Store16 { offset, .. } => {
                    // Issue #95: same const-address fold as I32Store.
                    let folded = self.try_fold_const_addr_store(wasm_ops, idx, *offset);
                    let value = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;

                    let access_size = match op {
                        I32Store8 { .. } => 1,
                        I32Store16 { .. } => 2,
                        _ => unreachable!(),
                    };

                    if let Some(eff_offset) = folded {
                        Self::splice_out_addr_const_materialization(
                            &mut instructions,
                            idx - 2,
                            idx - 1,
                        );
                        // #739: same static-region classification as I32Store —
                        // a folded const address in the static region must be
                        // relocated, never baked as a raw `[R11, #imm]` offset.
                        let mem = if let Some(addend) = self.static_data_addend(eff_offset) {
                            let a = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &[live_params.as_slice(), &[value]].concat(),
                                idx,
                            )?;
                            Self::emit_wasm_data_addr(&mut instructions, a, addend, idx);
                            MemAddr::imm(a, 0)
                        } else {
                            MemAddr::imm(Reg::R11, eff_offset as i32)
                        };
                        let arm_op = match access_size {
                            1 => ArmOp::Strb {
                                rd: value,
                                addr: mem,
                            },
                            2 => ArmOp::Strh {
                                rd: value,
                                addr: mem,
                            },
                            _ => unreachable!(),
                        };
                        instructions.push(ArmInstruction {
                            op: arm_op,
                            source_line: Some(idx),
                        });
                    } else if self.is_native_pointer_static_offset(*offset) {
                        // #739 (symmetric to the sub-word load): a dynamic-index
                        // sub-word store into the static-data region must
                        // relocate its base to `__synth_wasm_data + offset` +
                        // the dynamic index — the raw path below would bake the
                        // linmem offset as an un-relocated MOVW/MOVT immediate
                        // (silent OOB once `--shadow-stack-size` shrinks the
                        // reservation; the store lands in unmapped memory).
                        let base = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &[live_params.as_slice(), &[addr, value]].concat(),
                            idx,
                        )?;
                        Self::emit_wasm_data_addr(&mut instructions, base, *offset as i32, idx);
                        instructions.push(ArmInstruction {
                            op: ArmOp::Add {
                                rd: base,
                                rn: base,
                                op2: Operand2::Reg(addr),
                            },
                            source_line: Some(idx),
                        });
                        let mem = MemAddr::imm(base, 0);
                        let arm_op = match access_size {
                            1 => ArmOp::Strb {
                                rd: value,
                                addr: mem,
                            },
                            2 => ArmOp::Strh {
                                rd: value,
                                addr: mem,
                            },
                            _ => unreachable!(),
                        };
                        instructions.push(ArmInstruction {
                            op: arm_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else {
                        // #494 bounds-elision: a certificate-discharged mark
                        // for THIS op index strips the software guard.
                        let store_ops = self.apply_mem_bounds_elision(
                            idx,
                            self.generate_subword_store_with_bounds_check(
                                value,
                                addr,
                                *offset as i32,
                                access_size,
                            ),
                        );
                        for arm_op in store_ops {
                            instructions.push(ArmInstruction {
                                op: arm_op,
                                source_line: Some(idx),
                            });
                        }
                    }
                }

                // i64 sub-word loads — load sub-word, extend to i64 (register pair)
                //
                // Pre-fix `dst_lo` and `dst_hi` were hardcoded to R0:R1,
                // clobbering AAPCS params 0 and 1 on every i64.load{8,16,32}*
                // — even when the function had 2+ params and neither was
                // the address operand. Use `alloc_consecutive_pair` with
                // `addr` in `extra_avoid` so the destination pair never
                // overlaps the address register OR a live param.
                I64Load8S { offset, .. }
                | I64Load8U { offset, .. }
                | I64Load16S { offset, .. }
                | I64Load16U { offset, .. }
                | I64Load32S { offset, .. }
                | I64Load32U { offset, .. } => {
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[addr],
                        &live_params,
                        idx,
                    )?;

                    if self.is_native_pointer_static_offset(*offset) {
                        // #746 (the #739 residual): a dynamic-index i64
                        // NARROW load whose constant memarg `offset` lands in
                        // the static-data region. Pre-fix this arm declined
                        // loudly (#744 relocated only the i32 sub-word arms);
                        // the raw path below would bake the linmem offset as
                        // an un-relocated MOVW/MOVT immediate — invisible to
                        // the #678 `--shadow-stack-size` rebase → silent OOB.
                        // Relocate the base to `__synth_wasm_data + offset` +
                        // the dynamic index, load the low half through it,
                        // then fill the high half (sign / zero extend) —
                        // exactly the #744 sub-word branch, plus the hi fill.
                        let base = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &[live_params.as_slice(), &[addr, dst_lo, dst_hi]].concat(),
                            idx,
                        )?;
                        Self::emit_wasm_data_addr(&mut instructions, base, *offset as i32, idx);
                        instructions.push(ArmInstruction {
                            op: ArmOp::Add {
                                rd: base,
                                rn: base,
                                op2: Operand2::Reg(addr),
                            },
                            source_line: Some(idx),
                        });
                        let mem = MemAddr::imm(base, 0);
                        let (load_op, sign_extend) = match op {
                            I64Load8S { .. } => (
                                ArmOp::Ldrsb {
                                    rd: dst_lo,
                                    addr: mem,
                                },
                                true,
                            ),
                            I64Load8U { .. } => (
                                ArmOp::Ldrb {
                                    rd: dst_lo,
                                    addr: mem,
                                },
                                false,
                            ),
                            I64Load16S { .. } => (
                                ArmOp::Ldrsh {
                                    rd: dst_lo,
                                    addr: mem,
                                },
                                true,
                            ),
                            I64Load16U { .. } => (
                                ArmOp::Ldrh {
                                    rd: dst_lo,
                                    addr: mem,
                                },
                                false,
                            ),
                            I64Load32S { .. } => (
                                ArmOp::Ldr {
                                    rd: dst_lo,
                                    addr: mem,
                                },
                                true,
                            ),
                            I64Load32U { .. } => (
                                ArmOp::Ldr {
                                    rd: dst_lo,
                                    addr: mem,
                                },
                                false,
                            ),
                            _ => unreachable!(),
                        };
                        let hi_fill = if sign_extend {
                            ArmOp::Asr {
                                rd: dst_hi,
                                rn: dst_lo,
                                shift: 31,
                            }
                        } else {
                            ArmOp::Mov {
                                rd: dst_hi,
                                op2: Operand2::Imm(0),
                            }
                        };
                        for arm_op in [load_op, hi_fill] {
                            instructions.push(ArmInstruction {
                                op: arm_op,
                                source_line: Some(idx),
                            });
                        }
                        cf.add_instruction();
                        stack.push(StackVal::i64(dst_lo));
                        continue;
                    }

                    let ops: Vec<ArmOp> = match op {
                        I64Load8S { .. } => {
                            let mut v = self.generate_subword_load_with_bounds_check(
                                dst_lo,
                                addr,
                                *offset as i32,
                                1,
                                true,
                            );
                            v.push(ArmOp::Asr {
                                rd: dst_hi,
                                rn: dst_lo,
                                shift: 31,
                            });
                            v
                        }
                        I64Load8U { .. } => {
                            let mut v = self.generate_subword_load_with_bounds_check(
                                dst_lo,
                                addr,
                                *offset as i32,
                                1,
                                false,
                            );
                            v.push(ArmOp::Mov {
                                rd: dst_hi,
                                op2: Operand2::Imm(0),
                            });
                            v
                        }
                        I64Load16S { .. } => {
                            let mut v = self.generate_subword_load_with_bounds_check(
                                dst_lo,
                                addr,
                                *offset as i32,
                                2,
                                true,
                            );
                            v.push(ArmOp::Asr {
                                rd: dst_hi,
                                rn: dst_lo,
                                shift: 31,
                            });
                            v
                        }
                        I64Load16U { .. } => {
                            let mut v = self.generate_subword_load_with_bounds_check(
                                dst_lo,
                                addr,
                                *offset as i32,
                                2,
                                false,
                            );
                            v.push(ArmOp::Mov {
                                rd: dst_hi,
                                op2: Operand2::Imm(0),
                            });
                            v
                        }
                        I64Load32S { .. } => {
                            let mut v = self.generate_load_with_bounds_check(
                                dst_lo,
                                addr,
                                *offset as i32,
                                4,
                            );
                            v.push(ArmOp::Asr {
                                rd: dst_hi,
                                rn: dst_lo,
                                shift: 31,
                            });
                            v
                        }
                        I64Load32U { .. } => {
                            let mut v = self.generate_load_with_bounds_check(
                                dst_lo,
                                addr,
                                *offset as i32,
                                4,
                            );
                            v.push(ArmOp::Mov {
                                rd: dst_hi,
                                op2: Operand2::Imm(0),
                            });
                            v
                        }
                        _ => unreachable!(),
                    };

                    for arm_op in ops {
                        instructions.push(ArmInstruction {
                            op: arm_op,
                            source_line: Some(idx),
                        });
                    }
                    // i64 on 32-bit ARM uses register pair; push low register
                    stack.push(StackVal::i64(dst_lo));
                }

                // i64 sub-word stores
                I64Store8 { offset, .. }
                | I64Store16 { offset, .. }
                | I64Store32 { offset, .. } => {
                    // Pop i64 value (lo register) and address
                    let value_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;

                    if self.is_native_pointer_static_offset(*offset) {
                        // #746 (symmetric to the i64 narrow load): a
                        // dynamic-index i64 narrow store into the static-data
                        // region must relocate its base to `__synth_wasm_data
                        // + offset` + the dynamic index (only the LOW half is
                        // stored — wrapping semantics, same as the raw path).
                        // Pre-fix this arm declined loudly (#744 relocated
                        // only the i32 sub-word arms); the raw path below
                        // would bake the linmem offset as an un-relocated
                        // MOVW/MOVT immediate (silent OOB once
                        // `--shadow-stack-size` shrinks the reservation).
                        let base = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &[live_params.as_slice(), &[addr, value_lo]].concat(),
                            idx,
                        )?;
                        Self::emit_wasm_data_addr(&mut instructions, base, *offset as i32, idx);
                        instructions.push(ArmInstruction {
                            op: ArmOp::Add {
                                rd: base,
                                rn: base,
                                op2: Operand2::Reg(addr),
                            },
                            source_line: Some(idx),
                        });
                        let mem = MemAddr::imm(base, 0);
                        let arm_op = match op {
                            I64Store8 { .. } => ArmOp::Strb {
                                rd: value_lo,
                                addr: mem,
                            },
                            I64Store16 { .. } => ArmOp::Strh {
                                rd: value_lo,
                                addr: mem,
                            },
                            I64Store32 { .. } => ArmOp::Str {
                                rd: value_lo,
                                addr: mem,
                            },
                            _ => unreachable!(),
                        };
                        instructions.push(ArmInstruction {
                            op: arm_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        continue;
                    }

                    let ops: Vec<ArmOp> = match op {
                        I64Store8 { .. } => self.generate_subword_store_with_bounds_check(
                            value_lo,
                            addr,
                            *offset as i32,
                            1,
                        ),
                        I64Store16 { .. } => self.generate_subword_store_with_bounds_check(
                            value_lo,
                            addr,
                            *offset as i32,
                            2,
                        ),
                        I64Store32 { .. } => {
                            self.generate_store_with_bounds_check(value_lo, addr, *offset as i32, 4)
                        }
                        _ => unreachable!(),
                    };

                    for arm_op in ops {
                        instructions.push(ArmInstruction {
                            op: arm_op,
                            source_line: Some(idx),
                        });
                    }
                }

                // Memory management
                MemorySize(mem_idx) => {
                    let dst = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    if *mem_idx == 0 {
                        // Memory 0: runtime size register (R10 >> 16 = pages),
                        // byte-identical to the pre-#406 lowering.
                        instructions.push(ArmInstruction {
                            op: ArmOp::MemorySize { rd: dst },
                            source_line: Some(idx),
                        });
                    } else {
                        // VCR-MEM-002 phase 1 (#406): memory k > 0 has no
                        // runtime size register (R10 belongs to memory 0 —
                        // reading it here silently returned memory 0's size).
                        // Its size is FIXED at the declared initial page count:
                        // `memory.grow` on this backend always lowers to the
                        // fixed-memory -1 (see `ArmOp::MemoryGrow`), so the
                        // size can never change — materialize the constant.
                        // The runtime contract is that the embedder maps the
                        // `__synth_wasm_data_<k>` region at exactly its
                        // declared initial size (the ELF NOBITS/PROGBITS
                        // section is emitted at that size).
                        let pages = self.multi_memory_pages(*mem_idx)?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::Movw {
                                rd: dst,
                                imm16: (pages & 0xFFFF) as u16,
                            },
                            source_line: Some(idx),
                        });
                        if pages > 0xFFFF {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Movt {
                                    rd: dst,
                                    imm16: ((pages >> 16) & 0xFFFF) as u16,
                                },
                                source_line: Some(idx),
                            });
                        }
                    }
                    stack.push(StackVal::i32(dst));
                }

                MemoryGrow(mem_idx) => {
                    // VCR-MEM-002 phase 1 (#406): the fixed-memory `-1`
                    // lowering below is memory-agnostic (no state read), so it
                    // is equally correct for memory k > 0 — but only in a
                    // configuration whose multi-memory context is validated
                    // (relocatable, known index). Same typed declines as the
                    // load/store path.
                    if *mem_idx != 0 {
                        self.multi_memory_pages(*mem_idx)?;
                    }
                    // Pop the requested number of pages from stack
                    let pages = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    instructions.push(ArmInstruction {
                        op: ArmOp::MemoryGrow { rd: dst, rn: pages },
                        source_line: Some(idx),
                    });
                    stack.push(StackVal::i32(dst));
                }

                // =========================================================
                // Multi-memory (#406, VCR-MEM-002 phase 1)
                // =========================================================
                // A load/store on a NON-DEFAULT memory (memidx > 0). R11 is
                // memory 0's base; memory k is addressed base-independently
                // via its own `__synth_wasm_data_<k>` region symbol (Abs32
                // literal-pool load, the #345 link-survivable form), which
                // build_relocatable_elf defines at the base of memory k's
                // NOBITS/PROGBITS section:
                //
                //     LDR  base, =__synth_wasm_data_k + memarg.offset
                //     ADD  base, base, addr
                //     LDR/STR[B/H] value, [base]
                //
                // Phase-1 scope: the i32 access family only. i64/f32/f64/v128
                // accesses and `--safety-bounds` on memory k decline LOUDLY
                // (typed Err → loud-skip), never alias memory 0.
                MultiMemory {
                    memory,
                    op: inner_op,
                } => {
                    // Validates the configuration (relocatable, no
                    // native-pointer ABI, known index) — pages unused here.
                    self.multi_memory_pages(*memory)?;
                    if self.bounds_check != BoundsCheckConfig::None {
                        return Err(synth_core::Error::synthesis(format!(
                            "multi-memory: --safety-bounds is not lowered for an \
                             op on memory {memory} in phase 1 — the bounds \
                             machinery (R10/mask) is memory-0-only (#406)"
                        )));
                    }
                    let sym = Self::wasm_data_symbol(*memory);
                    match inner_op.as_ref() {
                        I32Load { offset, .. }
                        | I32Load8S { offset, .. }
                        | I32Load8U { offset, .. }
                        | I32Load16S { offset, .. }
                        | I32Load16U { offset, .. } => {
                            let addr = pop_operand(
                                &mut stack,
                                &mut next_temp,
                                &mut instructions,
                                &mut spill,
                                &live_params,
                                idx,
                            )?;
                            let dst = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &[live_params.as_slice(), &[addr]].concat(),
                                idx,
                            )?;
                            let base = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &[live_params.as_slice(), &[addr, dst]].concat(),
                                idx,
                            )?;
                            Self::emit_sym_addr(&mut instructions, base, &sym, *offset as i32, idx);
                            instructions.push(ArmInstruction {
                                op: ArmOp::Add {
                                    rd: base,
                                    rn: base,
                                    op2: Operand2::Reg(addr),
                                },
                                source_line: Some(idx),
                            });
                            let mem = MemAddr::imm(base, 0);
                            let load_op = match inner_op.as_ref() {
                                I32Load { .. } => ArmOp::Ldr { rd: dst, addr: mem },
                                I32Load8U { .. } => ArmOp::Ldrb { rd: dst, addr: mem },
                                I32Load8S { .. } => ArmOp::Ldrsb { rd: dst, addr: mem },
                                I32Load16U { .. } => ArmOp::Ldrh { rd: dst, addr: mem },
                                I32Load16S { .. } => ArmOp::Ldrsh { rd: dst, addr: mem },
                                _ => unreachable!(),
                            };
                            instructions.push(ArmInstruction {
                                op: load_op,
                                source_line: Some(idx),
                            });
                            cf.add_instructions(3);
                            stack.push(StackVal::i32(dst));
                        }
                        I32Store { offset, .. }
                        | I32Store8 { offset, .. }
                        | I32Store16 { offset, .. } => {
                            // WASM store pops: value first, then address.
                            let value = pop_operand(
                                &mut stack,
                                &mut next_temp,
                                &mut instructions,
                                &mut spill,
                                &live_params,
                                idx,
                            )?;
                            let addr = pop_operand(
                                &mut stack,
                                &mut next_temp,
                                &mut instructions,
                                &mut spill,
                                &live_params,
                                idx,
                            )?;
                            let base = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &[live_params.as_slice(), &[addr, value]].concat(),
                                idx,
                            )?;
                            Self::emit_sym_addr(&mut instructions, base, &sym, *offset as i32, idx);
                            instructions.push(ArmInstruction {
                                op: ArmOp::Add {
                                    rd: base,
                                    rn: base,
                                    op2: Operand2::Reg(addr),
                                },
                                source_line: Some(idx),
                            });
                            let mem = MemAddr::imm(base, 0);
                            let store_op = match inner_op.as_ref() {
                                I32Store { .. } => ArmOp::Str {
                                    rd: value,
                                    addr: mem,
                                },
                                I32Store8 { .. } => ArmOp::Strb {
                                    rd: value,
                                    addr: mem,
                                },
                                I32Store16 { .. } => ArmOp::Strh {
                                    rd: value,
                                    addr: mem,
                                },
                                _ => unreachable!(),
                            };
                            instructions.push(ArmInstruction {
                                op: store_op,
                                source_line: Some(idx),
                            });
                            cf.add_instructions(3);
                        }
                        other => {
                            return Err(synth_core::Error::synthesis(format!(
                                "multi-memory: {other:?} on memory {memory} is not \
                                 lowered in phase 1 — only the i32 load/store \
                                 family is (#406); wider/float accesses on a \
                                 non-default memory decline loudly"
                            )));
                        }
                    }
                }

                // =========================================================
                // Control flow operations
                // =========================================================
                Block => {
                    let label = self.alloc_label("block_end");
                    // #509: blocktype arity from the ordinal side-table —
                    // (0,0) (void) when absent, preserving the legacy lowering.
                    let (params, results) =
                        self.block_arity.get(ctrl_ord).copied().unwrap_or((0, 0));
                    ctrl_ord += 1;
                    // Push block info so br can find the end label
                    cf.enter_block(BlockType::Block);
                    block_labels.push(BlockLabel {
                        label, // end label
                        is_loop: false,
                        is_if: false,
                        params,
                        results,
                        result_reg: None, // allocated lazily at the first br edge
                    });
                    // No ARM code emitted at block entry (label at end)
                }

                Loop => {
                    let label = self.alloc_label("loop_start");
                    let (params, results) =
                        self.block_arity.get(ctrl_ord).copied().unwrap_or((0, 0));
                    ctrl_ord += 1;
                    cf.enter_block(BlockType::Loop);
                    block_labels.push(BlockLabel {
                        label: label.clone(), // start label
                        is_loop: true,
                        is_if: false,
                        params,
                        results,
                        result_reg: None,
                    });
                    // Emit loop start label
                    instructions.push(ArmInstruction {
                        op: ArmOp::Label { name: label },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                If => {
                    // Pop condition from stack
                    let cond_reg = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let else_label = self.alloc_label("else");
                    let end_label = self.alloc_label("if_end");

                    let (params, results) =
                        self.block_arity.get(ctrl_ord).copied().unwrap_or((0, 0));
                    ctrl_ord += 1;
                    cf.enter_block(BlockType::If);
                    // Store both labels: else_label for the if-branch, end_label for the end
                    if_labels.push((else_label.clone(), end_label.clone()));
                    // #509: `is_if` marks this join as #313-reconciled — a
                    // value-carrying br to it is declined at the branch site
                    // (the reconciliation registers are not knowable there).
                    block_labels.push(BlockLabel {
                        label: end_label,
                        is_loop: false,
                        is_if: true,
                        params,
                        results,
                        result_reg: None,
                    });
                    // #313: checkpoint the operand-stack depth (the condition is
                    // already popped). The then-arm runs from here; its results
                    // are whatever sits ABOVE this depth at `Else`. Reservation
                    // starts EMPTY — nothing needs protecting during the then-arm
                    // (it runs first); it is filled at `Else`.
                    if_checkpoints.push(stack.len());
                    if_then_results.push(Vec::new());

                    // CMP cond_reg, #0
                    instructions.push(ArmInstruction {
                        op: ArmOp::Cmp {
                            rn: cond_reg,
                            op2: Operand2::Imm(0),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();

                    // BEQ else_label (skip then-block if condition is zero)
                    instructions.push(ArmInstruction {
                        op: ArmOp::Bcc {
                            cond: Condition::EQ,
                            label: else_label,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                Else => {
                    // #313: the then-arm's results are the vstack entries above
                    // the checkpoint. Pop them (top-most last) and truncate the
                    // vstack back to the checkpoint so the else-arm starts from
                    // the SAME stack shape the then-arm did. The captured regs
                    // are reserved across the else-arm (via `if_then_results`,
                    // merged into `live_params` above) so the else-arm cannot
                    // clobber them — reproducing the buggy code's incidental
                    // protection (the then-results were on the vstack) exactly,
                    // which is what keeps the else-arm allocation byte-identical.
                    if let Some(&cp) = if_checkpoints.last() {
                        let then_results: Vec<StackVal> = stack.split_off(cp);
                        if let Some(slot) = if_then_results.last_mut() {
                            *slot = then_results;
                        }
                    }
                    // End of then-block: jump to end of if
                    if let Some((_, end_label)) = if_labels.last() {
                        instructions.push(ArmInstruction {
                            op: ArmOp::B {
                                label: end_label.clone(),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    // Emit else label
                    if let Some((else_label, _)) = if_labels.last() {
                        instructions.push(ArmInstruction {
                            op: ArmOp::Label {
                                name: else_label.clone(),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                }

                End => {
                    cf.exit_block();
                    // If this closes an if-block, emit the end label
                    // and possibly the else label (if no else was present).
                    //
                    // #930: "closes an if-block" is decided by the INNERMOST open
                    // construct (`block_labels.last()`), never by `if_labels`
                    // alone. A plain block/loop nested inside an if's then/else
                    // arm reaches its `End` while the enclosing if's labels are
                    // still on `if_labels`; the old `if_labels.last()` test
                    // misattributed that `End` to the if — emitting the if's
                    // else/end labels at the inner block's position, popping the
                    // wrong stacks, and NEVER emitting the inner block's own end
                    // label. Its `B .Lblock_end_N` then stayed an unresolved
                    // `b #0` placeholder landing mid-instruction (labels.wast
                    // br / br_if2, silent wrong value).
                    if block_labels.last().is_some_and(|bl| bl.is_if)
                        && let Some((else_label, end_label)) = if_labels.last().cloned()
                    {
                        // Check if the else label was already emitted
                        // by looking for it in the instructions
                        let else_emitted = instructions
                            .iter()
                            .any(|i| matches!(&i.op, ArmOp::Label { name } if *name == else_label));
                        if !else_emitted {
                            // No else clause: emit else label (same as end).
                            // A valid if-without-else has arity 0 (no result),
                            // so there is nothing to reconcile (#313).
                            instructions.push(ArmInstruction {
                                op: ArmOp::Label { name: else_label },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        // #313: reconcile the two arms onto a single set of
                        // result registers. The then-arm's results were captured
                        // and reserved at `Else` (`if_then_results`); the
                        // else-arm's results are the vstack entries above the
                        // checkpoint right now. The `mov R_then, R_else`s emitted
                        // here sit on the ELSE path (between the else-arm body and
                        // `end_label`); the then-path's `B end_label` (emitted at
                        // `Else`) jumps over them, so the then-arm's value is the
                        // one live at `end_label` on the then path while the else
                        // path moves its value into the same registers. When the
                        // two arms already chose the same register, NO `mov` is
                        // emitted (this is what keeps register-symmetric and
                        // control-flow-only if/else byte-identical to before).
                        let then_results = if_then_results.pop().unwrap_or_default();
                        let checkpoint = if_checkpoints.pop();
                        if else_emitted {
                            if let Some(cp) = checkpoint {
                                // else-arm results above the checkpoint, in the
                                // same bottom→top order as `then_results`.
                                let else_results: Vec<StackVal> = stack.split_off(cp);
                                if else_results.len() == then_results.len() {
                                    for (then_v, else_v) in
                                        then_results.iter().zip(else_results.iter())
                                    {
                                        reconcile_if_result(
                                            then_v,
                                            else_v,
                                            &mut instructions,
                                            idx,
                                        )?;
                                    }
                                } else {
                                    // Arity mismatch between arms (should not
                                    // happen for valid wasm). Restore what we
                                    // took rather than silently miscompile;
                                    // downstream may still Err cleanly.
                                    stack.extend(else_results);
                                }
                            }
                            // The merged results live in the then-arm's
                            // registers — push them back onto the vstack so the
                            // surrounding code (return / outer op) reads them.
                            stack.extend(then_results);
                        }
                        instructions.push(ArmInstruction {
                            op: ArmOp::Label { name: end_label },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        if_labels.pop();
                        block_labels.pop();
                    } else if let Some(bl) = block_labels.pop()
                        && !bl.is_loop
                    {
                        // #509: fall-through edge into a branched-to value
                        // block's join — land the falling-through result in the
                        // designated result register BEFORE the end label (the
                        // branch edges jump past this move, having already done
                        // their own), then push R_res as the block's result.
                        // `result_reg` is only ever Some for a branched-to
                        // arity-1 block, so plain/void blocks keep the legacy
                        // label-only epilogue byte-identically.
                        if let Some(r_res) = bl.result_reg {
                            if let Some(top) = stack.last().copied() {
                                if top.is_i64() {
                                    return Err(synth_core::Error::synthesis(
                                        "#509: i64 fall-through into an \
                                         i32-carrying block join — width \
                                         mismatch (invalid wasm or unsupported \
                                         shape); declined rather than \
                                         miscompiled"
                                            .to_string(),
                                    ));
                                }
                                let val = pop_operand(
                                    &mut stack,
                                    &mut next_temp,
                                    &mut instructions,
                                    &mut spill,
                                    &live_params,
                                    idx,
                                )?;
                                if val != r_res {
                                    instructions.push(ArmInstruction {
                                        op: ArmOp::Mov {
                                            rd: r_res,
                                            op2: Operand2::Reg(val),
                                        },
                                        source_line: Some(idx),
                                    });
                                    cf.add_instruction();
                                }
                            }
                            // (An empty stack here is dead code after a
                            // terminator — the branch edges already loaded
                            // R_res, so just publish it as the result.)
                            instructions.push(ArmInstruction {
                                op: ArmOp::Label { name: bl.label },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                            stack.push(StackVal::i32(r_res));
                        } else {
                            // Block end: emit end label
                            instructions.push(ArmInstruction {
                                op: ArmOp::Label { name: bl.label },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        // Loop end: no label at end (label is at start)
                    }
                    // else: function-level end, nothing to emit
                }

                Br(depth) => {
                    // Branch to the Nth enclosing block/loop
                    // block_labels + if_labels are combined into the block_labels stack
                    //
                    // #500: `checked_sub`, not `saturating_sub`. The old clamp
                    // sent a FUNCTION-LEVEL `br` (depth reaching the implicit
                    // function body, e.g. `br 1` inside one block) to
                    // `block_labels[0]` — the OUTERMOST block's end — so code
                    // after that block still executed (`br_func(1)` also stored
                    // the post-block value; red in
                    // `cf_shapes_500_differential.py`). And the old
                    // depth-exceeds-EMPTY-stack arm emitted a bare `bx lr`,
                    // skipping the frame dealloc + callee-saved pop. A
                    // function-level `br` IS a `return` — lower it exactly like
                    // the `Return` arm below.
                    match block_labels.len().checked_sub(1 + *depth as usize) {
                        Some(target_idx) => {
                            // #509: land a carried value in the target block's
                            // designated result register BEFORE the jump (no-op for
                            // void targets and plain loop back-edges).
                            edge_value_move(
                                &mut block_labels,
                                target_idx,
                                &mut stack,
                                &mut next_temp,
                                &mut instructions,
                                &mut spill,
                                &live_params,
                                idx,
                            )?;
                            // Loop: branch back to start; block: forward to end.
                            instructions.push(ArmInstruction {
                                op: ArmOp::B {
                                    label: block_labels[target_idx].label.clone(),
                                },
                                source_line: Some(idx),
                            });
                        }
                        None => {
                            // Function-level branch == return: result to R0,
                            // deallocate the frame, pop callee-saved + PC
                            // (mirrors the `Return` arm; the push-trim post-pass
                            // rewrites this Pop symmetrically with the prologue).
                            if !stack.is_empty() {
                                let val = pop_operand(
                                    &mut stack,
                                    &mut next_temp,
                                    &mut instructions,
                                    &mut spill,
                                    &live_params,
                                    idx,
                                )?;
                                if val != Reg::R0 {
                                    instructions.push(ArmInstruction {
                                        op: ArmOp::Mov {
                                            rd: Reg::R0,
                                            op2: Operand2::Reg(val),
                                        },
                                        source_line: Some(idx),
                                    });
                                    cf.add_instruction();
                                }
                            }
                            if layout.frame_size > 0 {
                                instructions.push(ArmInstruction {
                                    op: ArmOp::Add {
                                        rd: Reg::SP,
                                        rn: Reg::SP,
                                        op2: Operand2::Imm(layout.frame_size),
                                    },
                                    source_line: Some(idx),
                                });
                                cf.add_instruction();
                            }
                            instructions.push(ArmInstruction {
                                op: ArmOp::Pop {
                                    regs: vec![
                                        Reg::R4,
                                        Reg::R5,
                                        Reg::R6,
                                        Reg::R7,
                                        Reg::R8,
                                        Reg::PC,
                                    ],
                                },
                                source_line: Some(idx),
                            });
                        }
                    }
                    cf.add_instruction();
                }

                BrIf(depth) => {
                    // Pop condition from stack
                    let cond_reg = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;

                    // #509: land a carried value in the target block's
                    // designated result register. Emitted BEFORE the CMP so no
                    // instruction sits between CMP and Bcc; the value is PEEKED
                    // (it stays on the operand stack for the fall-through path,
                    // wasm `br_if : [t*] i32 -> [t*]`), and the mov on the
                    // not-taken path is dead — R_res is reserved for the
                    // block's extent and only meaningful at its join.
                    //
                    // #500: `checked_sub`, not `saturating_sub` — the old clamp
                    // sent a FUNCTION-LEVEL `br_if` to the outermost block's
                    // end (or, with no open blocks, silently emitted a lone
                    // CMP with no branch at all). A function-level `br_if` is
                    // a CONDITIONAL return: the whole return sequence sits
                    // inside the taken region (behind a BEQ over it), so the
                    // fall-through path — where the operand stack stays live —
                    // executes none of it.
                    match block_labels.len().checked_sub(1 + *depth as usize) {
                        Some(target_idx) => {
                            let mut edge_reserved = live_params.clone();
                            edge_reserved.push(cond_reg);
                            edge_value_move(
                                &mut block_labels,
                                target_idx,
                                &mut stack,
                                &mut next_temp,
                                &mut instructions,
                                &mut spill,
                                &edge_reserved,
                                idx,
                            )?;

                            // CMP cond_reg, #0
                            instructions.push(ArmInstruction {
                                op: ArmOp::Cmp {
                                    rn: cond_reg,
                                    op2: Operand2::Imm(0),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();

                            // BNE target_label (branch if non-zero)
                            instructions.push(ArmInstruction {
                                op: ArmOp::Bcc {
                                    cond: Condition::NE,
                                    label: block_labels[target_idx].label.clone(),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        None => {
                            // PEEK the would-be result BEFORE the CMP (a spilled
                            // top may need a reload, which must not sit between
                            // CMP and Bcc). The stack is NOT popped: on the
                            // fall-through path the value stays live.
                            let val = if stack.is_empty() {
                                None
                            } else {
                                let mut peek_reserved = live_params.clone();
                                peek_reserved.push(cond_reg);
                                Some(peek_operand(
                                    &mut stack,
                                    &mut next_temp,
                                    &mut instructions,
                                    &mut spill,
                                    &peek_reserved,
                                    idx,
                                )?)
                            };
                            let skip = self.alloc_label("brif_fnret_skip");

                            // CMP cond_reg, #0
                            instructions.push(ArmInstruction {
                                op: ArmOp::Cmp {
                                    rn: cond_reg,
                                    op2: Operand2::Imm(0),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();

                            // BEQ over the return sequence (not taken → return)
                            instructions.push(ArmInstruction {
                                op: ArmOp::Bcc {
                                    cond: Condition::EQ,
                                    label: skip.clone(),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();

                            // Taken region: result to R0, frame dealloc, pop+PC
                            // (mirrors the `Return` arm).
                            if let Some(val) = val
                                && val != Reg::R0
                            {
                                instructions.push(ArmInstruction {
                                    op: ArmOp::Mov {
                                        rd: Reg::R0,
                                        op2: Operand2::Reg(val),
                                    },
                                    source_line: Some(idx),
                                });
                                cf.add_instruction();
                            }
                            if layout.frame_size > 0 {
                                instructions.push(ArmInstruction {
                                    op: ArmOp::Add {
                                        rd: Reg::SP,
                                        rn: Reg::SP,
                                        op2: Operand2::Imm(layout.frame_size),
                                    },
                                    source_line: Some(idx),
                                });
                                cf.add_instruction();
                            }
                            instructions.push(ArmInstruction {
                                op: ArmOp::Pop {
                                    regs: vec![
                                        Reg::R4,
                                        Reg::R5,
                                        Reg::R6,
                                        Reg::R7,
                                        Reg::R8,
                                        Reg::PC,
                                    ],
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();

                            instructions.push(ArmInstruction {
                                op: ArmOp::Label { name: skip },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                    }
                }

                BrTable { targets, default } => {
                    // Pop index from stack
                    let index_reg = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;

                    // #509: land the carried value in EVERY distinct target
                    // block's designated result register up front, before the
                    // dispatch cascade (never between a CMP and its Bcc — a
                    // flag-setting MOV encoding would corrupt the condition).
                    // Each mov is dead on the edges that don't take it: every
                    // R_res is reserved for its block's extent and only
                    // meaningful at that block's join. Valid wasm gives all
                    // br_table targets the same arity, so either every edge
                    // carries the value or none does.
                    let mut moved: Vec<usize> = Vec::new();
                    for t in targets.iter().chain(std::iter::once(default)) {
                        let target_idx = block_labels.len().saturating_sub(1 + *t as usize);
                        if target_idx < block_labels.len() && !moved.contains(&target_idx) {
                            moved.push(target_idx);
                            let mut edge_reserved = live_params.clone();
                            edge_reserved.push(index_reg);
                            edge_value_move(
                                &mut block_labels,
                                target_idx,
                                &mut stack,
                                &mut next_temp,
                                &mut instructions,
                                &mut spill,
                                &edge_reserved,
                                idx,
                            )?;
                        }
                    }

                    // Emit cascading CMP + BEQ for each target
                    for (i, target) in targets.iter().enumerate() {
                        instructions.push(ArmInstruction {
                            op: ArmOp::Cmp {
                                rn: index_reg,
                                op2: Operand2::Imm(i as i32),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();

                        let target_idx = block_labels.len().saturating_sub(1 + *target as usize);
                        if target_idx < block_labels.len() {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Bcc {
                                    cond: Condition::EQ,
                                    label: block_labels[target_idx].label.clone(),
                                },
                                source_line: Some(idx),
                            });
                        }
                        cf.add_instruction();
                    }

                    // Default branch
                    let default_idx = block_labels.len().saturating_sub(1 + *default as usize);
                    if default_idx < block_labels.len() {
                        instructions.push(ArmInstruction {
                            op: ArmOp::B {
                                label: block_labels[default_idx].label.clone(),
                            },
                            source_line: Some(idx),
                        });
                    }
                    cf.add_instruction();
                }

                Return => {
                    // GI-FPU-002 (#782): a float result reaches an EXPLICIT
                    // `return` in the VFP file — home it to S0 (f32) / D0
                    // (f64) per AAPCS-VFP, exactly like the fall-through
                    // epilogue below the op loop (which already does this),
                    // instead of loud-declining in the integer pop. Same
                    // soundness guard as the epilogue (#719): a hard-float
                    // function whose f32/f64 result shows up integer-tagged
                    // (e.g. a call's R0 result) must NOT emit the integer R0
                    // return — the AAPCS-VFP caller reads S0/D0.
                    let ret_top_f32 = stack.last().and_then(|v| v.as_float());
                    let ret_top_f64 = stack.last().and_then(|v| v.as_double());
                    if (self.ret_f32 || self.ret_f64) && fpu.is_some() {
                        let top_matches = if self.ret_f64 {
                            ret_top_f64.is_some()
                        } else {
                            ret_top_f32.is_some()
                        };
                        if !top_matches {
                            return Err(synth_core::Error::synthesis(format!(
                                "GI-FPU-002 phase 2: function returns {} but an \
                                 explicit `return`'s result is in a core register \
                                 — refusing to emit an integer R0 return where an \
                                 AAPCS-VFP caller reads {} (declining, #719/#369)",
                                if self.ret_f64 { "f64" } else { "f32" },
                                if self.ret_f64 { "D0" } else { "S0" },
                            )));
                        }
                    }
                    if self.ret_f64
                        && let Some(dreg) = ret_top_f64
                    {
                        // Home to D0 via the core round-trip (bit-exact; no
                        // D→D move in the ArmOp set). R0/R1 are dead at the
                        // return of an f64-returning function.
                        if vfp_d_index(dreg) != Some(0) {
                            instructions.push(ArmInstruction {
                                op: ArmOp::I64ReinterpretF64 {
                                    rdlo: Reg::R0,
                                    rdhi: Reg::R1,
                                    dm: dreg,
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                            instructions.push(ArmInstruction {
                                op: ArmOp::F64ReinterpretI64 {
                                    dd: VfpReg::D0,
                                    rmlo: Reg::R0,
                                    rmhi: Reg::R1,
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        stack.pop();
                        free_vfp_dtemp(&mut vfp_used, &vfp_home, dreg);
                    } else if self.ret_f32
                        && let Some(sreg) = ret_top_f32
                    {
                        // Home to S0 via the R12 (IP scratch) round-trip.
                        if vfp_s_index(sreg) != Some(0) {
                            instructions.push(ArmInstruction {
                                op: ArmOp::I32ReinterpretF32 {
                                    rd: Reg::R12,
                                    sm: sreg,
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                            instructions.push(ArmInstruction {
                                op: ArmOp::F32ReinterpretI32 {
                                    sd: VfpReg::S0,
                                    rm: Reg::R12,
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        stack.pop();
                        free_vfp_temp(&mut vfp_used, &vfp_home, sreg);
                    } else if ret_top_f32.is_some() || ret_top_f64.is_some() {
                        // A float on top of the stack at the `return` of a
                        // function that does not return that float type —
                        // invalid wasm (or an unlowered shape). Loud, as ever.
                        return Err(synth_core::Error::synthesis(
                            "GI-FPU-002: a VFP stack value reached an explicit \
                             `return` of a non-float-returning function — \
                             invalid wasm or an unlowered float op reached the \
                             integer path"
                                .to_string(),
                        ));
                    } else
                    // Move top-of-stack to R0 for return value (AAPCS). Pop is
                    // reload-aware (#171): a spilled return value is reloaded
                    // from its frame slot first.
                    if !stack.is_empty() {
                        let val = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        if val != Reg::R0 {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Mov {
                                    rd: Reg::R0,
                                    op2: Operand2::Reg(val),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                    }
                    // Deallocate the local frame before popping callee-saved
                    // registers; otherwise the pop would read from the locals
                    // area instead of the saved-register slots.
                    if layout.frame_size > 0 {
                        instructions.push(ArmInstruction {
                            op: ArmOp::Add {
                                rd: Reg::SP,
                                rn: Reg::SP,
                                op2: Operand2::Imm(layout.frame_size),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    // Restore callee-saved registers and return via PC
                    instructions.push(ArmInstruction {
                        op: ArmOp::Pop {
                            regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::PC],
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                Call(func_idx) => {
                    // GI-FPU-002 phase 3 (#369): the callee's float ABI at the
                    // boundary — marshalled below (float args into the VFP
                    // S0../D0.. pools before the BL, a float result out of
                    // S0/D0 after it). All-integer callees take the
                    // byte-identical legacy path (empty layout, both flags
                    // false).
                    let (callee_ret_f32, callee_ret_f64, float_arg_layout) =
                        self.callee_float_signature(*func_idx)?;
                    let has_float_boundary =
                        callee_ret_f32 || callee_ret_f64 || !float_arg_layout.is_empty();
                    if has_float_boundary {
                        // Capability gates: the marshalling itself emits VFP
                        // moves. f32 boundaries need any FPU; an f64 boundary
                        // (D-register argument or D0 result) needs
                        // double-precision — on m4f/m7 the callee's own f64
                        // body declines anyway, so decline the caller
                        // symmetrically instead of emitting UNDEFINED D-ops.
                        let needs_double = callee_ret_f64
                            || float_arg_layout
                                .iter()
                                .any(|(_, r)| vfp_d_index(*r).is_some());
                        if fpu.is_none()
                            || (needs_double && !matches!(fpu, Some(FPUPrecision::Double)))
                        {
                            return Err(synth_core::Error::synthesis(format!(
                                "GI-FPU-002 phase 3: call to func_{func_idx} has {} \
                                 at the AAPCS-VFP boundary but target '{}' {} — \
                                 declining loudly (#369)",
                                if needs_double { "an f64" } else { "an f32" },
                                self.target_name,
                                if fpu.is_none() {
                                    "has no FPU"
                                } else {
                                    "has a single-precision FPU (f32 only)"
                                },
                            )));
                        }
                    }
                    let is_import = *func_idx < self.num_imports;
                    // #197: a relocatable host-link import is a *direct* AAPCS
                    // call (`BL func_N` → wasm field name), so it marshals args
                    // into R0–R3 exactly like a local call. Only the legacy Meld
                    // dispatch ABI (non-relocatable imports) puts the import
                    // index in R0 and takes no AAPCS args.
                    let meld_dispatch = is_import && !self.relocatable;
                    // GI-FPU-002 phase 3 (#369): the legacy Meld dispatch ABI
                    // (import index in R0, no AAPCS args) has no VFP
                    // marshalling — a float-signature import there declines
                    // loudly rather than silently dropping its float args.
                    if meld_dispatch && has_float_boundary {
                        return Err(synth_core::Error::synthesis(format!(
                            "GI-FPU-002 phase 3: import func_{func_idx} has a \
                             float signature but the Meld dispatch import ABI \
                             marshals no AAPCS-VFP registers — declining loudly \
                             (compile with --relocatable for direct AAPCS import \
                             calls, #369)"
                        )));
                    }

                    // ── #195: AAPCS argument count for this callee ──
                    // Look up how many integer args the callee expects so we can
                    // move the top-N operand-stack values into R0–R3. Meld
                    // dispatch imports are excluded: that ABI puts the import
                    // index in R0 (see below), which would collide with arg0.
                    // Direct imports (#197) and local calls marshal normally —
                    // `func_arg_counts` is indexed by the full wasm function
                    // index (imports first), so an import's entry is valid.
                    let arg_count = if meld_dispatch {
                        0
                    } else {
                        self.func_arg_counts
                            .get(*func_idx as usize)
                            .copied()
                            .unwrap_or(0)
                    };

                    // #195: pop the call arguments off the operand stack FIRST so
                    // they are excluded from caller-saved preservation (they are
                    // consumed by the call, not live across it). The actual moves
                    // into R0–R3 are emitted AFTER preservation (below), so they
                    // are the last writes before the BL.
                    // GI-FPU-002 phase 3 (#369): a float-signature callee pops
                    // per-kind — float params via pop_float/pop_double with
                    // their AAPCS-VFP destinations, integer params via the
                    // legacy path (`arg_srcs` then holds the INTEGER params in
                    // integer-position order, which is exactly what the core
                    // R0..R3/NSAA walk consumes since AAPCS-VFP floats occupy
                    // neither). Integer-only callees keep the byte-identical
                    // legacy pop.
                    // #881: under the VFP spill rung, a float argument may
                    // have been spilled to the frame while deeper expression
                    // pressure was relieved — reload every spilled VFP entry
                    // in the argument window so pop_float/pop_double see
                    // register-resident values. Non-argument entries stay
                    // spilled (a frame slot trivially survives the call —
                    // they need no caller-saved preservation).
                    if spill.vfp_spill_on_exhaustion && fpu.is_some() && arg_count > 0 {
                        let n = (arg_count as usize).min(stack.len());
                        let lo = stack.len() - n;
                        vfp_cf_floor = vfp_cf_floor.min(stack.len());
                        for pos in lo..stack.len() {
                            vfp_reload_spilled(
                                pos,
                                &mut stack,
                                vfp_cf_floor,
                                n,
                                &mut vfp_used,
                                &vfp_home,
                                &mut spill,
                                &mut instructions,
                                idx,
                            )?;
                        }
                    }
                    let (arg_srcs, float_args) = if float_arg_layout.is_empty() {
                        (
                            Self::pop_call_args(
                                &mut stack,
                                &mut next_temp,
                                &mut instructions,
                                &mut spill,
                                arg_count,
                                idx,
                            )?,
                            Vec::new(),
                        )
                    } else {
                        let float_dst: std::collections::HashMap<u32, VfpReg> =
                            float_arg_layout.iter().copied().collect();
                        Self::pop_call_args_mixed(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            arg_count,
                            &float_dst,
                            idx,
                        )?
                    };

                    // #359: store args index>=4 to the outgoing stack region
                    // BEFORE preservation and the r0..r3 move (their sources are
                    // already popped, so the move could otherwise clobber them).
                    let n_stack_args = self.emit_stack_args(&mut instructions, &arg_srcs, idx)?;
                    for _ in 0..n_stack_args {
                        cf.add_instruction();
                    }
                    // Only the first <=4 args are marshalled into r0..r3.
                    let reg_srcs = &arg_srcs[..arg_srcs.len().min(ARG_REGS.len())];

                    // ── #188: caller-saved preservation across the call ──
                    // A BL clobbers R0–R3 and R12. Any live value (operand-stack
                    // temp or param) residing in one of those registers and needed
                    // after the call must be spilled before the BL and reloaded
                    // after it. R4–R8 are callee-saved and survive untouched. The
                    // call arguments were already popped, so they are not spilled.
                    let preserved = self.preserve_caller_saved(
                        &mut instructions,
                        &stack_live_regs(&stack),
                        &local_to_reg,
                        &layout,
                        idx,
                    )?;
                    // #719 phase 2: spill every live f32 value (S0..S15 caller-saved)
                    // to the VFP call-spill area before the BL — the VFP analogue of
                    // the #188 integer preservation above. Disjoint register file
                    // and disjoint frame slots, so order vs the integer spill and
                    // the R0..R3 arg move is immaterial.
                    let vfp_preserved = preserve_vfp_caller_saved(
                        &mut instructions,
                        &stack,
                        &vfp_home,
                        &layout,
                        idx,
                    )?;
                    // GI-FPU-002 phase 3 (#369): marshal the float arguments
                    // into their AAPCS-VFP registers — AFTER preservation (so a
                    // live value about to be overwritten in S0../D0.. is already
                    // parked in the frame) and overlap-safe via the two-phase
                    // source-slot staging. The consumed source registers are
                    // freed afterwards (a float RESULT below can then reuse
                    // them); a home register stays pinned by `free_vfp_temp`'s
                    // home guard.
                    Self::emit_vfp_arg_moves(&mut instructions, &float_args, &layout, idx)?;
                    for &(src, _) in &float_args {
                        if vfp_d_index(src).is_some() {
                            free_vfp_dtemp(&mut vfp_used, &vfp_home, src);
                        } else {
                            free_vfp_temp(&mut vfp_used, &vfp_home, src);
                        }
                    }

                    // #195: move arguments into R0–R3 — the LAST thing before the
                    // BL, after live values are safely in the spill area. Skipped
                    // for imports (arg_srcs is empty there). Uses a cycle-safe
                    // parallel move so chains/swaps among R0–R3 are handled.
                    let n_arg_moves = self.emit_arg_moves(
                        &mut instructions,
                        reg_srcs,
                        &stack_live_regs(&stack),
                        &local_to_reg,
                        &layout,
                        &mut spill,
                        idx,
                    )?;
                    for _ in 0..n_arg_moves {
                        cf.add_instruction();
                    }

                    if meld_dispatch {
                        // Legacy import call — dispatch through the Meld runtime
                        // (import index in R0, then BL __meld_dispatch_import).
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mov {
                                rd: Reg::R0,
                                op2: Operand2::Imm(*func_idx as i32),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        instructions.push(ArmInstruction {
                            op: ArmOp::Bl {
                                label: "__meld_dispatch_import".to_string(),
                            },
                            source_line: Some(idx),
                        });
                    } else {
                        // Direct `BL func_N`: a local call, or (#197) a
                        // relocatable import whose `func_N` symbol the ELF
                        // builder rewrites to the wasm field name (e.g.
                        // `k_spin_lock`) for the host linker to resolve.
                        instructions.push(ArmInstruction {
                            op: ArmOp::Bl {
                                label: format!("func_{}", func_idx),
                            },
                            source_line: Some(idx),
                        });
                    }
                    cf.add_instruction();

                    if callee_ret_f32 || callee_ret_f64 {
                        // GI-FPU-002 phase 3 (#369): the float result arrives in
                        // S0/D0. Capture it into a fresh VFP temp BEFORE the
                        // preservation reloads below — if S0/S1 held a live
                        // value before the call, `restore_vfp_caller_saved`
                        // overwrites them with the OLD value, so the result must
                        // move out first. The allocator skips every still-live
                        // register (preserved values stay marked used), and when
                        // S0/D0 itself is free the temp IS S0/D0 and no move is
                        // needed. The copies are the bit-exact core round-trips
                        // the return lowering uses; R0/R1/R12 are dead here (a
                        // float-returning callee leaves no core result, and every
                        // live caller-saved value sits in the spill area until
                        // the reloads below).
                        let result = if callee_ret_f64 {
                            let dd = alloc_vfp_dtemp(&mut vfp_used)?;
                            if dd != VfpReg::D0 {
                                instructions.push(ArmInstruction {
                                    op: ArmOp::I64ReinterpretF64 {
                                        rdlo: Reg::R0,
                                        rdhi: Reg::R1,
                                        dm: VfpReg::D0,
                                    },
                                    source_line: Some(idx),
                                });
                                instructions.push(ArmInstruction {
                                    op: ArmOp::F64ReinterpretI64 {
                                        dd,
                                        rmlo: Reg::R0,
                                        rmhi: Reg::R1,
                                    },
                                    source_line: Some(idx),
                                });
                            }
                            StackVal::Double { dreg: dd }
                        } else {
                            let sd = alloc_vfp_temp(&mut vfp_used)?;
                            if sd != VfpReg::S0 {
                                instructions.push(ArmInstruction {
                                    op: ArmOp::I32ReinterpretF32 {
                                        rd: Reg::R12,
                                        sm: VfpReg::S0,
                                    },
                                    source_line: Some(idx),
                                });
                                instructions.push(ArmInstruction {
                                    op: ArmOp::F32ReinterpretI32 { sd, rm: Reg::R12 },
                                    source_line: Some(idx),
                                });
                            }
                            StackVal::Float { sreg: sd }
                        };
                        // Reload the integer caller-saved values (no R0 result
                        // relocation — the result lives in the VFP file).
                        for &(reg, off) in &preserved {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Ldr {
                                    rd: reg,
                                    addr: MemAddr::imm(Reg::SP, off),
                                },
                                source_line: Some(idx),
                            });
                        }
                        restore_vfp_caller_saved(&mut instructions, &vfp_preserved, idx);
                        stack.push(result);
                    } else {
                        // #311: tag an i64 result as the R0:R1 pair.
                        let ret_i64 = self
                            .func_ret_i64
                            .get(*func_idx as usize)
                            .copied()
                            .unwrap_or(false);
                        let result_reg = self.restore_caller_saved(
                            &mut instructions,
                            &preserved,
                            &stack_live_regs(&stack),
                            &local_to_reg,
                            &layout,
                            &mut spill,
                            ret_i64,
                            idx,
                        )?;
                        // #719 phase 2: reload the f32 S-registers the BL clobbered.
                        // The callee returns in R0 (never S0/D0 on this branch), so
                        // reloading S0..S15 here cannot destroy the integer result.
                        restore_vfp_caller_saved(&mut instructions, &vfp_preserved, idx);
                        // Push the call's return value as a live operand (spilled to
                        // the frame if no register was free to hold it — #171).
                        stack.push(result_reg);
                    }
                }

                CallIndirect {
                    type_index,
                    table_index,
                } => {
                    // #642/#650: WASM Core §4.4.8 requires call_indirect to
                    // TRAP on an out-of-bounds index and on a type mismatch.
                    // The bounds check needs the dispatched table's
                    // compile-time size (the raw code-pointer region has no
                    // runtime size fields); the dispatch needs the table's
                    // constant base offset within the contiguous R11 region
                    // (#650); the type check is discharged HERE at compile
                    // time via the per-table closed-world verdict (every slot
                    // of THAT table verifiably holds a function of the
                    // expected signature — tables cannot change:
                    // table.grow/table.set are unsupported ops that loud-skip
                    // their functions). If any input is missing, DECLINE
                    // loudly — never emit an unchecked indirect branch.
                    // GI-FPU-002 phase 2 (#719/#369): decline loudly when the
                    // static callee type RETURNS f32/f64 (S0/D0 result, not yet
                    // marshalled). f32 ARGS need no type-level check here: every
                    // f32 producer pushes a `Float` operand, which the integer
                    // `pop_call_args` path below already rejects loudly.
                    self.check_indirect_float_signature(*type_index)?;
                    let (table_size, table_byte_offset, null_check, type_check) =
                        self.resolve_call_indirect_guards(*table_index, *type_index)?;

                    // Top of stack is the table index; the call arguments sit
                    // BELOW it on the operand stack.
                    let mut table_idx_reg = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;

                    // #195: callee arg count comes from the static function type.
                    let arg_count = self
                        .type_arg_counts
                        .get(*type_index as usize)
                        .copied()
                        .unwrap_or(0);
                    let arg_srcs = Self::pop_call_args(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        arg_count,
                        idx,
                    )?;

                    // #359: store args index>=4 to the outgoing stack region
                    // BEFORE the table-index relocation (free_callee_saved below
                    // could pick an R4–R8 reg still holding a stack-arg source),
                    // preservation, and the r0..r3 move. The popped arg regs are
                    // not in stack_live_regs, so storing first closes the window.
                    let n_stack_args = self.emit_stack_args(&mut instructions, &arg_srcs, idx)?;
                    for _ in 0..n_stack_args {
                        cf.add_instruction();
                    }
                    let reg_srcs = &arg_srcs[..arg_srcs.len().min(ARG_REGS.len())];

                    // #195: the arg moves write R0–R3, but the `CallIndirect`
                    // expansion reads `table_idx_reg` to compute the branch
                    // target (and clobbers R12). When there are args to marshal,
                    // relocate the table index into a free callee-saved register
                    // so neither the R0–R3 arg writes nor the spill scratch can
                    // clobber it. We keep that register ON the operand stack while
                    // marshalling so every `free_callee_saved` call avoids it,
                    // then pop it back off just before emitting the call.
                    let mut table_pushed = false;
                    if !reg_srcs.is_empty() {
                        let safe = self.free_callee_saved(
                            &stack_live_regs(&stack),
                            &local_to_reg,
                            &layout,
                        )?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mov {
                                rd: safe,
                                op2: Operand2::Reg(table_idx_reg),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        table_idx_reg = safe;
                        stack.push(StackVal::i32(safe));
                        table_pushed = true;
                    }

                    // #188: preserve caller-saved registers across the indirect
                    // call (the table-index reg and the args are already popped
                    // and consumed, so they are excluded from preservation; the
                    // relocated callee-saved table index, if any, is not spilled
                    // because preservation only touches caller-saved regs).
                    let preserved = self.preserve_caller_saved(
                        &mut instructions,
                        &stack_live_regs(&stack),
                        &local_to_reg,
                        &layout,
                        idx,
                    )?;
                    // #719 phase 2: spill live f32 values across the indirect call
                    // (S0..S15 caller-saved). The relocated table index on `stack`
                    // is an integer, invisible to `vfp_live_set`.
                    let vfp_preserved = preserve_vfp_caller_saved(
                        &mut instructions,
                        &stack,
                        &vfp_home,
                        &layout,
                        idx,
                    )?;

                    // #195: marshal args into R0–R3 (after preservation, last
                    // writes before the indirect branch). The relocated table
                    // index on the stack keeps the scratch picker away from it.
                    let n_arg_moves = self.emit_arg_moves(
                        &mut instructions,
                        reg_srcs,
                        &stack_live_regs(&stack),
                        &local_to_reg,
                        &layout,
                        &mut spill,
                        idx,
                    )?;
                    for _ in 0..n_arg_moves {
                        cf.add_instruction();
                    }

                    // Pop the relocated table index back off before the call op.
                    if table_pushed {
                        stack.pop();
                    }

                    if self.self_contained_funcref_table {
                        // #275: SELF-CONTAINED image — dispatch through the
                        // flash-resident funcref table (`FUNC_TABLE_SYMBOL`),
                        // reached PC-relative via an `LdrSym` literal-pool
                        // pointer the image builder patches post-layout.
                        // NEVER via R11 (linear-memory base — the #717
                        // collision), R9/R10 (globals / mem-size), or R12
                        // (encoder scratch). Same §4.4.8 guard semantics as
                        // the R11 expansion: OOB index → UDF, #676 type
                        // mismatch → UDF, #664 null slot → UDF.
                        let n = self.emit_self_contained_call_indirect(
                            &mut instructions,
                            table_idx_reg,
                            &stack_live_regs(&stack),
                            &local_to_reg,
                            &layout,
                            table_size,
                            table_byte_offset,
                            null_check,
                            type_check,
                            idx,
                        )?;
                        for _ in 0..n {
                            cf.add_instruction();
                        }
                    } else {
                        instructions.push(ArmInstruction {
                            op: ArmOp::CallIndirect {
                                rd: Reg::R0,
                                type_idx: *type_index,
                                table_index_reg: table_idx_reg,
                                // #642: the encoder emits `CMP idx, size; BLO ok;
                                // UDF #0` before the table load. #650: a non-zero
                                // offset routes the load through the table's base
                                // within the contiguous R11 region. #664: a table
                                // with null slots gets a runtime null check on
                                // the loaded pointer (zero-linked slot → trap).
                                // #676: a heterogeneous table gets the runtime
                                // type check against the type-id sidecar.
                                table_size,
                                table_byte_offset,
                                null_check,
                                type_check,
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    // #311: tag an i64 result as the R0:R1 pair (static type).
                    let ret_i64 = self
                        .type_ret_i64
                        .get(*type_index as usize)
                        .copied()
                        .unwrap_or(false);
                    let result_reg = self.restore_caller_saved(
                        &mut instructions,
                        &preserved,
                        &stack_live_regs(&stack),
                        &local_to_reg,
                        &layout,
                        &mut spill,
                        ret_i64,
                        idx,
                    )?;
                    // #719 phase 2: reload the f32 S-registers the indirect call
                    // clobbered.
                    restore_vfp_caller_saved(&mut instructions, &vfp_preserved, idx);
                    stack.push(result_reg);
                }

                Unreachable => {
                    instructions.push(ArmInstruction {
                        op: ArmOp::Udf { imm: 0 },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                Nop => {
                    instructions.push(ArmInstruction {
                        op: ArmOp::Nop,
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                Drop => {
                    // Just pop a value from the stack and discard it.
                    // #881 (rung-only, byte-invisible otherwise): a dropped
                    // VFP value releases its register / spill slot so deep
                    // drop-heavy shapes don't leak the finite S-file/pool.
                    match stack.pop() {
                        Some(StackVal::Float { sreg }) if spill.vfp_spill_on_exhaustion => {
                            free_vfp_temp(&mut vfp_used, &vfp_home, sreg);
                        }
                        Some(StackVal::Double { dreg }) if spill.vfp_spill_on_exhaustion => {
                            free_vfp_dtemp(&mut vfp_used, &vfp_home, dreg);
                        }
                        Some(
                            StackVal::FloatSpilled { slot } | StackVal::DoubleSpilled { slot },
                        ) => {
                            spill.free(slot);
                        }
                        _ => {}
                    }
                }

                Select => {
                    // Select: pop condition, val2, val1; push val1 if cond != 0, else val2
                    let cond_reg = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    // GI-FPU-002 (#782): FLOAT select — both value operands
                    // live in the VFP register file (`select` over f32/f64 is
                    // the clamp idiom `(x>k)?k:x` falcon emits throughout its
                    // stabilization math). The integer pop below loud-declines
                    // on a Float/Double entry, so route the float shapes
                    // through a VFP-aware lowering FIRST: move both operands'
                    // bit patterns into core registers (VMOV — bit-exact, no
                    // conversion), run the SAME flag-safe CMP + IT;MOV select
                    // on the patterns, and move the winner back into a fresh
                    // VFP register. NaN-safe by construction: `select` picks a
                    // value, never computes one, and the round-trip preserves
                    // the exact bits. Only reachable when an operand is
                    // VFP-resident (fpu-gated paths pushed it), so integer
                    // modules are byte-identical.
                    let top2_f32 = stack.len() >= 2
                        && matches!(stack[stack.len() - 1], StackVal::Float { .. })
                        && matches!(stack[stack.len() - 2], StackVal::Float { .. });
                    let top2_f64 = stack.len() >= 2
                        && matches!(stack[stack.len() - 1], StackVal::Double { .. })
                        && matches!(stack[stack.len() - 2], StackVal::Double { .. });
                    if top2_f32 {
                        let s2 = pop_float(&mut stack)?; // val2 (cond == 0)
                        let s1 = pop_float(&mut stack)?; // val1 (cond != 0)
                        // `cond_reg` is off the vstack but must survive until
                        // the CMP — reserve it (and the first pattern temp)
                        // through the core-register allocations.
                        let mut resv = live_params.clone();
                        resv.push(cond_reg);
                        let ra = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &resv,
                            idx,
                        )?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::I32ReinterpretF32 { rd: ra, sm: s1 },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        resv.push(ra);
                        let rb = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &resv,
                            idx,
                        )?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::I32ReinterpretF32 { rd: rb, sm: s2 },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        // CMP first, then the single flag-preserving IT;MOV —
                        // `rb` already holds val2's pattern (the EQ result), so
                        // only the NE override is needed (in-place form). Both
                        // come from the Rocq-proved in-place select rule
                        // (increment 5, RQ-58-SELDSL).
                        for rule_op in
                            crate::sel_dsl::generated::rule_i32_select_inplace(rb, cond_reg, ra)
                        {
                            instructions.push(ArmInstruction {
                                op: rule_op,
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        // Free the two consumed S-registers (home-aware), then
                        // home the selected pattern in a fresh S-register.
                        free_vfp_temp(&mut vfp_used, &vfp_home, s1);
                        free_vfp_temp(&mut vfp_used, &vfp_home, s2);
                        let sd = alloc_vfp_temp(&mut vfp_used)?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::F32ReinterpretI32 { sd, rm: rb },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        stack.push(StackVal::Float { sreg: sd });
                        continue;
                    }
                    if top2_f64 {
                        // Same bit-pattern select, one register PAIR per f64
                        // (I64ReinterpretF64/F64ReinterpretI64 are the shipped
                        // core round-trip — no D→D move in the ArmOp set).
                        let d2 = pop_double(&mut stack)?; // val2 (cond == 0)
                        let d1 = pop_double(&mut stack)?; // val1 (cond != 0)
                        let mut resv = live_params.clone();
                        resv.push(cond_reg);
                        let (alo, ahi) = alloc_consecutive_pair(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &[],
                            &resv,
                            idx,
                        )?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::I64ReinterpretF64 {
                                rdlo: alo,
                                rdhi: ahi,
                                dm: d1,
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        resv.push(alo);
                        resv.push(ahi);
                        let (blo, bhi) = alloc_consecutive_pair(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &[],
                            &resv,
                            idx,
                        )?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::I64ReinterpretF64 {
                                rdlo: blo,
                                rdhi: bhi,
                                dm: d2,
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        // CMP + two flag-preserving IT;MOVs (the b pair holds
                        // val2's pattern, only the NE override is needed) —
                        // from the Rocq-proved in-place i64-pair select rule
                        // (increment 5, RQ-58-SELDSL), pair side conditions
                        // Ok-or-Err.
                        let rule_ops = crate::sel_dsl::generated::rule_i64_select_inplace(
                            blo, bhi, alo, ahi, cond_reg,
                        )
                        .map_err(synth_core::Error::synthesis)?;
                        for rule_op in rule_ops {
                            instructions.push(ArmInstruction {
                                op: rule_op,
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        free_vfp_dtemp(&mut vfp_used, &vfp_home, d1);
                        free_vfp_dtemp(&mut vfp_used, &vfp_home, d2);
                        let dd = alloc_vfp_dtemp(&mut vfp_used)?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::F64ReinterpretI64 {
                                dd,
                                rmlo: blo,
                                rmhi: bhi,
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        stack.push(StackVal::Double { dreg: dd });
                        continue;
                    }
                    // #782(b): WIDE (i64) select — BOTH halves must be picked.
                    // The narrow path below moves only the lo register and
                    // pushed the result as i32, silently keeping the WRONG hi
                    // half whenever cond == 0 (found adversarially while
                    // clearing the float-select class; also covers a soft-float
                    // f64 select, which rides the i64-pair treatment). Width is
                    // read BEFORE the pops (pop_operand returns only the lo).
                    let v2_wide = stack.last().is_some_and(|v| v.is_i64());
                    let v1_wide = stack.len() >= 2 && stack[stack.len() - 2].is_i64();
                    if v2_wide || v1_wide {
                        if v2_wide != v1_wide {
                            return Err(synth_core::Error::synthesis(
                                "select value operands disagree on width \
                                 (i32 vs i64) — invalid wasm"
                                    .to_string(),
                            ));
                        }
                        // Destination pair FIRST, while both values are still
                        // stack-live (the allocator cannot hand out their
                        // registers; a pressure spill of them reloads on pop).
                        let mut resv = live_params.clone();
                        resv.push(cond_reg);
                        let (dlo, dhi) = alloc_consecutive_pair(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &[],
                            &resv,
                            idx,
                        )?;
                        // Reserve the dst pair through the (possibly reloading)
                        // pops so a spilled operand cannot reload into it.
                        // #973: `val2`'s PAIR joins the reservation for the
                        // second pop for the same reason — it is off the vstack
                        // but still read by the two EQ moves below. (This path
                        // measured GREEN on the #973 fixture pre-fix; the
                        // omission is the identical latent shape, closed here
                        // rather than left for the next pressure change to
                        // expose.)
                        let mut committed = vec![cond_reg, dlo, dhi];
                        let val2 = pop_operand_committed(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            &committed,
                            idx,
                        )?;
                        let hi2 = i64_pair_hi(val2)?;
                        committed.push(val2);
                        committed.push(hi2);
                        let val1 = pop_operand_committed(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            &committed,
                            idx,
                        )?;
                        let hi1 = i64_pair_hi(val1)?;
                        // CMP + four flag-preserving IT;MOVs — from the
                        // Rocq-proved i64-pair select rule (increment 5,
                        // RQ-58-SELDSL). The pair aliasing constraints the
                        // old comment argued by construction are the rule's
                        // machine-checked side conditions, Ok-or-Err.
                        let rule_ops = crate::sel_dsl::generated::rule_i64_select(
                            dlo, dhi, val1, hi1, val2, hi2, cond_reg,
                        )
                        .map_err(synth_core::Error::synthesis)?;
                        for rule_op in rule_ops {
                            instructions.push(ArmInstruction {
                                op: rule_op,
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        stack.push(StackVal::i64(dlo));
                        continue;
                    }
                    // #973: both pops may RELOAD a spilled operand, and the
                    // allocator only avoids what is still on the vstack plus
                    // what it is told. `cond_reg` came off the vstack above but
                    // is not read until the CMP below; `val2` is not read until
                    // the EQ move. Commit both so a reload cannot land on them —
                    // the i64-comparison condition spills the then-arm every
                    // time (`alloc_consecutive_pair` frees a pair by spilling
                    // the deepest entry), and the reload used to pick the
                    // else-arm's register.
                    let val2 = pop_operand_committed(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        &[cond_reg],
                        idx,
                    )?;
                    let val1 = pop_operand_committed(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        &[cond_reg, val2],
                        idx,
                    )?;
                    // #209/VCR-SEL-002 — in-place select. `val2` is consumed by
                    // this op, so when it is a free temp (not a live param reg,
                    // and distinct from cond/val1) we reuse ITS register as `dst`
                    // and keep its value via the EQ fall-through — only ONE
                    // conditional move is needed (cond != 0 overrides with val1).
                    // This is exactly what native emits for a clamp `(x>k)?k:x`
                    // and removes one `SelectMove` per select, the dominant cost
                    // in flat_flight's saturation chain. The three guards rule out
                    // the cases where overwriting val2's register is observable:
                    //   - live param  → #193 param-clobber class
                    //   - val2==cond  → cmp consumed cond, but a later read can't
                    //   - val2==val1  → degenerate; fresh dst keeps it simple
                    // Falls back to the fresh-dst two-move form otherwise.
                    let in_place = !live_params.contains(&val2) && val2 != cond_reg && val2 != val1;
                    let dst = if in_place {
                        val2
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };

                    // CMP cond, #0 — sets the flags FIRST, before anything writes
                    // `dst`. The previous lowering put a `MOV dst, val1` between
                    // the CMP and the conditional move; that MOV is a 16-bit Thumb
                    // `MOVS` for low registers and SETS the flags, clobbering the
                    // comparison whenever the allocator picked a low `dst` — which
                    // mis-computed gale's br_table index so the binary-semaphore
                    // WAKE path never ran. The `SelectMove`s below are `IT;MOV`
                    // (the flag-preserving 0x46xx MOV), so neither disturbs the
                    // flags and exactly one fires — correct under any aliasing of
                    // dst with cond/val1/val2 (cond is already consumed by CMP).
                    // In the in-place case there is NO instruction between the CMP
                    // and the conditional move, so the flags are likewise intact.
                    // Emission from the Rocq-proved select rules (increment
                    // 5, RQ-58-SELDSL): the in-place/fresh-dst choice above
                    // stays selector-owned as dispatch between the two proven
                    // forms — the in-place theorem pins the EQ fall-through
                    // (dst keeps val2) that the elision relies on.
                    let rule_ops = if in_place {
                        crate::sel_dsl::generated::rule_i32_select_inplace(dst, cond_reg, val1)
                    } else {
                        crate::sel_dsl::generated::rule_i32_select(dst, cond_reg, val1, val2)
                    };
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    stack.push(StackVal::i32(dst));
                }

                LocalSet(local_idx) => {
                    let val = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    if let Some(&(off, is_wide)) = layout.incoming_params.get(local_idx) {
                        // #359/#503: write to the incoming stack-passed param's
                        // slot in the caller's frame (wide: both halves, I64Str).
                        let op = if is_wide {
                            ArmOp::I64Str {
                                rdlo: val,
                                rdhi: i64_pair_hi(val)?,
                                addr: MemAddr::imm(Reg::SP, off),
                            }
                        } else {
                            ArmOp::Str {
                                rd: val,
                                addr: MemAddr::imm(Reg::SP, off),
                            }
                        };
                        instructions.push(ArmInstruction {
                            op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else if let Some(&(off, is_i64)) = layout.param_slots.get(local_idx) {
                        // #204/#193: frame-backed param — store to its slot.
                        let op = if is_i64 {
                            ArmOp::I64Str {
                                rdlo: val,
                                rdhi: i64_pair_hi(val)?,
                                addr: MemAddr::imm(Reg::SP, off),
                            }
                        } else {
                            ArmOp::Str {
                                rd: val,
                                addr: MemAddr::imm(Reg::SP, off),
                            }
                        };
                        instructions.push(ArmInstruction {
                            op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else if *local_idx < num_params.min(4) {
                        let target = index_to_reg(*local_idx as u8);
                        if val != target {
                            // #989: an EARLIER `local.get` of this same param
                            // pushed `target` by reference — copy any such
                            // still-live stack entry out before the overwrite
                            // destroys it (the get→set→use WAR hazard).
                            let mut rsv = live_params.clone();
                            rsv.push(val);
                            snapshot_home_reg_aliases(
                                target,
                                None,
                                &mut stack,
                                &mut next_temp,
                                &mut instructions,
                                &mut spill,
                                &rsv,
                                idx,
                            )?;
                            instructions.push(ArmInstruction {
                                op: ArmOp::Mov {
                                    rd: target,
                                    op2: Operand2::Reg(val),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        local_to_reg.insert(*local_idx, target);
                    } else if let Some(&target) = promoted.get(local_idx) {
                        // VCR-RA local promotion (#390, #242): store into the
                        // promoted callee-saved register (r4..r8) instead of a frame
                        // slot. The register is reserved from temp/pair/reload
                        // allocation (seeded into local_to_reg → param_last_read), so
                        // `val` is never the target itself; the `val != target` guard
                        // only elides a redundant self-move. Checked before
                        // `layout.locals` so the dead frame slot is never written.
                        if val != target {
                            // #989: same WAR snapshot as the param arm —
                            // `local.get` of a promoted local aliases r4..r8
                            // by reference.
                            let mut rsv = live_params.clone();
                            rsv.push(val);
                            snapshot_home_reg_aliases(
                                target,
                                None,
                                &mut stack,
                                &mut next_temp,
                                &mut instructions,
                                &mut spill,
                                &rsv,
                                idx,
                            )?;
                            instructions.push(ArmInstruction {
                                op: ArmOp::Mov {
                                    rd: target,
                                    op2: Operand2::Reg(val),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                    } else if let Some(&(off, true)) = layout.locals.get(local_idx) {
                        // i64 spilled local: store BOTH 32-bit halves
                        // (lower at offset N, upper at N+4) via the I64Str
                        // pseudo-op. Without this we drop the upper half.
                        let val_hi = i64_pair_hi(val)?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::I64Str {
                                rdlo: val,
                                rdhi: val_hi,
                                addr: MemAddr::imm(Reg::SP, off),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else if let Some(&(off, false)) = layout.locals.get(local_idx) {
                        // i32 spilled local: single 4-byte store.
                        instructions.push(ArmInstruction {
                            op: ArmOp::Str {
                                rd: val,
                                addr: MemAddr::imm(Reg::SP, off),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else {
                        // #378 honesty: refuse to guess a frame offset for a local
                        // absent from the layout — fail loud (loud-skip) rather than
                        // silently store to a guessed address. See LocalGet above.
                        return Err(synth_core::Error::synthesis(format!(
                            "local.set {local_idx} (op {idx}) is absent from the \
                             computed frame layout — refusing to guess a stack \
                             offset (would silently miscompile)"
                        )));
                    }
                }

                LocalTee(local_idx) => {
                    // Like local.set but keeps value on stack. Peek is
                    // reload-aware (#171): a spilled TOS is reloaded in place.
                    let val = peek_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    if let Some(&(off, is_wide)) = layout.incoming_params.get(local_idx) {
                        // #359/#503: write to the incoming stack-passed param's
                        // slot (wide: both halves, I64Str); value stays on the
                        // operand stack (peek kept it).
                        let op = if is_wide {
                            ArmOp::I64Str {
                                rdlo: val,
                                rdhi: i64_pair_hi(val)?,
                                addr: MemAddr::imm(Reg::SP, off),
                            }
                        } else {
                            ArmOp::Str {
                                rd: val,
                                addr: MemAddr::imm(Reg::SP, off),
                            }
                        };
                        instructions.push(ArmInstruction {
                            op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else if let Some(&(off, is_i64)) = layout.param_slots.get(local_idx) {
                        // #204/#193: frame-backed param — store to its slot; value
                        // stays on the operand stack (peek kept it).
                        let op = if is_i64 {
                            ArmOp::I64Str {
                                rdlo: val,
                                rdhi: i64_pair_hi(val)?,
                                addr: MemAddr::imm(Reg::SP, off),
                            }
                        } else {
                            ArmOp::Str {
                                rd: val,
                                addr: MemAddr::imm(Reg::SP, off),
                            }
                        };
                        instructions.push(ArmInstruction {
                            op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else if *local_idx < num_params.min(4) {
                        let target = index_to_reg(*local_idx as u8);
                        if val != target {
                            // #989: snapshot earlier `local.get` aliases of this
                            // param's home register before overwriting it. The
                            // tee's own kept top is SKIPPED — it is the value
                            // being written and stays aliased to its producer.
                            let mut rsv = live_params.clone();
                            rsv.push(val);
                            let top_idx = stack.len() - 1;
                            snapshot_home_reg_aliases(
                                target,
                                Some(top_idx),
                                &mut stack,
                                &mut next_temp,
                                &mut instructions,
                                &mut spill,
                                &rsv,
                                idx,
                            )?;
                            instructions.push(ArmInstruction {
                                op: ArmOp::Mov {
                                    rd: target,
                                    op2: Operand2::Reg(val),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        local_to_reg.insert(*local_idx, target);
                    } else if let Some(&target) = promoted.get(local_idx) {
                        // VCR-RA local promotion (#390, #242): copy into the promoted
                        // callee-saved register; the value STAYS on the operand stack
                        // (peek kept it), so a later consumer of the tee'd value and a
                        // later `local.get` both see the same value from independent
                        // homes. Reserved like LocalSet, so `val != target`.
                        if val != target {
                            // #989: same WAR snapshot as the param arm, top
                            // skipped (tee semantics).
                            let mut rsv = live_params.clone();
                            rsv.push(val);
                            let top_idx = stack.len() - 1;
                            snapshot_home_reg_aliases(
                                target,
                                Some(top_idx),
                                &mut stack,
                                &mut next_temp,
                                &mut instructions,
                                &mut spill,
                                &rsv,
                                idx,
                            )?;
                            instructions.push(ArmInstruction {
                                op: ArmOp::Mov {
                                    rd: target,
                                    op2: Operand2::Reg(val),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                    } else if let Some(&(off, true)) = layout.locals.get(local_idx) {
                        // i64 spilled local: store both halves like LocalSet.
                        let val_hi = i64_pair_hi(val)?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::I64Str {
                                rdlo: val,
                                rdhi: val_hi,
                                addr: MemAddr::imm(Reg::SP, off),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else if let Some(&(off, false)) = layout.locals.get(local_idx) {
                        instructions.push(ArmInstruction {
                            op: ArmOp::Str {
                                rd: val,
                                addr: MemAddr::imm(Reg::SP, off),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else {
                        // #378 honesty: refuse to guess a frame offset for a local
                        // absent from the layout — fail loud (loud-skip) rather than
                        // silently store to a guessed address. See LocalGet above.
                        return Err(synth_core::Error::synthesis(format!(
                            "local.tee {local_idx} (op {idx}) is absent from the \
                             computed frame layout — refusing to guess a stack \
                             offset (would silently miscompile)"
                        )));
                    }
                }

                GlobalGet(global_idx) => {
                    // #643: type-aware slot addressing. The offset is the SUM
                    // of earlier globals' widths (an i64/f64 slot is 8 bytes),
                    // NOT `idx * 4` — and an i64 global's value is a register
                    // PAIR loaded from `[R9, off]` / `[R9, off+4]`. The old
                    // single-word `idx * 4` lowering silently dropped the high
                    // word of every i64 global.
                    let slot_off = self.global_slot_offset(*global_idx);
                    let slot_width = self.global_slot_width(*global_idx);
                    if slot_width > 8 {
                        return Err(synth_core::Error::synthesis(format!(
                            "global.get {global_idx} (op {idx}) reads a \
                             {slot_width}-byte (v128) global — no lowering; \
                             refusing to truncate (#643)"
                        )));
                    }
                    // #237 (gale, mutex-on-silicon): under the native-pointer ABI,
                    // globals live in MATERIALIZED slots (`__synth_globals + idx*4`,
                    // emitted into the object's .data with their wasm init values)
                    // — mutable state that survives global.set, unlike the earlier
                    // constant promotion whose paired dropped-store miscompiled any
                    // multi-function module that moves the shadow-stack pointer.
                    // Slots hold wasm OFFSETS (no data relocation needed); the SP
                    // global is rebased to an absolute pointer on read so address
                    // arithmetic and [r11=0 + addr] accesses see host pointers.
                    if self.native_pointer_abi {
                        // #643: the materialized `__synth_globals` region is a
                        // 4-byte-slot layout (i32 inits, `idx * 4` addressing,
                        // emitted by the CLI). A wide global — or a 4-byte
                        // global whose offset an earlier wide global shifted —
                        // has no consistent slot there; decline loudly (the
                        // CLI refuses such modules before codegen; this guards
                        // direct `select_with_stack` drivers).
                        if slot_width != 4 || slot_off != (*global_idx as i32) * 4 {
                            return Err(synth_core::Error::synthesis(format!(
                                "global.get {global_idx} (op {idx}): i64/f64 \
                                 globals are unsupported under the native-pointer \
                                 ABI's 4-byte `__synth_globals` slot layout — \
                                 refusing to truncate (#643)"
                            )));
                        }
                        let dst = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        Self::emit_sym_addr(
                            &mut instructions,
                            dst,
                            "__synth_globals",
                            (*global_idx as i32) * 4,
                            idx,
                        );
                        instructions.push(ArmInstruction {
                            op: ArmOp::Ldr {
                                rd: dst,
                                addr: MemAddr::imm(dst, 0),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        stack.push(StackVal::i32(dst));
                        if let Some((sp_idx, _)) = self.sp_global
                            && *global_idx == sp_idx
                        {
                            // dst is on the operand stack now, so the base temp
                            // cannot alias it.
                            let base = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &live_params,
                                idx,
                            )?;
                            Self::emit_wasm_data_addr(&mut instructions, base, 0, idx);
                            instructions.push(ArmInstruction {
                                op: ArmOp::Add {
                                    rd: dst,
                                    rn: dst,
                                    op2: Operand2::Reg(base),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        continue;
                    }
                    // #643: an i64/f64 global is a register PAIR — load both
                    // words from its 8-byte slot. The pair MUST be consecutive
                    // in ALLOCATABLE_REGS (i64_pair_hi recovers the high reg
                    // downstream, exactly like I64Load).
                    if slot_width == 8 {
                        let (dst_lo, dst_hi) = alloc_consecutive_pair(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &[],
                            &live_params,
                            idx,
                        )?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::Ldr {
                                rd: dst_lo,
                                addr: MemAddr::imm(Reg::R9, slot_off),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        instructions.push(ArmInstruction {
                            op: ArmOp::Ldr {
                                rd: dst_hi,
                                addr: MemAddr::imm(Reg::R9, slot_off + 4),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        stack.push(StackVal::i64(dst_lo));
                        continue;
                    }
                    // Load global value from globals table (R9 = globals base).
                    // i32/f32 globals occupy one 4-byte slot at `slot_off`.
                    let dst = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    instructions.push(ArmInstruction {
                        op: ArmOp::Ldr {
                            rd: dst,
                            addr: MemAddr::imm(Reg::R9, slot_off),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i32(dst));
                }

                GlobalSet(global_idx) => {
                    // #643: type-aware slot addressing (see GlobalGet above) —
                    // an i64/f64 global's value is a register PAIR stored to
                    // `[R9, off]` / `[R9, off+4]`. The old single-word store
                    // silently discarded the already-materialized high word.
                    let slot_off = self.global_slot_offset(*global_idx);
                    let slot_width = self.global_slot_width(*global_idx);
                    if slot_width > 8 {
                        return Err(synth_core::Error::synthesis(format!(
                            "global.set {global_idx} (op {idx}) writes a \
                             {slot_width}-byte (v128) global — no lowering; \
                             refusing to truncate (#643)"
                        )));
                    }
                    if slot_width == 8 {
                        if self.native_pointer_abi {
                            // 4-byte `__synth_globals` slot layout — see the
                            // GlobalGet decline above.
                            return Err(synth_core::Error::synthesis(format!(
                                "global.set {global_idx} (op {idx}): i64/f64 \
                                 globals are unsupported under the native-pointer \
                                 ABI's 4-byte `__synth_globals` slot layout — \
                                 refusing to drop the high word (#643)"
                            )));
                        }
                        // The operand-stack top must actually BE a pair — a
                        // width mismatch (invalid wasm / a producer we failed
                        // to tag) would make i64_pair_hi fabricate a high reg.
                        if !stack.last().map(StackVal::is_i64).unwrap_or(false) {
                            return Err(synth_core::Error::synthesis(format!(
                                "global.set {global_idx} (op {idx}) writes an \
                                 8-byte global but the operand-stack top is not \
                                 an i64 pair — refusing to fabricate a high \
                                 word (#643)"
                            )));
                        }
                        let val_lo = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        let val_hi = i64_pair_hi(val_lo)?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::Str {
                                rd: val_lo,
                                addr: MemAddr::imm(Reg::R9, slot_off),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        instructions.push(ArmInstruction {
                            op: ArmOp::Str {
                                rd: val_hi,
                                addr: MemAddr::imm(Reg::R9, slot_off + 4),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        continue;
                    }
                    // Pop value from stack and store to globals table (R9 = globals base).
                    let val = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    // #237 (gale, mutex-on-silicon): under the native-pointer ABI
                    // the store is REAL — write the value into the global's
                    // materialized slot. The earlier "dropped store" leaf
                    // assumption miscompiled multi-function modules whose callees
                    // re-read the moved shadow-stack pointer. The SP global's
                    // absolute pointer is rebased back to a wasm offset before the
                    // store (slots hold offsets; no data relocation needed).
                    if self.native_pointer_abi {
                        // #643: a 4-byte global whose offset an earlier wide
                        // global shifted has no consistent slot in the CLI's
                        // `idx * 4` `__synth_globals` layout — decline loudly
                        // (mirrors the GlobalGet guard above).
                        if slot_off != (*global_idx as i32) * 4 {
                            return Err(synth_core::Error::synthesis(format!(
                                "global.set {global_idx} (op {idx}): the module \
                                 mixes i64/f64 globals into the native-pointer \
                                 ABI's 4-byte `__synth_globals` slot layout — \
                                 refusing an inconsistent offset (#643)"
                            )));
                        }
                        let mut reserved = live_params.clone();
                        reserved.push(val);
                        let stored = if let Some((sp_idx, _)) = self.sp_global
                            && *global_idx == sp_idx
                        {
                            let base = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &reserved,
                                idx,
                            )?;
                            Self::emit_wasm_data_addr(&mut instructions, base, 0, idx);
                            instructions.push(ArmInstruction {
                                op: ArmOp::Sub {
                                    rd: base,
                                    rn: val,
                                    op2: Operand2::Reg(base),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                            base
                        } else {
                            val
                        };
                        reserved.push(stored);
                        let slot = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &reserved,
                            idx,
                        )?;
                        Self::emit_sym_addr(
                            &mut instructions,
                            slot,
                            "__synth_globals",
                            (*global_idx as i32) * 4,
                            idx,
                        );
                        instructions.push(ArmInstruction {
                            op: ArmOp::Str {
                                rd: stored,
                                addr: MemAddr::imm(slot, 0),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        continue;
                    }
                    instructions.push(ArmInstruction {
                        op: ArmOp::Str {
                            rd: val,
                            addr: MemAddr::imm(Reg::R9, slot_off),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                // =========================================================
                // i64 operations with proper stack tracking
                // =========================================================
                // Convention: i64 values occupy a register pair (lo, hi).
                // Only the lo register is pushed onto the virtual stack.
                // The hi register is derived as the next consecutive
                // register via i64_pair_hi(lo).
                // Pairs are allocated as two consecutive temp registers.
                // =========================================================
                I64Const(val) => {
                    // Allocate a CONSECUTIVE register pair for the 64-bit
                    // constant. Two separate alloc_temp_safe calls can return
                    // non-consecutive registers if something in between is
                    // live on the wasm stack, which then breaks the
                    // i64_pair_hi convention used by every i64 op downstream.
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[],
                        &live_params,
                        idx,
                    )?;

                    // The I64Const pseudo comes from the Rocq-proved rule —
                    // the only path (increment 6, RQ-59-SUBTRACT). Carries
                    // the rd_hi <> rd_lo side condition Ok-or-Err; the
                    // consecutive pair satisfies it by construction.
                    let rule_ops = crate::sel_dsl::generated::rule_i64_const(dst_lo, dst_hi, *val)
                        .map_err(synth_core::Error::synthesis)?;
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    // Push only the lo register; hi is derived via i64_pair_hi
                    stack.push(StackVal::i64(dst_lo));
                }

                I64Add => {
                    // Pop two i64 register pairs: b (top), a (second)
                    let b_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let b_hi = i64_pair_hi(b_lo)?;
                    let a_hi = i64_pair_hi(a_lo)?;

                    // Allocate result register pair. MUST be consecutive
                    // in ALLOCATABLE_REGS — i64_pair_hi assumes consecutive
                    // and is called by every i64 op downstream to recover
                    // the high register. Two separate alloc_temp_safe calls
                    // skip live registers and produce non-consecutive pairs.
                    // Avoid clobbering the just-popped operand pairs before
                    // the ADC reads them — passing them in extra_avoid
                    // ensures dst doesn't overlap any of a_lo/a_hi/b_lo/b_hi.
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[a_lo, a_hi, b_lo, b_hi],
                        &live_params,
                        idx,
                    )?;

                    // The ADDS+ADC pair comes from the generated Rocq-proved
                    // rule — the only path (RQ-58-RETIRE). The pair aliasing
                    // side conditions hold by construction here:
                    // alloc_consecutive_pair avoids every operand half and a
                    // consecutive pair never self-aliases.
                    let rule_ops = crate::sel_dsl::generated::rule_i64_add(
                        dst_lo, dst_hi, a_lo, a_hi, b_lo, b_hi,
                    )
                    .map_err(synth_core::Error::synthesis)?;
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }

                    stack.push(StackVal::i64(dst_lo));
                }

                I64Sub => {
                    // Pop two i64 register pairs: b (top), a (second)
                    let b_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let b_hi = i64_pair_hi(b_lo)?;
                    let a_hi = i64_pair_hi(a_lo)?;

                    // See I64Add for why extra_avoid carries a_*/b_* —
                    // dst must not overlap any operand half before SBC reads it.
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[a_lo, a_hi, b_lo, b_hi],
                        &live_params,
                        idx,
                    )?;

                    // Same as I64Add — the Rocq-proved SUBS+SBC pair rule is
                    // the only path (RQ-58-RETIRE).
                    let rule_ops = crate::sel_dsl::generated::rule_i64_sub(
                        dst_lo, dst_hi, a_lo, a_hi, b_lo, b_hi,
                    )
                    .map_err(synth_core::Error::synthesis)?;
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }

                    stack.push(StackVal::i64(dst_lo));
                }

                // ============================================================
                // i64 bitwise ops (I64Or / I64And / I64Xor)
                //
                // Each pops two i64 register pairs from the wasm stack and
                // emits two ARM ops (low-half then high-half) into a freshly
                // allocated consecutive pair. This replaces the wildcard
                // fallthrough to select_default, which assumed inputs in
                // R0:R1 and R2:R3 — incorrect when the wasm stack tracks
                // arbitrary register pairs from earlier ops.
                // ============================================================
                I64Or | I64And | I64Xor => {
                    let b_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let b_hi = i64_pair_hi(b_lo)?;
                    let a_hi = i64_pair_hi(a_lo)?;
                    // dst must not overlap any popped operand's half — the
                    // hi instruction reads a_hi and b_hi after the lo
                    // instruction writes dst_lo.
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[a_lo, a_hi, b_lo, b_hi],
                        &live_params,
                        idx,
                    )?;
                    // The per-half bitwise pair comes from the generated
                    // Rocq-proved rule — the only path (RQ-58-RETIRE; side
                    // conditions hold by construction, see I64Add).
                    let rule_ops =
                        crate::sel_dsl::i64_pair_rule(op, dst_lo, dst_hi, a_lo, a_hi, b_lo, b_hi)
                            .expect("i64 bitwise op has a pair rule")
                            .map_err(synth_core::Error::synthesis)?;
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    stack.push(StackVal::i64(dst_lo));
                }

                // ============================================================
                // i32 -> i64 extension (I64ExtendI32U / I64ExtendI32S)
                //
                // Pops one i32, allocates a consecutive i64 pair, places the
                // i32 in the low half. For unsigned: high = 0. For signed:
                // high = arithmetic-shift-right by 31 (sign-extension).
                // ============================================================
                I64ExtendI32U => {
                    let val = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    // val must stay alive until the Mov reads it; dst_hi
                    // must not be val (we'd write the zero high before
                    // moving val to dst_lo).
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[val],
                        &live_params,
                        idx,
                    )?;
                    // Rocq-proved rules as the only path (increment 5,
                    // RQ-58-SELDSL): the register-coincidence elision
                    // (val == dst_lo skips the MOV) stays selector-owned as
                    // DISPATCH between two proven rules — the in-place form's
                    // theorem pins the low half under rd_hi <> rn, which is
                    // exactly what the elision relies on.
                    let rule_ops = if val != dst_lo {
                        crate::sel_dsl::generated::rule_i64_extend_i32_u(dst_lo, dst_hi, val)
                            .map_err(synth_core::Error::synthesis)?
                    } else {
                        crate::sel_dsl::generated::rule_i64_extend_i32_u_inplace(dst_hi, val)
                            .map_err(synth_core::Error::synthesis)?
                    };
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    stack.push(StackVal::i64(dst_lo));
                }

                I64ExtendI32S => {
                    let val = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[val],
                        &live_params,
                        idx,
                    )?;
                    // Rocq-proved rule as the only path (increment 5,
                    // RQ-58-SELDSL): rule_i64_extend_i32_s, with the
                    // rd_hi <> rd_lo pair side condition Ok-or-Err.
                    let rule_ops =
                        crate::sel_dsl::generated::rule_i64_extend_i32_s(dst_lo, dst_hi, val)
                            .map_err(synth_core::Error::synthesis)?;
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    stack.push(StackVal::i64(dst_lo));
                }

                // ============================================================
                // i64 variable shifts (I64Shl / I64ShrU / I64ShrS)
                //
                // Use the existing I64Shl/I64ShrU/I64ShrS pseudo-ops (which
                // expand to the variable-shift logic in arm_encoder.rs) but
                // pass the actual stack-tracked register pairs rather than
                // assuming R0:R1 / R2:R3.
                // ============================================================
                I64Shl | I64ShrU | I64ShrS => {
                    let b_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let b_hi = i64_pair_hi(b_lo)?;
                    let a_hi = i64_pair_hi(a_lo)?;
                    // dst must not overlap any popped operand's half — the
                    // shift pseudo-op reads all four (rn_lo/rn_hi/rm_lo/rm_hi)
                    // before writing the destination.
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[a_lo, a_hi, b_lo, b_hi],
                        &live_params,
                        idx,
                    )?;
                    // The single i64 shift pseudo-op comes from the generated
                    // Rocq-proved rule — the only path (RQ-58-RETIRE). The
                    // `rd_hi <> rd_lo` side condition holds by construction:
                    // alloc_consecutive_pair returns a distinct pair.
                    let shift_op = crate::sel_dsl::i64_pair_bin_rule(
                        op, dst_lo, dst_hi, a_lo, a_hi, b_lo, b_hi,
                    )
                    .expect("i64 shift op dispatch")
                    .map_err(synth_core::Error::synthesis)?
                    .into_iter()
                    .next()
                    .expect("i64 shift rule emits one op");
                    instructions.push(ArmInstruction {
                        op: shift_op,
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i64(dst_lo));
                }

                I64Load { offset, .. } => {
                    // Pop address from stack
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;

                    // Allocate result register pair. MUST be consecutive
                    // in ALLOCATABLE_REGS — i64_pair_hi assumes consecutive
                    // and is called by every i64 op downstream to recover
                    // the high register. Avoid clobbering addr before the
                    // load uses it.
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[addr],
                        &live_params,
                        idx,
                    )?;

                    if self.is_native_pointer_static_offset(*offset) {
                        // #746 (the #739 residual): a DYNAMIC-index i64 load
                        // whose constant memarg `offset` lands in the
                        // static-data region (gale's gust:os `log.line`
                        // bulk-copies its message via i64.load from static
                        // data ABOVE sp_init). Pre-fix this arm DECLINED
                        // loudly (#744 gave only the sub-word arms the
                        // relocation treatment); the raw path below would
                        // BAKE the linmem offset as an un-relocated
                        // MOVW/MOVT immediate — invisible to the #678
                        // `--shadow-stack-size` rebase → silent OOB.
                        // Relocate the base to `__synth_wasm_data + offset`
                        // (the ELF builder retargets it to the owning
                        // segment symbol) and add the dynamic index —
                        // exactly the I32Load #359 branch, with the I64Ldr
                        // pair form. The base temp stays disjoint from the
                        // dst pair: I64Ldr reads its base for BOTH halves,
                        // so neither half may alias it.
                        let base = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &[live_params.as_slice(), &[addr, dst_lo, dst_hi]].concat(),
                            idx,
                        )?;
                        Self::emit_wasm_data_addr(&mut instructions, base, *offset as i32, idx);
                        instructions.push(ArmInstruction {
                            op: ArmOp::Add {
                                rd: base,
                                rn: base,
                                op2: Operand2::Reg(addr),
                            },
                            source_line: Some(idx),
                        });
                        instructions.push(ArmInstruction {
                            op: ArmOp::I64Ldr {
                                rdlo: dst_lo,
                                rdhi: dst_hi,
                                addr: MemAddr::imm(base, 0),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else {
                        // Generate bounds-checked i64 load into the allocated pair
                        let load_ops =
                            self.generate_i64_load_into_regs(dst_lo, dst_hi, addr, *offset as i32);
                        for arm_op in load_ops {
                            instructions.push(ArmInstruction {
                                op: arm_op,
                                source_line: Some(idx),
                            });
                        }
                    }
                    stack.push(StackVal::i64(dst_lo));
                }

                I64Store { offset, .. } => {
                    // WASM i64.store pops: value first, then address
                    let value_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let value_hi = i64_pair_hi(value_lo)?;

                    if self.is_native_pointer_static_offset(*offset) {
                        // #746 (symmetric to the I64Load arm): a dynamic-index
                        // i64 store into the static-data region must relocate
                        // its base to `__synth_wasm_data + offset` + the
                        // dynamic index — pre-fix this arm declined loudly
                        // (#744 relocated only the sub-word arms); the raw
                        // path below would bake the linmem offset as an
                        // un-relocated MOVW/MOVT immediate (silent OOB once
                        // `--shadow-stack-size` shrinks the reservation).
                        let base = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &[live_params.as_slice(), &[addr, value_lo, value_hi]].concat(),
                            idx,
                        )?;
                        Self::emit_wasm_data_addr(&mut instructions, base, *offset as i32, idx);
                        instructions.push(ArmInstruction {
                            op: ArmOp::Add {
                                rd: base,
                                rn: base,
                                op2: Operand2::Reg(addr),
                            },
                            source_line: Some(idx),
                        });
                        instructions.push(ArmInstruction {
                            op: ArmOp::I64Str {
                                rdlo: value_lo,
                                rdhi: value_hi,
                                addr: MemAddr::imm(base, 0),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else {
                        // Generate bounds-checked i64 store from the value pair
                        let store_ops = self.generate_i64_store_from_regs(
                            value_lo,
                            value_hi,
                            addr,
                            *offset as i32,
                        );
                        for arm_op in store_ops {
                            instructions.push(ArmInstruction {
                                op: arm_op,
                                source_line: Some(idx),
                            });
                        }
                    }
                    // Store doesn't push anything to stack
                }

                I64Eqz => {
                    // Pop one i64 register pair
                    let src_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let src_hi = i64_pair_hi(src_lo)?;

                    // Result is a single i32 (0 or 1)
                    let dst = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;

                    // The SetCondZ-shape Rocq-proved rule is the only path
                    // (RQ-58-RETIRE).
                    for rule_op in crate::sel_dsl::generated::rule_i64_eqz(dst, src_lo, src_hi) {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }

                    // I64Eqz produces an i32 result (single register)
                    stack.push(StackVal::i32(dst));
                }

                // =========================================================
                // i32 comparisons (binary: pop 2, push 1)
                // CMP rn, rm; SetCond rd, <condition>
                // =========================================================
                I32Eq | I32Ne | I32LtS | I32LtU | I32GtS | I32GtU | I32LeS | I32LeU | I32GeS
                | I32GeU => {
                    // #258: fold a compare *bound* into a `cmp`/`cmn` immediate
                    // instead of materializing it into a register. A const
                    // `0..=0xFF` → `cmp a, #C`; a const `-0xFF..=-1` →
                    // `cmn a, #-C` (`cmp a, #neg` ≡ `cmn a, #|neg|`, same flags →
                    // same condition). Bounded to a byte (both imm encoders are
                    // correct there); the guard keeps it to a cleanly-tail
                    // materialization (not spilled), covering the `movw` and the
                    // `movw;mvn` (negative) forms.
                    let fold = if idx > 0
                        && instructions
                            .last()
                            .is_some_and(|i| i.source_line == Some(idx - 1))
                    {
                        match wasm_ops[idx - 1] {
                            WasmOp::I32Const(c) if (0..=0xFF).contains(&c) => Some((false, c)),
                            WasmOp::I32Const(c) if (-0xFF..=-1).contains(&c) => Some((true, -c)),
                            _ => None,
                        }
                    } else {
                        None
                    };
                    // Rocq-proved rules on the reg-reg path (increment 2) AND
                    // the positive imm-fold path (increment 5,
                    // `rule_i32_*_imm`: `cmp a, #C; SetCond`). `reg_operands`
                    // records the reg-reg operand pair for its dispatch.
                    // RESIDUAL, not superseded: the NEGATIVE fold half
                    // (`cmn a, #-C`) has no rule — its add-derived NZCV needs
                    // a sub<->add flag-correspondence lemma family the Rocq
                    // model does not carry — so its hand-written Cmn+SetCond
                    // emission stays (see the else branch below).
                    let mut reg_operands = None;
                    let (a, imm_fold) = if let Some((is_neg, mag)) = fold {
                        let _b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        Self::drop_prev_const_materialization(&mut instructions, idx - 1);
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Some((is_neg, mag)))
                    } else {
                        let b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        reg_operands = Some((a, b));
                        (a, None)
                    };
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    let dsl_ops = match imm_fold {
                        None => {
                            let (a, b) = reg_operands.expect("reg-reg operands recorded");
                            crate::sel_dsl::i32_cmp_rule(op, dst, a, b)
                        }
                        Some((false, mag)) => crate::sel_dsl::i32_cmp_imm_rule(op, dst, a, mag),
                        // cmn residual: falls through to the hand-written arm.
                        Some((true, _)) => None,
                    };
                    if let Some(rule_ops) = dsl_ops {
                        for rule_op in rule_ops {
                            instructions.push(ArmInstruction {
                                op: rule_op,
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                    } else {
                        let (_, mag) =
                            imm_fold.expect("only the negative fold reaches the cmn residual");
                        let cond = match op {
                            I32Eq => Condition::EQ,
                            I32Ne => Condition::NE,
                            I32LtS => Condition::LT,
                            I32LtU => Condition::LO,
                            I32GtS => Condition::GT,
                            I32GtU => Condition::HI,
                            I32LeS => Condition::LE,
                            I32LeU => Condition::LS,
                            I32GeS => Condition::GE,
                            I32GeU => Condition::HS,
                            _ => unreachable!(),
                        };
                        instructions.push(ArmInstruction {
                            op: ArmOp::Cmn {
                                rn: a,
                                op2: Operand2::Imm(mag),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        // SetCond rd, <cond> — materializes 0/1 based on flags
                        instructions.push(ArmInstruction {
                            op: ArmOp::SetCond { rd: dst, cond },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    stack.push(StackVal::i32(dst));
                }

                // i32.eqz (unary: pop 1, push 1)
                // CMP rn, #0; SetCond rd, EQ
                I32Eqz => {
                    let a = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    // The CMP+SetCond pair comes from the generated
                    // Rocq-proved rule — the only path (RQ-58-RETIRE).
                    // select_with_stack owns the materializing lowering, so
                    // the rule is wired here only.
                    let rule_ops = crate::sel_dsl::i32_eqz_rule(op, dst, a)
                        .expect("i32.eqz has a generated rule");
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    stack.push(StackVal::i32(dst));
                }

                // =========================================================
                // i32 shifts and rotates (binary: pop 2, push 1)
                // =========================================================
                I32Shl | I32ShrS | I32ShrU | I32Rotr => {
                    let shift_amt = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let value = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    // #682: LSL/LSR/ASR mask the amount mod 32 through R12
                    // (ARM uses Rm[7:0]; WASM requires mod 32). ROR is cyclic,
                    // so Rm[7:0] already agrees with WASM — no mask. The
                    // generated Rocq-proved rules carry the mask themselves
                    // and are the only path (RQ-58-RETIRE).
                    let rule_ops =
                        crate::sel_dsl::i32_shift_rule(op, dst, value, shift_amt, Reg::R12)
                            .expect("i32 shift/rotate op has a generated rule")
                            .map_err(synth_core::Error::synthesis)?;
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    stack.push(StackVal::i32(dst));
                }

                I32Rotl => {
                    // Rotate left by N = Rotate right by (32 - N)
                    // RSB tmp, shift_amt, #32; ROR dst, value, tmp
                    let shift_amt = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let value = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    let tmp = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    // RSB+ROR from the Rocq-proved rule — the only path
                    // (increment 5, RQ-58-SELDSL closes the #999 residual:
                    // the rule existed but was never wired here). Carries the
                    // `rs <> rn` scratch side condition, Ok-or-Err.
                    let rule_ops =
                        crate::sel_dsl::generated::rule_i32_rotl(dst, value, shift_amt, tmp)
                            .map_err(synth_core::Error::synthesis)?;
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    stack.push(StackVal::i32(dst));
                }

                // =========================================================
                // i32 unary bit operations (pop 1, push 1)
                // =========================================================
                I32Clz => {
                    let src = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    // The single CLZ comes from the generated Rocq-proved
                    // rule — the only path (RQ-58-RETIRE).
                    let rule_ops = crate::sel_dsl::i32_unary_rule(op, dst, src)
                        .expect("i32.clz has a generated rule");
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    stack.push(StackVal::i32(dst));
                }

                I32Ctz => {
                    // Count trailing zeros: RBIT + CLZ
                    let src = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    // The two-instruction RBIT+CLZ scratch=dest shape comes
                    // from the generated Rocq-proved rule — the only path
                    // (RQ-58-RETIRE).
                    let rule_ops = crate::sel_dsl::i32_unary_rule(op, dst, src)
                        .expect("i32.ctz has a generated rule");
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    stack.push(StackVal::i32(dst));
                }

                I32Popcnt => {
                    // Population count — no native ARM instruction
                    // Popcnt pseudo-op expanded by encoder
                    let src = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    // Pseudo-op-tier Rocq-proved rule (ArmOp::Popcnt) — the
                    // only path (RQ-58-RETIRE).
                    let rule_ops = crate::sel_dsl::i32_unary_rule(op, dst, src)
                        .expect("i32.popcnt has a generated rule");
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    stack.push(StackVal::i32(dst));
                }

                // =========================================================
                // i32 sign extension (pop 1, push 1)
                // =========================================================
                I32Extend8S => {
                    let src = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    // SXTB from the Rocq-proved rule — the only path
                    // (increment 6, RQ-59-SUBTRACT: the hand-written
                    // ArmOp::Sxtb construction is deleted).
                    let rule_ops = crate::sel_dsl::i32_extend_rule(op, dst, src)
                        .expect("i32.extend8_s has a generated rule");
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    stack.push(StackVal::i32(dst));
                }

                I32Extend16S => {
                    let src = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    // SXTH from the Rocq-proved rule — the only path
                    // (increment 6, RQ-59-SUBTRACT: the hand-written
                    // ArmOp::Sxth construction is deleted).
                    let rule_ops = crate::sel_dsl::i32_extend_rule(op, dst, src)
                        .expect("i32.extend16_s has a generated rule");
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    stack.push(StackVal::i32(dst));
                }

                // ============================================================
                // i64 comparisons (binary: pop 2 i64 pairs, push 1 i32 result)
                //
                // Issue #103: previously these fell through to `select_default`,
                // which hardcodes the operand pairs at R0:R1 / R2:R3 and the
                // result at R0 — clobbering any AAPCS param register the user
                // hasn't read yet via `LocalGet`. The fix is to pop the actual
                // register pairs the stack tracker assigned to the operands and
                // allocate a result register with `alloc_temp_safe`, which
                // already skips live stack values.
                //
                // Same class as PR #86's i64-const fix in `optimizer_bridge`,
                // applied here to every i64 op that hardcoded R0..R3.
                // ============================================================
                I64Eq | I64Ne | I64LtS | I64LtU | I64LeS | I64LeU | I64GtS | I64GtU | I64GeS
                | I64GeU => {
                    let b_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let b_hi = i64_pair_hi(b_lo)?;
                    let a_hi = i64_pair_hi(a_lo)?;
                    // Result is a single i32. alloc_temp_safe avoids any reg
                    // still on the wasm stack, but the popped operand halves
                    // are NO LONGER on the stack — they may be reused by the
                    // allocator. That is fine for I64SetCond which encodes to
                    // a sequence that reads all four operand halves before
                    // writing rd (see arm_encoder; the CMP chain is fully
                    // resolved before SetCond writes the byte).
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    // The I64SetCond pseudo-op (condition mapping included)
                    // comes from the generated Rocq-proved rule — the only
                    // path (RQ-58-RETIRE).
                    let rule_ops =
                        crate::sel_dsl::i64_setcond_rule(op, dst, a_lo, a_hi, b_lo, b_hi)
                            .expect("binary i64 comparison has a generated rule");
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    stack.push(StackVal::i32(dst));
                }

                // ============================================================
                // i64 multiply (binary: pop 2 i64 pairs, push 1 i64 pair)
                //
                // Issue #103: was hardcoding R0:R1 (operands and result low),
                // R2:R3 (second operand). Now uses the stack-tracked pairs
                // and a fresh consecutive pair for the destination.
                // ============================================================
                I64Mul => {
                    let b_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let b_hi = i64_pair_hi(b_lo)?;
                    let a_hi = i64_pair_hi(a_lo)?;
                    // I64Mul encodes to UMULL + MLA cross products: rd_lo/rd_hi
                    // are written, and ALL four operand halves are read. dst
                    // must not overlap any operand half before the encoded
                    // sequence reads it.
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[a_lo, a_hi, b_lo, b_hi],
                        &live_params,
                        idx,
                    )?;
                    // The single I64Mul pseudo-op comes from the generated
                    // Rocq-proved rule — the only path (RQ-58-RETIRE;
                    // `rd_hi <> rd_lo` holds by construction via
                    // alloc_consecutive_pair).
                    let mul_op = crate::sel_dsl::i64_pair_bin_rule(
                        op, dst_lo, dst_hi, a_lo, a_hi, b_lo, b_hi,
                    )
                    .expect("i64 mul op dispatch")
                    .map_err(synth_core::Error::synthesis)?
                    .into_iter()
                    .next()
                    .expect("i64 mul rule emits one op");
                    instructions.push(ArmInstruction {
                        op: mul_op,
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i64(dst_lo));
                }

                // ============================================================
                // i64 divide / remainder (binary: pop 2 i64 pairs, push 1 pair)
                //
                // Issue #103: was hardcoding R0:R1 / R2:R3. The encoded
                // sequence for these ops is a libcall-style helper that
                // reads/writes the operand and result registers — using the
                // stack-tracked pairs keeps AAPCS params intact.
                // ============================================================
                I64DivS | I64DivU | I64RemS | I64RemU => {
                    let b_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let b_hi = i64_pair_hi(b_lo)?;
                    let a_hi = i64_pair_hi(a_lo)?;
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[a_lo, a_hi, b_lo, b_hi],
                        &live_params,
                        idx,
                    )?;
                    // #494 phase 2b: certificate-discharged guard-elision marks
                    // (fact-spec pass, UNSAT obligations checked BEFORE selection).
                    // The overflow mark applies to div_s ONLY and is a separate
                    // obligation from the zero mark (#633/#634).
                    let elide_zero_guard = self.fact_div_zero_elide.contains(&idx);
                    let elide_overflow_guard = self.fact_div_ovf_elide.contains(&idx);
                    let arm_op = match op {
                        I64DivS => ArmOp::I64DivS {
                            rdlo: dst_lo,
                            rdhi: dst_hi,
                            rnlo: a_lo,
                            rnhi: a_hi,
                            rmlo: b_lo,
                            rmhi: b_hi,
                            elide_zero_guard,
                            elide_overflow_guard,
                        },
                        I64DivU => ArmOp::I64DivU {
                            rdlo: dst_lo,
                            rdhi: dst_hi,
                            rnlo: a_lo,
                            rnhi: a_hi,
                            rmlo: b_lo,
                            rmhi: b_hi,
                            elide_zero_guard,
                        },
                        I64RemS => ArmOp::I64RemS {
                            rdlo: dst_lo,
                            rdhi: dst_hi,
                            rnlo: a_lo,
                            rnhi: a_hi,
                            rmlo: b_lo,
                            rmhi: b_hi,
                            elide_zero_guard,
                        },
                        I64RemU => ArmOp::I64RemU {
                            rdlo: dst_lo,
                            rdhi: dst_hi,
                            rnlo: a_lo,
                            rnhi: a_hi,
                            rmlo: b_lo,
                            rmhi: b_hi,
                            elide_zero_guard,
                        },
                        _ => unreachable!(),
                    };
                    instructions.push(ArmInstruction {
                        op: arm_op,
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i64(dst_lo));
                }

                // ============================================================
                // i64 rotations (binary: pop 2 i64 pairs, push 1 pair)
                //
                // Issue #103: was hardcoding R0:R1 / R2. ArmOp::I64Rotl/Rotr
                // takes a SINGLE shift reg (the low half of the i64 shift
                // amount) — i64.rotl in WASM has an i64 shift amount but
                // ARM only uses the low 32 bits modulo-64 by convention.
                // We pop both halves of `b` for stack correctness and pass
                // b_lo as the shift reg, matching the pre-fix `select_default`
                // contract (which assumed shift in R2).
                // ============================================================
                I64Rotl | I64Rotr => {
                    let b_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let b_hi = i64_pair_hi(b_lo)?;
                    let a_hi = i64_pair_hi(a_lo)?;
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[a_lo, a_hi, b_lo, b_hi],
                        &live_params,
                        idx,
                    )?;
                    // The single i64 rotate pseudo-op comes from the generated
                    // Rocq-proved rule — the only path (RQ-58-RETIRE;
                    // `rd_hi <> rd_lo` holds by construction).
                    let arm_op = crate::sel_dsl::i64_rot_rule(op, dst_lo, dst_hi, a_lo, a_hi, b_lo)
                        .expect("i64 rotate op dispatch")
                        .map_err(synth_core::Error::synthesis)?
                        .into_iter()
                        .next()
                        .expect("i64 rotate rule emits one op");
                    instructions.push(ArmInstruction {
                        op: arm_op,
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i64(dst_lo));
                }

                // ============================================================
                // i64 unary bit ops (pop 1 i64 pair, push 1 i32 result)
                //
                // I64Clz / I64Ctz / I64Popcnt return a 32-bit count. Was
                // hardcoding R0 (operand lo + result) and R1 (operand hi).
                // ============================================================
                I64Clz | I64Ctz | I64Popcnt => {
                    let src_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let src_hi = i64_pair_hi(src_lo)?;
                    // The count is i64-typed (lo = count 0..64, hi = 0). Produce
                    // a proper pair so the hi half is reserved and zeroed
                    // (#204/#171: pushing i32 left hi unreserved/garbage for a
                    // downstream i64 consumer).
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[src_lo, src_hi],
                        &live_params,
                        idx,
                    )?;
                    // The single i64 bit-count pseudo-op comes from the
                    // generated Rocq-proved rule — the only path
                    // (RQ-58-RETIRE). The trailing `Movw dst_hi, 0` (hi-half
                    // zeroing) is outside the rule's single-pseudo-op scope,
                    // exactly as the flat-model ancestor proves only the count
                    // pseudo-op.
                    let arm_op = crate::sel_dsl::i64_unary_count_rule(op, dst_lo, src_lo, src_hi)
                        .expect("i64 count op dispatch")
                        .into_iter()
                        .next()
                        .expect("i64 count rule emits one op");
                    instructions.push(ArmInstruction {
                        op: arm_op,
                        source_line: Some(idx),
                    });
                    instructions.push(ArmInstruction {
                        op: ArmOp::Movw {
                            rd: dst_hi,
                            imm16: 0,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i64(dst_lo));
                }

                // ============================================================
                // i64 in-place sign extension (pop 1 i64 pair, push 1 pair)
                //
                // I64Extend{8,16,32}S take an i64 (the upper bits are
                // ignored) and sign-extend the low N bits to 64. Was
                // hardcoding R0:R1 for both operand and result.
                // ============================================================
                I64Extend8S | I64Extend16S | I64Extend32S => {
                    let src_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let _src_hi = i64_pair_hi(src_lo)?;
                    // dst must not overlap src_lo before the encoded sequence
                    // reads it (the encoder issues a SXTB/SXTH/MOV + ASR #31
                    // pattern that reads src_lo first then writes rdlo/rdhi).
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[src_lo],
                        &live_params,
                        idx,
                    )?;
                    // The narrow sign-extension pseudo-op comes from the
                    // Rocq-proved rule — the only path (increment 6,
                    // RQ-59-SUBTRACT: the hand-written ArmOp::I64Extend{8,16,32}S
                    // construction match, wildcard included, is deleted).
                    // Carries the rd_hi <> rd_lo side condition Ok-or-Err;
                    // alloc_consecutive_pair satisfies it by construction.
                    let rule_ops =
                        crate::sel_dsl::i64_extend_narrow_rule(op, dst_lo, dst_hi, src_lo)
                            .expect("narrow i64 sign-extend op has a generated rule")
                            .map_err(synth_core::Error::synthesis)?;
                    for rule_op in rule_ops {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    stack.push(StackVal::i64(dst_lo));
                }

                // ============================================================
                // i64 → i32 wrap (pop 1 i64 pair, push 1 i32)
                //
                // I32WrapI64 keeps the low half. Was hardcoding R0 for both
                // operand low and result.
                // ============================================================
                I32WrapI64 => {
                    let src_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let _src_hi = i64_pair_hi(src_lo)?;
                    // Always allocate a fresh temporary. Pre-fix, this picked
                    // `Reg::R0` when `idx == wasm_ops.len() - 1`, on the theory
                    // that "the last wasm op is the function's return value, so
                    // place it directly in R0". That premature R0-pin clobbers
                    // any AAPCS param the function hasn't yet read — PR #100's
                    // `i64_lowering_doesnt_clobber_params` fuzz harness caught
                    // this for the `i64.const; i32.wrap_i64` pattern (rdlo
                    // landing on R3, then I32WrapI64 pinning rd=R0). The
                    // function epilogue now handles the return-value Mov to R0
                    // explicitly via `emit_return_move_if_needed` below.
                    let dst = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    // Rocq-proved rule as the only path (increment 5,
                    // RQ-58-SELDSL): the pseudo-op comes from
                    // rule_i32_wrap_i64.
                    for rule_op in crate::sel_dsl::generated::rule_i32_wrap_i64(dst, src_lo) {
                        instructions.push(ArmInstruction {
                            op: rule_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    stack.push(StackVal::i32(dst));
                }

                // Bulk memory (#374): memory.fill / memory.copy. Both pop three
                // i32 operands (dst, val/src, len) and push nothing. The lowering
                // reuses (mutates) operand registers as walking pointers / byte
                // buffer, so any popped register still live past the op — a
                // register-homed local's HOME register, a duplicate vstack entry,
                // or an alias of another operand — is first copied into a fresh
                // scratch via `bulk_mutable_operand` (#677); a provably-dead temp
                // is used in place (byte-identical to pre-#677 code). Lowered to a
                // bounds-checked byte loop:
                //   - bounds (Software mode, mirroring the store helper): trap
                //     iff `off + len` overflows u32 OR `off + len > size` (R10, in
                //     bytes). End-EXCLUSIVE, so a zero-length op at `off == size`
                //     and an access ending exactly at `size` do NOT trap (matches
                //     wasmtime). Trap target is the established "Trap_Handler".
                //   - Masking (#679): the same wrap-not-trap discipline as the
                //     scalar `mask_effective_address` — fold dst (and src) into
                //     `[0, size)` with `AND (size-1)`, then clamp len to
                //     `size - dst` (and `size - src`) so the FINAL byte stays in
                //     bounds; every loop access lands in `[0, size)` and an
                //     in-bounds op is untouched. Pre-#679 Masking emitted the
                //     raw loop, byte-identical to None, while the safety
                //     manifest still attested `mask`.
                //   - addresses are R11-relative (R11 = linear-memory base);
                //     R10 = size in bytes.
                // None/Mpu emit just the loop (MPU faults in hardware).
                MemoryFill => {
                    let len = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let val = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let loop_label = self.alloc_label("memfill_loop");
                    let done_label = self.alloc_label("memfill_done");
                    let software = matches!(self.bounds_check, BoundsCheckConfig::Software);
                    let masking = matches!(self.bounds_check, BoundsCheckConfig::Masking);
                    // #677: the loop mutates `dst` in place (walking pointer) and,
                    // under Masking, the clamp mutates `len`; copy either into a
                    // scratch first when it is still live past this op. `val` and
                    // (non-mask) `len` are only ever read — no copy needed.
                    let mut reserve: Vec<Reg> = live_params.clone();
                    reserve.extend([len, val, dst]);
                    let dst = bulk_mutable_operand(
                        dst,
                        &[val, len],
                        &live_params,
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &mut reserve,
                        idx,
                    )?;
                    let len = if masking {
                        bulk_mutable_operand(
                            len,
                            &[val, dst],
                            &live_params,
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &mut reserve,
                            idx,
                        )?
                    } else {
                        len
                    };
                    let mut ops: Vec<ArmOp> = Vec::new();
                    if masking {
                        // #679: dst &= (size-1); len = min(len, size - dst).
                        // After this, dst ∈ [0, size) and dst+len <= size, so
                        // every byte the loop writes is in bounds; an op that was
                        // already wasm-in-bounds is unchanged (dst < size keeps
                        // AND a no-op; len <= size-dst keeps the clamp a no-op).
                        ops.push(ArmOp::Sub {
                            rd: Reg::R12,
                            rn: Reg::R10,
                            op2: Operand2::Imm(1),
                        });
                        ops.push(ArmOp::And {
                            rd: dst,
                            rn: dst,
                            op2: Operand2::Reg(Reg::R12),
                        });
                        ops.push(ArmOp::Sub {
                            rd: Reg::R12,
                            rn: Reg::R10,
                            op2: Operand2::Reg(dst),
                        });
                        ops.push(ArmOp::Cmp {
                            rn: len,
                            op2: Operand2::Reg(Reg::R12),
                        });
                        ops.push(ArmOp::SelectMove {
                            rd: len,
                            rm: Reg::R12,
                            cond: Condition::HI,
                        });
                    }
                    // R12 = dst + len (wasm offset of one-past-end); ADDS sets carry
                    // on u32 overflow.
                    ops.push(ArmOp::Adds {
                        rd: Reg::R12,
                        rn: dst,
                        op2: Operand2::Reg(len),
                    });
                    if software {
                        // Trap (inline UDF) iff `dst+len` overflows u32 OR
                        // `dst+len > size` (end-EXCLUSIVE, so `== size` is ok). The
                        // trap is a self-contained `UDF` guarded by a LOCAL skip
                        // branch — a body branch to the external `Trap_Handler` is
                        // only relocated in `--relocatable` mode, not in the
                        // self-contained image; `UDF` faults to UsageFault/HardFault
                        // which the vector table routes to `Trap_Handler` on real
                        // silicon (matching wasmtime's trap).
                        let ovf_ok = self.alloc_label("memfill_ovf_ok");
                        let size_ok = self.alloc_label("memfill_size_ok");
                        // no overflow => carry clear (LO) => skip the trap
                        ops.push(ArmOp::Bcc {
                            cond: Condition::LO,
                            label: ovf_ok.clone(),
                        });
                        ops.push(ArmOp::Udf { imm: 0 });
                        ops.push(ArmOp::Label { name: ovf_ok });
                        // size >= end (HS after `CMP size,end`) => in bounds => skip
                        ops.push(ArmOp::Cmp {
                            rn: Reg::R10,
                            op2: Operand2::Reg(Reg::R12),
                        });
                        ops.push(ArmOp::Bcc {
                            cond: Condition::HS,
                            label: size_ok.clone(),
                        });
                        ops.push(ArmOp::Udf { imm: 0 });
                        ops.push(ArmOp::Label { name: size_ok });
                    }
                    // R12 = base + (dst+len) = absolute end pointer; dst = base + dst
                    // = absolute start pointer. `len` is dead after the Adds above.
                    ops.push(ArmOp::Add {
                        rd: Reg::R12,
                        rn: Reg::R11,
                        op2: Operand2::Reg(Reg::R12),
                    });
                    ops.push(ArmOp::Add {
                        rd: dst,
                        rn: Reg::R11,
                        op2: Operand2::Reg(dst),
                    });
                    ops.push(ArmOp::Label {
                        name: loop_label.clone(),
                    });
                    ops.push(ArmOp::Cmp {
                        rn: dst,
                        op2: Operand2::Reg(Reg::R12),
                    });
                    ops.push(ArmOp::Bcc {
                        cond: Condition::HS,
                        label: done_label.clone(),
                    });
                    // STRB writes only the low byte of `val` (free high-bit mask).
                    ops.push(ArmOp::Strb {
                        rd: val,
                        addr: MemAddr::imm(dst, 0),
                    });
                    ops.push(ArmOp::Add {
                        rd: dst,
                        rn: dst,
                        op2: Operand2::Imm(1),
                    });
                    ops.push(ArmOp::B {
                        label: loop_label.clone(),
                    });
                    ops.push(ArmOp::Label {
                        name: done_label.clone(),
                    });
                    for op in ops {
                        instructions.push(ArmInstruction {
                            op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                }

                MemoryCopy => {
                    let len = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let src = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let fwd_loop = self.alloc_label("memcpy_fwd");
                    let bwd_setup = self.alloc_label("memcpy_bwd");
                    let bwd_loop = self.alloc_label("memcpy_bwd_loop");
                    let done_label = self.alloc_label("memcpy_done");
                    let software = matches!(self.bounds_check, BoundsCheckConfig::Software);
                    let masking = matches!(self.bounds_check, BoundsCheckConfig::Masking);
                    // #677: the copy mutates ALL THREE operand registers in place
                    // (dst/src walking pointers, len as the byte buffer — and the
                    // Masking clamp); copy each into a scratch first when it is
                    // still live past this op.
                    let mut reserve: Vec<Reg> = live_params.clone();
                    reserve.extend([len, src, dst]);
                    let dst = bulk_mutable_operand(
                        dst,
                        &[src, len],
                        &live_params,
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &mut reserve,
                        idx,
                    )?;
                    let src = bulk_mutable_operand(
                        src,
                        &[dst, len],
                        &live_params,
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &mut reserve,
                        idx,
                    )?;
                    let len = bulk_mutable_operand(
                        len,
                        &[dst, src],
                        &live_params,
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &mut reserve,
                        idx,
                    )?;
                    let mut ops: Vec<ArmOp> = Vec::new();
                    if masking {
                        // #679: fold BOTH effective addresses into [0, size) and
                        // clamp len so both ranges end within the bound:
                        //   dst &= size-1; src &= size-1;
                        //   len = min(len, size - dst, size - src)
                        // Every byte the loop touches (read AND write) then lands
                        // in [0, size); a wasm-in-bounds copy is unchanged. Same
                        // wrap-not-trap discipline as `mask_effective_address`,
                        // with the dynamic len taking the place of the static
                        // access-size clamp (len bounds the FINAL byte).
                        ops.push(ArmOp::Sub {
                            rd: Reg::R12,
                            rn: Reg::R10,
                            op2: Operand2::Imm(1),
                        });
                        ops.push(ArmOp::And {
                            rd: dst,
                            rn: dst,
                            op2: Operand2::Reg(Reg::R12),
                        });
                        ops.push(ArmOp::And {
                            rd: src,
                            rn: src,
                            op2: Operand2::Reg(Reg::R12),
                        });
                        for range_base in [dst, src] {
                            ops.push(ArmOp::Sub {
                                rd: Reg::R12,
                                rn: Reg::R10,
                                op2: Operand2::Reg(range_base),
                            });
                            ops.push(ArmOp::Cmp {
                                rn: len,
                                op2: Operand2::Reg(Reg::R12),
                            });
                            ops.push(ArmOp::SelectMove {
                                rd: len,
                                rm: Reg::R12,
                                cond: Condition::HI,
                            });
                        }
                    }
                    if software {
                        // Both `dst+len` and `src+len` must be in bounds
                        // (end-exclusive; overflow or `> size` traps, `== size` is
                        // ok). Inline UDF guarded by LOCAL skip branches — see
                        // MemoryFill above for why an external Trap_Handler branch
                        // is not used in the self-contained image.
                        for (base_reg, tag) in [(dst, "memcpy_dst"), (src, "memcpy_src")] {
                            let ovf_ok = self.alloc_label(&format!("{tag}_ovf_ok"));
                            let size_ok = self.alloc_label(&format!("{tag}_size_ok"));
                            ops.push(ArmOp::Adds {
                                rd: Reg::R12,
                                rn: base_reg,
                                op2: Operand2::Reg(len),
                            });
                            ops.push(ArmOp::Bcc {
                                cond: Condition::LO,
                                label: ovf_ok.clone(),
                            });
                            ops.push(ArmOp::Udf { imm: 0 });
                            ops.push(ArmOp::Label { name: ovf_ok });
                            ops.push(ArmOp::Cmp {
                                rn: Reg::R10,
                                op2: Operand2::Reg(Reg::R12),
                            });
                            ops.push(ArmOp::Bcc {
                                cond: Condition::HS,
                                label: size_ok.clone(),
                            });
                            ops.push(ArmOp::Udf { imm: 0 });
                            ops.push(ArmOp::Label { name: size_ok });
                        }
                    }
                    // memmove direction: overlapping `dst > src` MUST copy backward
                    // (a forward loop would overwrite source bytes before reading
                    // them). `dst <= src` (incl. non-overlap) copies forward. The
                    // compare is on wasm offsets, monotone under +R11.
                    ops.push(ArmOp::Cmp {
                        rn: dst,
                        op2: Operand2::Reg(src),
                    });
                    ops.push(ArmOp::Bcc {
                        cond: Condition::HI,
                        label: bwd_setup.clone(),
                    });
                    // ---- forward: sptr=R11+src, dptr=R11+dst, dend=dptr+len ----
                    ops.push(ArmOp::Add {
                        rd: src,
                        rn: Reg::R11,
                        op2: Operand2::Reg(src),
                    });
                    ops.push(ArmOp::Add {
                        rd: dst,
                        rn: Reg::R11,
                        op2: Operand2::Reg(dst),
                    });
                    ops.push(ArmOp::Add {
                        rd: Reg::R12,
                        rn: dst,
                        op2: Operand2::Reg(len),
                    });
                    // `len` dead from here; reused as the byte buffer below.
                    ops.push(ArmOp::Label {
                        name: fwd_loop.clone(),
                    });
                    ops.push(ArmOp::Cmp {
                        rn: dst,
                        op2: Operand2::Reg(Reg::R12),
                    });
                    ops.push(ArmOp::Bcc {
                        cond: Condition::HS,
                        label: done_label.clone(),
                    });
                    ops.push(ArmOp::Ldrb {
                        rd: len,
                        addr: MemAddr::imm(src, 0),
                    });
                    ops.push(ArmOp::Strb {
                        rd: len,
                        addr: MemAddr::imm(dst, 0),
                    });
                    ops.push(ArmOp::Add {
                        rd: src,
                        rn: src,
                        op2: Operand2::Imm(1),
                    });
                    ops.push(ArmOp::Add {
                        rd: dst,
                        rn: dst,
                        op2: Operand2::Imm(1),
                    });
                    ops.push(ArmOp::B {
                        label: fwd_loop.clone(),
                    });
                    // ---- backward: walk from one-past-end down to dlo (exclusive) ----
                    ops.push(ArmOp::Label {
                        name: bwd_setup.clone(),
                    });
                    // R12 = dlo = R11 + dst (lowest dst byte; exclusive lower bound)
                    ops.push(ArmOp::Add {
                        rd: Reg::R12,
                        rn: Reg::R11,
                        op2: Operand2::Reg(dst),
                    });
                    // dst = R11 + dst + len (one past highest dst byte)
                    ops.push(ArmOp::Add {
                        rd: dst,
                        rn: dst,
                        op2: Operand2::Reg(len),
                    });
                    ops.push(ArmOp::Add {
                        rd: dst,
                        rn: Reg::R11,
                        op2: Operand2::Reg(dst),
                    });
                    // src = R11 + src + len (one past highest src byte); `len` dead after
                    ops.push(ArmOp::Add {
                        rd: src,
                        rn: src,
                        op2: Operand2::Reg(len),
                    });
                    ops.push(ArmOp::Add {
                        rd: src,
                        rn: Reg::R11,
                        op2: Operand2::Reg(src),
                    });
                    ops.push(ArmOp::Label {
                        name: bwd_loop.clone(),
                    });
                    // dptr <= dlo => all bytes copied
                    ops.push(ArmOp::Cmp {
                        rn: dst,
                        op2: Operand2::Reg(Reg::R12),
                    });
                    ops.push(ArmOp::Bcc {
                        cond: Condition::LS,
                        label: done_label.clone(),
                    });
                    ops.push(ArmOp::Sub {
                        rd: dst,
                        rn: dst,
                        op2: Operand2::Imm(1),
                    });
                    ops.push(ArmOp::Sub {
                        rd: src,
                        rn: src,
                        op2: Operand2::Imm(1),
                    });
                    ops.push(ArmOp::Ldrb {
                        rd: len,
                        addr: MemAddr::imm(src, 0),
                    });
                    ops.push(ArmOp::Strb {
                        rd: len,
                        addr: MemAddr::imm(dst, 0),
                    });
                    ops.push(ArmOp::B {
                        label: bwd_loop.clone(),
                    });
                    ops.push(ArmOp::Label {
                        name: done_label.clone(),
                    });
                    for op in ops {
                        instructions.push(ArmInstruction {
                            op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                }

                // For other operations, fall back to default behavior.
                // Stack tracking is approximate after this point: select_default
                // uses its own register allocator and doesn't update the virtual stack.
                _ => {
                    let arm_ops = self.select_default(op)?;
                    for arm_op in arm_ops {
                        instructions.push(ArmInstruction {
                            op: arm_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    // Update stack based on WASM stack effect.
                    // This is approximate — select_default allocated its own registers.
                    let (pops, pushes) = wasm_stack_effect(op);
                    for _ in 0..pops.min(stack.len()) {
                        stack.pop();
                    }
                    for _ in 0..pushes {
                        // Push a placeholder — select_default used its own register
                        let placeholder = self.regs.alloc_reg();
                        stack.push(StackVal::i32(placeholder));
                    }
                }
            }
        }

        // Function epilogue: place the AAPCS return value in R0 (if the last
        // expression result isn't already there), deallocate the local frame,
        // then restore callee-saved registers and return via PC.
        //
        // Pre-fix, several wasm-op handlers (I32Add, I32Sub, ..., I32WrapI64,
        // I64ExtendI32U/S) pinned the destination register to R0 when their
        // `idx == wasm_ops.len() - 1`. That heuristic conflated "lexically
        // last op handed to select_with_stack" with "function-return
        // boundary"; with the move to fuzz-driven testing (PR #100) those
        // are no longer the same thing, and the pin caused AAPCS-param
        // clobbers. The fix is to keep results in regalloc-chosen temps and
        // have the epilogue emit the AAPCS return-value move here, ONCE.
        //
        // `source_line: None` keeps the move out of the
        // "writes-param-reg-before-LocalGet" invariant the fuzz harness
        // checks; it's the function-boundary Mov, not a body-level write.
        // Reload-aware (#171): a spilled final result is reloaded before the
        // AAPCS return-value move. Past the op loop, so use wasm_ops.len() as
        // the synthetic source line for any reload.
        // #311 defect 3 (gale): an i64 RESULT is the (lo, hi) pair and BOTH
        // halves must reach r0:r1 — the single-register move silently dropped
        // the hi whenever the final value transited registers other than
        // r0/r1 (decide() returned (0,0) where the contract says (0,1)).
        // Capture the width BEFORE peek (which returns only the lo register).
        // GI-FPU-002 (#619/#369): an f32 result is returned in S0 (AAPCS-VFP).
        // If the producing S-register is not already S0, copy it there via a
        // core scratch (phase 1 has no VMOV Sd,Sm op; R12/IP is caller-saved,
        // safe to clobber at the epilogue). Skip the integer return-value move.
        // GI-FPU-002 phase 2 (#719/#369) SOUNDNESS: a function that RETURNS f32
        // or f64 must present its result in an S/D register (a `Float` stack
        // entry). If the top-of-stack is anything else — most importantly an
        // integer-tagged `Reg` produced by a call that returned f32/f64 as R0
        // (#719 "f32 in a fn with a call": the call result is pushed as an
        // integer operand) — emitting the integer R0 return would be a SILENT
        // MISCOMPILE: the AAPCS-VFP caller reads S0/D0. Decline loudly instead
        // (skip-and-continue). This also catches the pre-existing pure-passthrough
        // shape `(func (result f32) (call $g))` that never entered the VFP path.
        // Gated on `fpu.is_some()`: the guard protects the HARD-float
        // (AAPCS-VFP) return convention. A soft-float target (m0/m3/r5)
        // genuinely returns f32 in R0 / f64 in R0:R1, so an integer-tagged
        // result at the epilogue is ABI-CORRECT there (e.g. the f64-param
        // passthrough `(param f64) (result f64) local.get 0` on cortex-m3,
        // where the i64-pair treatment matches the soft-float ABI exactly).
        if (self.ret_f32 || self.ret_f64) && self.fpu.is_some() {
            let top_matches = if self.ret_f64 {
                stack.last().and_then(|v| v.as_double()).is_some()
            } else {
                stack.last().and_then(|v| v.as_float()).is_some()
            };
            if !top_matches {
                return Err(synth_core::Error::synthesis(format!(
                    "GI-FPU-002 phase 2: function returns {} but its result reached \
                     the epilogue in a core register (e.g. an f32/f64-returning \
                     call's R0 result) — refusing to emit an integer R0 return \
                     where an AAPCS-VFP caller reads {} (declining, #719/#369)",
                    if self.ret_f64 { "f64" } else { "f32" },
                    if self.ret_f64 { "D0" } else { "S0" },
                )));
            }
        }
        let f32_result = stack.last().and_then(|v| v.as_float());
        let f64_result = stack.last().and_then(|v| v.as_double());
        if let Some(dreg) = f64_result {
            // GI-FPU-002 phase 2 (#369): an f64 result is returned in D0
            // (AAPCS-VFP). Copy via the core round-trip (`VMOV lo,hi,Dm` +
            // `VMOV D0,lo,hi` — bit-exact, no D→D move in the ArmOp set).
            // R0/R1 are dead at the epilogue of an f64-returning function
            // (the integer return registers are unused), R12 is IP scratch.
            if vfp_d_index(dreg) != Some(0) {
                instructions.push(ArmInstruction {
                    op: ArmOp::I64ReinterpretF64 {
                        rdlo: Reg::R0,
                        rdhi: Reg::R1,
                        dm: dreg,
                    },
                    source_line: None,
                });
                instructions.push(ArmInstruction {
                    op: ArmOp::F64ReinterpretI64 {
                        dd: VfpReg::D0,
                        rmlo: Reg::R0,
                        rmhi: Reg::R1,
                    },
                    source_line: None,
                });
            }
        } else if let Some(sreg) = f32_result {
            if vfp_s_index(sreg) != Some(0) {
                instructions.push(ArmInstruction {
                    op: ArmOp::I32ReinterpretF32 {
                        rd: Reg::R12,
                        sm: sreg,
                    },
                    source_line: None,
                });
                instructions.push(ArmInstruction {
                    op: ArmOp::F32ReinterpretI32 {
                        sd: VfpReg::S0,
                        rm: Reg::R12,
                    },
                    source_line: None,
                });
            }
        } else {
            let result_is_i64 = matches!(
                stack.last(),
                Some(StackVal::Reg { is_i64: true, .. })
                    | Some(StackVal::Spilled { is_i64: true, .. })
            );
            let result_reg = if stack.is_empty() {
                None
            } else {
                Some(peek_operand(
                    &mut stack,
                    &mut next_temp,
                    &mut instructions,
                    &mut spill,
                    &[],
                    wasm_ops.len(),
                )?)
            };
            if let Some(result_reg) = result_reg {
                // lo move FIRST: for a consecutive pair (hi = lo+1) the only
                // overlap case is lo == R1 (hi == R2), where r1 must be READ by
                // the lo move before the hi move WRITES it — lo-first is safe for
                // every possible pair (hi == R0 would require lo == "R-1").
                if result_reg != Reg::R0 {
                    instructions.push(ArmInstruction {
                        op: ArmOp::Mov {
                            rd: Reg::R0,
                            op2: Operand2::Reg(result_reg),
                        },
                        source_line: None,
                    });
                }
                if result_is_i64 {
                    let hi = i64_pair_hi(result_reg)?;
                    if hi != Reg::R1 {
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mov {
                                rd: Reg::R1,
                                op2: Operand2::Reg(hi),
                            },
                            source_line: None,
                        });
                    }
                }
            }
        } // GI-FPU-002: end of the integer-result `else` branch
        if layout.frame_size > 0 {
            instructions.push(ArmInstruction {
                op: ArmOp::Add {
                    rd: Reg::SP,
                    rn: Reg::SP,
                    op2: Operand2::Imm(layout.frame_size),
                },
                source_line: None,
            });
        }
        // POP {R4-R8, PC} restores registers and returns (PC = saved LR)
        instructions.push(ArmInstruction {
            op: ArmOp::Pop {
                regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::PC],
            },
            source_line: None,
        });

        // #581 defensive invariant: no reload of a never-stored spill slot may
        // leave the selector (see `assert_spill_reloads_have_stores`).
        if spill.area_reserved {
            assert_spill_reloads_have_stores(&instructions, spill.base, spill.used.len());
        }

        Ok(instructions)
    }
}
