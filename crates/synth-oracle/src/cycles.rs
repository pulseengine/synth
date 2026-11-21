//! Price an executed Thumb-2 trace in Cortex-M4 worst-case CYCLES.
//!
//! The target record cross-checks each `--emit-wcet` bound against what one
//! executed call of its function cost. Comparing a bound in cycles with an
//! instruction COUNT lets an unsound bound through (a 4-cycle bound for a
//! 4-instruction function that takes 11 cycles; REVIEW_17 finding 2), so the
//! trace is priced here, INDEPENDENTLY of synth's own cycle table: this file
//! does not read `synth_core::wcet`.
//!
//! The model is ARM DDI 0439 (Cortex-M4 TRM) table 3-1 at its worst case,
//! zero wait states, pipeline refill P = 3, taking the Cortex-M3 figure where
//! the M3 is slower (long multiply 5, MLA/MLS 2), divide 12. It is the same
//! table REVIEW_17's independent Python check used (`cyc.py`); the record's
//! per-function figures were compared against that script's output.
//!
//! unicorn's code hook fires neither for `IT` nor for a condition-failed
//! instruction inside an IT block. Each of those still costs one cycle, so a
//! short forward gap after a non-branch instruction is priced one cycle per
//! instruction in it.
//!
//! An instruction that transferred control but is not modelled as a branch
//! is an ERROR, never priced as 1: the checker fails closed.

/// Pipeline refill.
pub const P: u64 = 3;

/// How long a forward gap after a non-branch instruction may be and still be
/// read as skipped IT-block instructions (an IT block is at most 4 x 4 bytes
/// minus the instruction that ran; REVIEW_17's script uses 12).
const MAX_IT_GAP: u64 = 12;

/// The instruction width from its first halfword.
pub fn width(hw1: u16) -> u64 {
    if matches!(hw1 >> 11, 0b11101..=0b11111) {
        4
    } else {
        2
    }
}

/// What an instruction is, for pricing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    /// B (conditional or not), CBZ/CBNZ: `1 + P` taken, `1` not.
    CondBranch,
    /// BL, BX, BLX: always `1 + P`.
    Branch,
    /// TBB/TBH: `2 + P`.
    TableBranch,
    /// LDM/POP: `1 + n`, `+ P` when PC is loaded.
    LoadMultiple { n: u64, pc: bool },
    /// STM/PUSH: `1 + n`.
    StoreMultiple { n: u64 },
    /// LDRD/STRD, exclusives: `3`.
    Dual,
    /// Single load: `2`, `+ P` when the destination is PC.
    Load { pc: bool },
    /// Single store: `2`.
    Store,
    /// SDIV/UDIV: `12`.
    Divide,
    /// SMULL/UMULL/SMLAL/UMLAL: `5`.
    LongMultiply,
    /// MLA/MLS: `2`.
    MulAcc,
    /// MOV/ADD (high-register form) with PC as destination: `1 + P`.
    WritesPc,
    /// Anything else: `1`.
    Simple,
}

impl Class {
    /// A branch-like instruction, after which a forward jump is a taken
    /// branch, never an IT gap.
    fn transfers(self) -> bool {
        matches!(
            self,
            Class::CondBranch
                | Class::Branch
                | Class::TableBranch
                | Class::WritesPc
                | Class::LoadMultiple { pc: true, .. }
                | Class::Load { pc: true }
        )
    }

    pub fn cost(self, taken: bool) -> u64 {
        match self {
            Class::CondBranch => {
                if taken {
                    1 + P
                } else {
                    1
                }
            }
            Class::Branch | Class::WritesPc => 1 + P,
            Class::TableBranch => 2 + P,
            Class::LoadMultiple { n, pc } => 1 + n + if pc { P } else { 0 },
            Class::StoreMultiple { n } => 1 + n,
            Class::Dual => 3,
            Class::Load { pc } => 2 + if pc { P } else { 0 },
            Class::Store => 2,
            Class::Divide => 12,
            Class::LongMultiply => 5,
            Class::MulAcc => 2,
            Class::Simple => 1,
        }
    }
}

/// Classify one instruction (`hw2` is ignored for a 16-bit one).
pub fn classify(hw1: u16, hw2: u16) -> Class {
    if width(hw1) == 2 {
        let low8 = u64::from((hw1 & 0xFF).count_ones());
        return match hw1 {
            // B<c> T1 (0xDE = UDF, 0xDF = SVC are not branches).
            h if h & 0xF000 == 0xD000 && (h >> 8) & 0xF < 0xE => Class::CondBranch,
            // B T2.
            h if h & 0xF800 == 0xE000 => Class::CondBranch,
            // CBZ / CBNZ.
            h if h & 0xF500 == 0xB100 => Class::CondBranch,
            // BX / BLX (register).
            h if h & 0xFF00 == 0x4700 => Class::Branch,
            // POP.
            h if h & 0xFE00 == 0xBC00 => Class::LoadMultiple {
                n: low8 + u64::from((h >> 8) & 1),
                pc: h & 0x100 != 0,
            },
            // PUSH.
            h if h & 0xFE00 == 0xB400 => Class::StoreMultiple {
                n: low8 + u64::from((h >> 8) & 1),
            },
            // LDM T1 / STM T1.
            h if h & 0xF800 == 0xC800 => Class::LoadMultiple { n: low8, pc: false },
            h if h & 0xF800 == 0xC000 => Class::StoreMultiple { n: low8 },
            // LDR (literal) T1.
            h if h & 0xF800 == 0x4800 => Class::Load { pc: false },
            // Load/store register offset: bit 11 set is a load for opB 011..111
            // except STRH/STRB; opB = bits 11:9. 000 STR, 001 STRH, 010 STRB,
            // 011 LDRSB, 1xx loads.
            h if h & 0xF000 == 0x5000 => {
                if (h >> 9) & 7 <= 2 {
                    Class::Store
                } else {
                    Class::Load { pc: false }
                }
            }
            // Load/store immediate (word/byte, halfword, SP-relative): L = bit 11.
            h if (0x6000..0xA000).contains(&h) => {
                if h & 0x0800 != 0 {
                    Class::Load { pc: false }
                } else {
                    Class::Store
                }
            }
            // ADD / MOV (high registers) writing PC: Rd = DN:Rdn.
            h if (h & 0xFF00 == 0x4400 || h & 0xFF00 == 0x4600)
                && (((h >> 4) & 0x8) | (h & 0x7)) == 15 =>
            {
                Class::WritesPc
            }
            _ => Class::Simple,
        };
    }
    // 32-bit.
    if hw1 & 0xF800 == 0xF000 && hw2 & 0x8000 != 0 {
        // Branches and miscellaneous control.
        return match hw2 & 0xD000 {
            0xD000 | 0xC000 => Class::Branch, // BL (BLX imm does not exist on M)
            0x9000 => Class::CondBranch,      // B T4
            0x8000 if (hw1 >> 7) & 0x7 != 0x7 => Class::CondBranch, // B<c> T3
            _ => Class::Simple,               // MSR/MRS/hints/UDF.W
        };
    }
    if hw1 & 0xFFF0 == 0xE8D0 && hw2 & 0xFFE0 == 0xF000 {
        return Class::TableBranch;
    }
    if hw1 & 0xFE40 == 0xE840 {
        return Class::Dual;
    }
    if hw1 & 0xFE00 == 0xE800 && matches!((hw1 >> 7) & 3, 1 | 2) {
        let n = u64::from(hw2.count_ones());
        return if hw1 & 0x10 != 0 {
            Class::LoadMultiple {
                n,
                pc: hw2 & 0x8000 != 0,
            }
        } else {
            Class::StoreMultiple { n }
        };
    }
    if hw1 & 0xFE00 == 0xF800 {
        return if hw1 & 0x10 != 0 {
            Class::Load {
                pc: hw2 >> 12 == 15,
            }
        } else {
            Class::Store
        };
    }
    if hw1 & 0xFF80 == 0xFB80 {
        return match (hw1 >> 4) & 7 {
            1 | 3 => Class::Divide,
            _ => Class::LongMultiply,
        };
    }
    if hw1 & 0xFFF0 == 0xFB00 {
        // MUL / MLA / MLS: Ra = hw2[15:12], op2 = hw2[5:4].
        return match ((hw2 >> 4) & 3, hw2 >> 12) {
            (0, 15) => Class::Simple,
            (0, _) | (1, _) => Class::MulAcc,
            _ => Class::Simple,
        };
    }
    Class::Simple
}

/// Price one executed trace. `trace` is what the code hook saw, in order
/// (address, size); `end_pc` is where execution stopped; `fetch(addr)` reads
/// the halfword at `addr`. `trapped` marks a run whose last traced
/// instruction faulted (it did not transfer control).
///
/// Returns `(cycles, instructions)`, the instruction count INCLUDING the ones
/// the hook did not report, or an error naming an unmodelled transfer.
pub fn price(
    trace: &[(u64, u32)],
    end_pc: u64,
    trapped: bool,
    fetch: &dyn Fn(u64) -> Option<u16>,
) -> Result<(u64, u64), String> {
    let mut cycles = 0u64;
    let mut insns = 0u64;
    for (k, &(addr, size)) in trace.iter().enumerate() {
        let size = u64::from(size);
        let hw1 = fetch(addr).ok_or_else(|| format!("no code at {addr:#x}"))?;
        let hw2 = if size == 4 {
            fetch(addr + 2).ok_or_else(|| format!("no code at {:#x}", addr + 2))?
        } else {
            0
        };
        let class = classify(hw1, hw2);
        let next = trace.get(k + 1).map_or(end_pc, |t| t.0);
        let last = k + 1 == trace.len();
        let mut taken = next != addr + size && !(trapped && last);
        if taken && !class.transfers() && next > addr + size && next <= addr + size + MAX_IT_GAP {
            // Skipped IT / condition-failed instructions: one cycle each.
            let mut a = addr + size;
            while a < next {
                let h = fetch(a).ok_or_else(|| format!("no code at {a:#x}"))?;
                a += width(h);
                cycles += 1;
                insns += 1;
            }
            if a != next {
                return Err(format!(
                    "gap {:#x}..{next:#x} is not whole instructions",
                    addr + size
                ));
            }
            taken = false;
        }
        if taken && !class.transfers() {
            return Err(format!(
                "unmodelled control transfer at {addr:#x} ({hw1:04x} {hw2:04x}) to {next:#x}"
            ));
        }
        cycles += class.cost(taken);
        insns += 1;
    }
    Ok((cycles, insns))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    fn code(words: &[(u64, u16)]) -> BTreeMap<u64, u16> {
        words.iter().copied().collect()
    }

    #[test]
    fn classifies_what_synth_emits() {
        assert_eq!(classify(0xB580, 0), Class::StoreMultiple { n: 2 }); // push {r7, lr}
        assert_eq!(classify(0xBD80, 0), Class::LoadMultiple { n: 2, pc: true }); // pop {r7, pc}
        assert_eq!(classify(0x4770, 0), Class::Branch); // bx lr
        assert_eq!(classify(0xD001, 0), Class::CondBranch); // beq
        assert_eq!(classify(0xDE00, 0), Class::Simple); // udf
        assert_eq!(classify(0xE7FE, 0), Class::CondBranch); // b .
        assert_eq!(classify(0xB118, 0), Class::CondBranch); // cbz
        assert_eq!(classify(0x4801, 0), Class::Load { pc: false }); // ldr r0, [pc, #4]
        assert_eq!(classify(0x6808, 0), Class::Load { pc: false }); // ldr r0, [r1]
        assert_eq!(classify(0x6008, 0), Class::Store); // str r0, [r1]
        assert_eq!(classify(0x9000, 0), Class::Store); // str r0, [sp]
        assert_eq!(classify(0x4687, 0), Class::WritesPc); // mov pc, r0
        assert_eq!(classify(0xBF08, 0), Class::Simple); // it eq
        assert_eq!(classify(0xFBB0, 0xF0F1), Class::Divide); // udiv r0, r0, r1
        assert_eq!(classify(0xFB90, 0xF0F1), Class::Divide); // sdiv
        assert_eq!(classify(0xFBA0, 0x0101), Class::LongMultiply); // umull
        assert_eq!(classify(0xFB00, 0xF001), Class::Simple); // mul
        assert_eq!(classify(0xFB00, 0x2001), Class::MulAcc); // mla
        assert_eq!(classify(0xFB00, 0x2011), Class::MulAcc); // mls
        assert_eq!(classify(0xF000, 0xF800), Class::Branch); // bl
        assert_eq!(classify(0xF000, 0xB800), Class::CondBranch); // b.w
        assert_eq!(classify(0xF000, 0x8000), Class::CondBranch); // beq.w
        assert_eq!(classify(0xF7F0, 0xA000), Class::Simple); // udf.w
        assert_eq!(
            classify(0xE8BD, 0x8010),
            Class::LoadMultiple { n: 2, pc: true }
        ); // pop.w {r4, pc}
        assert_eq!(classify(0xE92D, 0x4010), Class::StoreMultiple { n: 2 }); // push.w {r4, lr}
        assert_eq!(classify(0xE9D0, 0x2300), Class::Dual); // ldrd
        assert_eq!(classify(0xE8DF, 0xF000), Class::TableBranch); // tbb [pc, r0]
        assert_eq!(classify(0xF8D0, 0x0004), Class::Load { pc: false }); // ldr.w r0, [r0, #4]
        assert_eq!(classify(0xF8DF, 0xF004), Class::Load { pc: true }); // ldr.w pc, [pc, #4]
        assert_eq!(classify(0xF8C0, 0x1004), Class::Store); // str.w
        assert_eq!(classify(0xF240, 0x0A00), Class::Simple); // movw
    }

    #[test]
    fn prices_a_call_in_cycles_not_instructions() {
        // push {r7,lr}; adds r0,r0,r1; mov r7,r7; pop {r7,pc} returning to 0x1000:
        // 3 + 1 + 1 + (3 + P) = 11 cycles, 4 instructions.
        let c = code(&[
            (0x100, 0xB580),
            (0x102, 0x1840),
            (0x104, 0x463F),
            (0x106, 0xBD80),
        ]);
        let trace = [(0x100, 2), (0x102, 2), (0x104, 2), (0x106, 2)];
        let r = price(&trace, 0x1000, false, &|a| c.get(&a).copied()).unwrap();
        assert_eq!(r, (11, 4));
        // So a 4-cycle bound (= the instruction count) is below the cost.
        assert!(4 < r.0);
    }

    #[test]
    fn counts_what_the_hook_skips() {
        // cmp; ite eq; moveq; movne; bx lr. The hook reports cmp, then the
        // instruction that ran (movne), then bx: `it` and `moveq` are skipped.
        let c = code(&[
            (0x100, 0x4288), // cmp r0, r1
            (0x102, 0xBF0C), // ite eq
            (0x104, 0x2001), // moveq r0, #1
            (0x106, 0x2000), // movne r0, #0
            (0x108, 0x4770), // bx lr
        ]);
        let trace = [(0x100, 2), (0x106, 2), (0x108, 2)];
        let r = price(&trace, 0x1000, false, &|a| c.get(&a).copied()).unwrap();
        // cmp 1 + it 1 + moveq 1 + movne 1 + bx 4 = 8; 5 instructions.
        assert_eq!(r, (8, 5));
    }

    #[test]
    fn an_unmodelled_transfer_is_an_error_never_one_cycle() {
        let c = code(&[(0x100, 0x2000)]); // movs r0, #0 "jumping" far
        let trace = [(0x100, 2)];
        assert!(price(&trace, 0x2000, false, &|a| c.get(&a).copied()).is_err());
        // A trapped last instruction did not transfer control.
        let c = code(&[(0x100, 0xDE00)]);
        assert_eq!(
            price(&[(0x100, 2)], 0x100, true, &|a| c.get(&a).copied()).unwrap(),
            (1, 1)
        );
    }
}
