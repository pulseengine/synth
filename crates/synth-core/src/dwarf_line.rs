//! VCR-DBG-001 step 3 — compose the source-line table (the join half).
//!
//! The DWARF Tier-1 bridge maps an ARM text offset back to a source `file:line`
//! through three established facts:
//!   1. each ARM instruction carries `source_line` = the wasm OP INDEX
//!      (`ArmInstruction.source_line`);
//!   2. step 1 (`FunctionOps.op_offsets`) maps op-index → the wasm code BYTE
//!      OFFSET (module-relative);
//!   3. step 2 parses the input wasm's `.debug_line` → (code-section-relative
//!      address → `file:line`) rows.
//!
//! This module is the join for the wasm half — **op-index → source line** —
//! which step 4 (emit) composes with the ARM layout (ARM-text-offset → op-index
//! is just `source_line`). It is pure plain-data (no gimli, no backend): the
//! caller parses the rows and supplies them, so the module is Bazel-clean and
//! unwired (frozen-safe) until the emitter consumes it.
//!
//! The crux it encodes (validated on `scripts/repro/dwarf_coherent.wasm`,
//! VCR-DBG-001 step-3 fixture): `op_offsets` are MODULE-relative while DWARF
//! addresses are CODE-section-relative, and they differ by a single constant —
//! the code section's payload start. So normalization is one subtraction:
//! `dwarf_addr = op_offset - code_base`.

/// One `.debug_line` row: a code-section-relative address and its source line.
/// `file` is an opaque caller-supplied id (e.g. an index into the line
/// program's file table) so this stays gimli-free.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LineRow {
    /// Code-section-relative address (the DWARF-for-wasm address space).
    pub addr: u32,
    pub line: u32,
    pub file: u32,
}

/// A resolved source location for a wasm op.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceLoc {
    pub line: u32,
    pub file: u32,
}

/// Map each wasm op (by its module-relative `op_offsets` byte offset) to a
/// source location, by normalizing into the code-section-relative DWARF address
/// space (`op_offset - code_base`) and taking the covering line-table row (the
/// last row whose address is ≤ the op's address — standard line-table lookup).
///
/// Returns one entry per `op_offsets` element (parallel to a function's ops).
/// `None` where the op precedes `code_base` (shouldn't happen for real code) or
/// no row covers it (an op before the first line-table address).
pub fn op_offsets_to_source(
    op_offsets: &[u32],
    code_base: u32,
    rows: &[LineRow],
) -> Vec<Option<SourceLoc>> {
    let mut sorted: Vec<LineRow> = rows.to_vec();
    sorted.sort_by_key(|r| r.addr);
    op_offsets
        .iter()
        .map(|&off| {
            let a = off.checked_sub(code_base)?;
            // Largest row addr ≤ a (the line in effect at address a).
            sorted
                .iter()
                .rev()
                .find(|r| r.addr <= a)
                .map(|r| SourceLoc {
                    line: r.line,
                    file: r.file,
                })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn covering_row_lookup() {
        // code_base 100; rows at code-rel 0→line10, 8→line11, 20→line12.
        let rows = [
            LineRow {
                addr: 0,
                line: 10,
                file: 1,
            },
            LineRow {
                addr: 8,
                line: 11,
                file: 1,
            },
            LineRow {
                addr: 20,
                line: 12,
                file: 1,
            },
        ];
        // ops at module 100 (→0), 104 (→4), 108 (→8), 130 (→30).
        let got = op_offsets_to_source(&[100, 104, 108, 130], 100, &rows);
        assert_eq!(got[0].map(|s| s.line), Some(10)); // addr 0  → row 0
        assert_eq!(got[1].map(|s| s.line), Some(10)); // addr 4  → still row 0
        assert_eq!(got[2].map(|s| s.line), Some(11)); // addr 8  → row 8
        assert_eq!(got[3].map(|s| s.line), Some(12)); // addr 30 → row 20 (last ≤)
    }

    #[test]
    fn op_before_first_row_is_none() {
        let rows = [LineRow {
            addr: 8,
            line: 11,
            file: 1,
        }];
        // op at module 100 → code-rel 0, before the first row (addr 8).
        let got = op_offsets_to_source(&[100], 100, &rows);
        assert_eq!(got[0], None);
    }

    #[test]
    fn op_before_code_base_is_none() {
        let rows = [LineRow {
            addr: 0,
            line: 1,
            file: 1,
        }];
        let got = op_offsets_to_source(&[50], 100, &rows);
        assert_eq!(got[0], None);
    }
}
