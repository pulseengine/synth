//! VCR-SEL-001 increment 1 (#242) — the Rocq-discharged selector rule DSL.
//!
//! Scope: `docs/design/vcr-sel-001-first-increment.md`. This module is the
//! **checked-in rule table**: a declarative `op → parameterized ARM sequence`
//! (registers as variables, side conditions explicit) for the pilot-measured
//! tier-A i32 ALU class (`add/sub/mul/and/or/xor`, 6/6 auto-discharge) plus one
//! tier-B scratch-using shape (`i32.rotl`), included deliberately so the rule
//! format carries a scratch non-aliasing side condition from day one.
//!
//! The table is turned into plain Rust lowering functions by
//! [`generate_lowering_source`] and the output is **committed to the tree** at
//! [`generated`] (reviewable diffs, no build-time codegen). `select_default`
//! keeps dispatch ownership: a migrated arm delegates to the generated rule
//! behind `SYNTH_SEL_DSL` (default OFF), so OFF ≡ baseline byte-identical by
//! construction.
//!
//! Every rule carries a **1:1 Rocq obligation**: rule `rule_i32_add` ↔ theorem
//! `rule_i32_add_correct` in `coq/Synth/Synth/VcrSelRules.v` (T1, discharged by
//! `synth_binop_proof_poly`; the scratch shape by the pilot's stepped proof with
//! the explicit `rs <> rn` hypothesis). Coverage is gated twice:
//!
//! - cargo side: [`tests::coq_coverage_every_rule_has_a_qed_theorem`] reads the
//!   `.v` file and fails if a rule lacks its `Theorem <name>_correct` or the
//!   file contains `Admitted`/`admit.`;
//! - bazel side: `//coq:vcr_sel_rules_coverage` (part of the
//!   `//coq:verify_proofs` suite CI runs) checks `coq/vcr_sel_rules.manifest`
//!   against the `.v`, and [`tests::manifest_matches_rule_table`] pins the
//!   manifest to this table — a rule without a Qed cannot merge.

use synth_core::WasmOp;

pub mod generated;

/// A register **variable** in a rule template — the rule is universally
/// quantified over the concrete assignment (VCR-RA picks the registers; the
/// Rocq theorem holds for every assignment satisfying the side conditions).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegVar {
    /// Destination register.
    Rd,
    /// First (left) operand register.
    Rn,
    /// Second (right) operand register.
    Rm,
    /// Scratch register (tier-B shapes only).
    Rs,
}

impl RegVar {
    /// The Rust parameter name this variable binds to in a generated lowering
    /// function (also the Coq binder name in the paired theorem).
    pub const fn rust_name(self) -> &'static str {
        match self {
            RegVar::Rd => "rd",
            RegVar::Rn => "rn",
            RegVar::Rm => "rm",
            RegVar::Rs => "rs",
        }
    }
}

/// An explicit side condition a rule's register assignment must satisfy.
///
/// This is the constraint the DSL must carry and feed to the allocator
/// (VCR-RA-001): e.g. `i32.rotl`'s scratch is written by instruction 1 before
/// the value register is read by instruction 2, so `rs` must not alias `rn` —
/// in the fixed-register proof that was a `discriminate` on `R0 <> R2`; under
/// register generalization it is a real hypothesis of the theorem, and here a
/// real runtime guard in the generated function (Ok-or-Err, never silent).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SideCondition {
    /// The two register variables must be assigned distinct registers.
    NotAlias(RegVar, RegVar),
}

/// One ARM instruction template over register variables. Shapes cover exactly
/// what the increment-1 rules need; new op classes add shapes alongside their
/// rules (+ theorems).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TemplateOp {
    /// `ArmOp::Add { rd, rn, op2: Reg(rm) }`
    AddReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::Sub { rd, rn, op2: Reg(rm) }`
    SubReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::Mul { rd, rn, rm }`
    Mul { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::And { rd, rn, op2: Reg(rm) }`
    AndReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::Orr { rd, rn, op2: Reg(rm) }`
    OrrReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::Eor { rd, rn, op2: Reg(rm) }`
    EorReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::Rsb { rd, rn, imm }` — `rd = imm - rn`
    RsbImm { rd: RegVar, rn: RegVar, imm: u32 },
    /// `ArmOp::RorReg { rd, rn, rm }`
    RorReg { rd: RegVar, rn: RegVar, rm: RegVar },
}

/// One declarative lowering rule: `op → parameterized ARM sequence`.
#[derive(Debug, Clone, PartialEq)]
pub struct SelRule {
    /// Rule name. 1:1 with the Rocq theorem `<name>_correct` in
    /// `coq/Synth/Synth/VcrSelRules.v` and with the generated Rust function
    /// `generated::<name>`.
    pub name: &'static str,
    /// The WASM op this rule lowers.
    pub op: WasmOp,
    /// Register parameters of the generated function, in signature order.
    pub params: &'static [RegVar],
    /// Explicit side conditions (checked at runtime in the generated function,
    /// hypotheses of the Rocq theorem).
    pub side_conditions: &'static [SideCondition],
    /// The emitted instruction sequence, over register variables.
    pub seq: &'static [TemplateOp],
    /// One-line human description for the generated function's doc comment.
    pub doc: &'static str,
}

impl SelRule {
    /// The 1:1 paired Rocq theorem name.
    pub fn theorem(&self) -> String {
        format!("{}_correct", self.name)
    }
}

use RegVar::{Rd, Rm, Rn, Rs};

/// The increment-1 rule table: the tier-A six + tier-B `i32.rotl`.
///
/// Sequences are copied byte-for-byte from `select_default`'s hand-written
/// arms — increment 1 migrates *structure, never bytes* (mirror-pinned by
/// `sel_dsl_mirror_pin_generated_rules_match_handwritten_arms_242`).
pub const RULES: &[SelRule] = &[
    SelRule {
        name: "rule_i32_add",
        op: WasmOp::I32Add,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::AddReg {
            rd: Rd,
            rn: Rn,
            rm: Rm,
        }],
        doc: "`i32.add`: rd = rn + rm",
    },
    SelRule {
        name: "rule_i32_sub",
        op: WasmOp::I32Sub,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::SubReg {
            rd: Rd,
            rn: Rn,
            rm: Rm,
        }],
        doc: "`i32.sub`: rd = rn - rm",
    },
    SelRule {
        name: "rule_i32_mul",
        op: WasmOp::I32Mul,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::Mul {
            rd: Rd,
            rn: Rn,
            rm: Rm,
        }],
        doc: "`i32.mul`: rd = rn * rm",
    },
    SelRule {
        name: "rule_i32_and",
        op: WasmOp::I32And,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::AndReg {
            rd: Rd,
            rn: Rn,
            rm: Rm,
        }],
        doc: "`i32.and`: rd = rn & rm",
    },
    SelRule {
        name: "rule_i32_or",
        op: WasmOp::I32Or,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::OrrReg {
            rd: Rd,
            rn: Rn,
            rm: Rm,
        }],
        doc: "`i32.or`: rd = rn | rm",
    },
    SelRule {
        name: "rule_i32_xor",
        op: WasmOp::I32Xor,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::EorReg {
            rd: Rd,
            rn: Rn,
            rm: Rm,
        }],
        doc: "`i32.xor`: rd = rn ^ rm",
    },
    SelRule {
        name: "rule_i32_rotl",
        op: WasmOp::I32Rotl,
        params: &[Rd, Rn, Rm, Rs],
        side_conditions: &[SideCondition::NotAlias(Rs, Rn)],
        seq: &[
            TemplateOp::RsbImm {
                rd: Rs,
                rn: Rm,
                imm: 32,
            },
            TemplateOp::RorReg {
                rd: Rd,
                rn: Rn,
                rm: Rs,
            },
        ],
        doc: "`i32.rotl`: rotate left by rm = rotate right by (32 - rm), via scratch rs",
    },
];

/// Render a struct field, using field-init shorthand when the bound variable
/// name matches the field name (keeps the generated file rustfmt/clippy-clean).
fn field(name: &str, var: RegVar) -> String {
    if name == var.rust_name() {
        name.to_string()
    } else {
        format!("{name}: {}", var.rust_name())
    }
}

/// Render an `ArmOp` data-processing constructor whose second operand is
/// `op2: Operand2::Reg(..)`, in the exploded multi-line form rustfmt settles
/// on for these literals (the generated file must be rustfmt-stable so
/// `cargo fmt` never drifts it away from the pinned generator output).
fn dp_reg_expr(op: &str, rd: RegVar, rn: RegVar, rm: RegVar, indent: usize) -> String {
    let ind = " ".repeat(indent);
    let fld = " ".repeat(indent + 4);
    format!(
        "ArmOp::{op} {{\n{fld}{},\n{fld}{},\n{fld}op2: Operand2::Reg({}),\n{ind}}}",
        field("rd", rd),
        field("rn", rn),
        rm.rust_name()
    )
}

/// Render one instruction template as an `ArmOp` constructor expression,
/// starting at column `indent` (continuation lines are indented relative to
/// it). Shapes mirror what rustfmt emits for the equivalent hand-written
/// literal, so the committed file is a rustfmt fixpoint.
fn template_expr(t: &TemplateOp, indent: usize) -> String {
    match *t {
        TemplateOp::AddReg { rd, rn, rm } => dp_reg_expr("Add", rd, rn, rm, indent),
        TemplateOp::SubReg { rd, rn, rm } => dp_reg_expr("Sub", rd, rn, rm, indent),
        TemplateOp::AndReg { rd, rn, rm } => dp_reg_expr("And", rd, rn, rm, indent),
        TemplateOp::OrrReg { rd, rn, rm } => dp_reg_expr("Orr", rd, rn, rm, indent),
        TemplateOp::EorReg { rd, rn, rm } => dp_reg_expr("Eor", rd, rn, rm, indent),
        TemplateOp::Mul { rd, rn, rm } => format!(
            "ArmOp::Mul {{ {}, {}, {} }}",
            field("rd", rd),
            field("rn", rn),
            field("rm", rm)
        ),
        TemplateOp::RsbImm { rd, rn, imm } => {
            let ind = " ".repeat(indent);
            let fld = " ".repeat(indent + 4);
            format!(
                "ArmOp::Rsb {{\n{fld}{},\n{fld}{},\n{fld}imm: {imm},\n{ind}}}",
                field("rd", rd),
                field("rn", rn)
            )
        }
        TemplateOp::RorReg { rd, rn, rm } => format!(
            "ArmOp::RorReg {{ {}, {}, {} }}",
            field("rd", rd),
            field("rn", rn),
            field("rm", rm)
        ),
    }
}

/// Generate the Rust source of `generated.rs` from [`RULES`].
///
/// The output is committed to the tree and pinned by
/// [`tests::generated_lowering_is_up_to_date`]; regenerate with
/// `SYNTH_SEL_DSL_REGEN=1 cargo test -p synth-synthesis sel_dsl`.
pub fn generate_lowering_source() -> String {
    let mut out = String::new();
    out.push_str(
        "//! GENERATED FILE — DO NOT EDIT BY HAND.\n\
         //!\n\
         //! Emitted by `crate::sel_dsl::generate_lowering_source()` from the declarative\n\
         //! rule table [`crate::sel_dsl::RULES`] (VCR-SEL-001 increment 1, #242,\n\
         //! `docs/design/vcr-sel-001-first-increment.md`). Pinned up-to-date by the\n\
         //! `generated_lowering_is_up_to_date` test; regenerate with\n\
         //! `SYNTH_SEL_DSL_REGEN=1 cargo test -p synth-synthesis sel_dsl`.\n\
         //!\n\
         //! Every function here carries a 1:1 Rocq T1 theorem in\n\
         //! `coq/Synth/Synth/VcrSelRules.v` (all Qed — coverage-gated by\n\
         //! `//coq:vcr_sel_rules_coverage`): the emitted sequence computes the op's\n\
         //! result in `rd` for EVERY register assignment satisfying the stated side\n\
         //! conditions.\n\n\
         use crate::rules::{ArmOp, Operand2, Reg};\n",
    );

    for rule in RULES {
        let params: Vec<String> = rule
            .params
            .iter()
            .map(|p| format!("{}: Reg", p.rust_name()))
            .collect();
        let params = params.join(", ");

        out.push('\n');
        out.push_str(&format!("/// {}\n", rule.doc));
        out.push_str("///\n");
        out.push_str(&format!(
            "/// Rocq obligation: `Synth.Synth.VcrSelRules.{}` (Qed).\n",
            rule.theorem()
        ));
        for sc in rule.side_conditions {
            let SideCondition::NotAlias(a, b) = sc;
            out.push_str(&format!(
                "///\n/// Side condition: `{}` must not alias `{}` (hypothesis of the theorem;\n\
                 /// violation is a loud `Err`, never a silent misassemble).\n",
                a.rust_name(),
                b.rust_name()
            ));
        }
        if rule.side_conditions.is_empty() {
            out.push_str(&format!(
                "pub fn {}({params}) -> Vec<ArmOp> {{\n",
                rule.name
            ));
        } else {
            out.push_str(&format!(
                "pub fn {}({params}) -> Result<Vec<ArmOp>, &'static str> {{\n",
                rule.name
            ));
            for sc in rule.side_conditions {
                let SideCondition::NotAlias(a, b) = sc;
                out.push_str(&format!(
                    "    if {a} == {b} {{\n        return Err(\"{name}: side condition violated: \
                     scratch {a} must not alias {b}\");\n    }}\n",
                    a = a.rust_name(),
                    b = b.rust_name(),
                    name = rule.name
                ));
            }
        }
        let (open, close) = if rule.side_conditions.is_empty() {
            ("vec![", "]")
        } else {
            ("Ok(vec![", "])")
        };
        if rule.seq.len() == 1 {
            out.push_str(&format!(
                "    {open}{}{close}\n",
                template_expr(&rule.seq[0], 4)
            ));
        } else {
            out.push_str(&format!("    {open}\n"));
            for t in rule.seq {
                out.push_str(&format!("        {},\n", template_expr(t, 8)));
            }
            out.push_str(&format!("    {close}\n"));
        }
        out.push_str("}\n");
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn crate_root() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    }

    /// The generated file is the committed output of the rule table — any edit
    /// to either without regenerating fails here. Regenerate with
    /// `SYNTH_SEL_DSL_REGEN=1 cargo test -p synth-synthesis sel_dsl`.
    #[test]
    fn generated_lowering_is_up_to_date() {
        let path = crate_root().join("src/sel_dsl/generated.rs");
        let expected = generate_lowering_source();
        if std::env::var("SYNTH_SEL_DSL_REGEN").is_ok() {
            std::fs::write(&path, &expected).expect("write generated.rs");
        }
        let actual = std::fs::read_to_string(&path).expect("read generated.rs");
        assert_eq!(
            actual, expected,
            "src/sel_dsl/generated.rs is stale relative to the RULES table — \
             regenerate with SYNTH_SEL_DSL_REGEN=1 cargo test -p synth-synthesis sel_dsl"
        );
    }

    /// Rule names are unique and follow the `rule_` prefix the 1:1 theorem
    /// naming convention builds on.
    #[test]
    fn rule_names_unique_and_theorem_named() {
        let mut seen = std::collections::HashSet::new();
        for rule in RULES {
            assert!(
                rule.name.starts_with("rule_"),
                "{}: rule names must start with rule_",
                rule.name
            );
            assert!(seen.insert(rule.name), "duplicate rule name {}", rule.name);
            assert_eq!(rule.theorem(), format!("{}_correct", rule.name));
        }
    }

    /// Cargo-side half of the coverage gate: every rule has its 1:1 Rocq
    /// theorem in `coq/Synth/Synth/VcrSelRules.v`, and the file carries no
    /// `Admitted`/`admit.` — so (with the file compiling under
    /// `//coq:verify_proofs`) every rule theorem is Qed.
    #[test]
    fn coq_coverage_every_rule_has_a_qed_theorem() {
        let v_path = crate_root().join("../../coq/Synth/Synth/VcrSelRules.v");
        let v = std::fs::read_to_string(&v_path)
            .unwrap_or_else(|e| panic!("read {}: {e}", v_path.display()));
        for rule in RULES {
            assert!(
                v.contains(&format!("Definition {} ", rule.name)),
                "rule {} has no Definition in VcrSelRules.v",
                rule.name
            );
            assert!(
                v.contains(&format!("Theorem {} ", rule.theorem())),
                "rule {} lacks its theorem {} in VcrSelRules.v — a rule without \
                 a Qed cannot merge",
                rule.name,
                rule.theorem()
            );
        }
        assert!(
            !v.contains("Admitted") && !v.contains("admit."),
            "VcrSelRules.v contains Admitted/admit — every rule theorem must be Qed"
        );
    }

    /// The bazel-side coverage gate (`//coq:vcr_sel_rules_coverage`) reads
    /// `coq/vcr_sel_rules.manifest`; pin the manifest to this table so the
    /// Rust-table ↔ manifest ↔ Coq-theorem chain is closed.
    #[test]
    fn manifest_matches_rule_table() {
        let m_path = crate_root().join("../../coq/vcr_sel_rules.manifest");
        let manifest = std::fs::read_to_string(&m_path)
            .unwrap_or_else(|e| panic!("read {}: {e}", m_path.display()));
        let listed: Vec<&str> = manifest
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
            .collect();
        let expected: Vec<&str> = RULES.iter().map(|r| r.name).collect();
        assert_eq!(
            listed, expected,
            "coq/vcr_sel_rules.manifest is out of sync with sel_dsl::RULES"
        );
    }

    /// The tier-B side condition is a loud Err, never a silent misassemble.
    #[test]
    fn rotl_side_condition_is_enforced() {
        use crate::rules::Reg;
        // Violating assignment: scratch aliases the value register.
        assert!(generated::rule_i32_rotl(Reg::R0, Reg::R1, Reg::R2, Reg::R1).is_err());
        // Satisfying assignment lowers to RSB scratch + ROR.
        let ops = generated::rule_i32_rotl(Reg::R0, Reg::R1, Reg::R2, Reg::R3).unwrap();
        assert_eq!(ops.len(), 2);
    }
}
