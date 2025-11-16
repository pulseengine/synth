//! Pattern Matching Engine for Synthesis Rules
//!
//! Matches WebAssembly instruction patterns against synthesis rules

use crate::rules::{Pattern, SynthesisRule, WasmOp};
use std::collections::HashMap;
use synth_core::Result;

/// Variable bindings from pattern matching
pub type Bindings = HashMap<String, MatchValue>;

/// Value matched from a pattern
#[derive(Debug, Clone)]
pub enum MatchValue {
    /// WebAssembly operation
    WasmOp(WasmOp),

    /// Integer constant
    I32(i32),

    /// Sequence of operations
    Sequence(Vec<WasmOp>),

    /// Variable reference
    Var(String),
}

/// Pattern matcher context
pub struct PatternMatcher {
    /// Rules to match against
    rules: Vec<SynthesisRule>,
}

impl PatternMatcher {
    /// Create a new pattern matcher
    pub fn new(rules: Vec<SynthesisRule>) -> Self {
        Self { rules }
    }

    /// Match a sequence of WASM operations against all rules
    pub fn match_sequence(&self, ops: &[WasmOp]) -> Vec<MatchResult> {
        let mut matches = Vec::new();

        for rule in &self.rules {
            if let Some(bindings) = self.match_pattern(&rule.pattern, ops, 0) {
                matches.push(MatchResult {
                    rule: rule.clone(),
                    bindings,
                    start_index: 0,
                    length: self.pattern_length(&rule.pattern),
                });
            }
        }

        // Sort by priority (highest first)
        matches.sort_by(|a, b| b.rule.priority.cmp(&a.rule.priority));

        matches
    }

    /// Match a single pattern against operations starting at index
    fn match_pattern(
        &self,
        pattern: &Pattern,
        ops: &[WasmOp],
        index: usize,
    ) -> Option<Bindings> {
        if index >= ops.len() {
            return None;
        }

        match pattern {
            Pattern::WasmInstr(expected_op) => {
                // Check if current operation matches
                if self.ops_match(expected_op, &ops[index]) {
                    Some(HashMap::new())
                } else {
                    None
                }
            }

            Pattern::Sequence(patterns) => {
                let mut bindings = HashMap::new();
                let mut current_index = index;

                for pat in patterns {
                    match self.match_pattern(pat, ops, current_index) {
                        Some(mut new_bindings) => {
                            bindings.extend(new_bindings.drain());
                            current_index += 1;
                        }
                        None => return None,
                    }
                }

                Some(bindings)
            }

            Pattern::Var(name, inner_pattern) => {
                match self.match_pattern(inner_pattern, ops, index) {
                    Some(mut bindings) => {
                        // Bind the variable
                        bindings.insert(name.clone(), MatchValue::WasmOp(ops[index].clone()));
                        Some(bindings)
                    }
                    None => None,
                }
            }

            Pattern::Any => {
                // Wildcard always matches
                let mut bindings = HashMap::new();
                bindings.insert("_any".to_string(), MatchValue::WasmOp(ops[index].clone()));
                Some(bindings)
            }
        }
    }

    /// Check if two operations match (with wildcards)
    fn ops_match(&self, expected: &WasmOp, actual: &WasmOp) -> bool {
        use WasmOp::*;

        match (expected, actual) {
            // Exact matches
            (I32Add, I32Add) => true,
            (I32Sub, I32Sub) => true,
            (I32Mul, I32Mul) => true,
            (I32And, I32And) => true,
            (I32Or, I32Or) => true,
            (I32Xor, I32Xor) => true,
            (I32Shl, I32Shl) => true,
            (I32ShrS, I32ShrS) => true,
            (I32ShrU, I32ShrU) => true,

            // Constants (wildcard for value)
            (I32Const(_), I32Const(_)) => true,

            // Memory operations (wildcard for offset/align)
            (I32Load { .. }, I32Load { .. }) => true,
            (I32Store { .. }, I32Store { .. }) => true,

            // Locals/calls (wildcard for index)
            (LocalGet(_), LocalGet(_)) => true,
            (LocalSet(_), LocalSet(_)) => true,
            (Call(_), Call(_)) => true,

            _ => false,
        }
    }

    /// Get the length (in instructions) of a pattern
    fn pattern_length(&self, pattern: &Pattern) -> usize {
        match pattern {
            Pattern::WasmInstr(_) => 1,
            Pattern::Var(_, inner) => self.pattern_length(inner),
            Pattern::Sequence(patterns) => patterns.iter().map(|p| self.pattern_length(p)).sum(),
            Pattern::Any => 1,
        }
    }
}

/// Result of pattern matching
#[derive(Debug, Clone)]
pub struct MatchResult {
    /// The rule that matched
    pub rule: SynthesisRule,

    /// Variable bindings from the match
    pub bindings: Bindings,

    /// Start index in the instruction sequence
    pub start_index: usize,

    /// Number of instructions matched
    pub length: usize,
}

/// Rule application engine
pub struct RuleApplicator {
    matcher: PatternMatcher,
}

impl RuleApplicator {
    /// Create a new rule applicator
    pub fn new(rules: Vec<SynthesisRule>) -> Self {
        Self {
            matcher: PatternMatcher::new(rules),
        }
    }

    /// Apply rules to a sequence of WASM operations
    pub fn apply_rules(&self, ops: &[WasmOp]) -> Result<Vec<WasmOp>> {
        let mut result = Vec::new();
        let mut index = 0;

        while index < ops.len() {
            // Try to match rules at current position
            let remaining = &ops[index..];
            let matches = self.matcher.match_sequence(remaining);

            if let Some(best_match) = matches.first() {
                // Apply the best matching rule
                // For now, just keep the original operations
                // In a full implementation, we would transform based on the rule
                for i in 0..best_match.length {
                    if index + i < ops.len() {
                        result.push(ops[index + i].clone());
                    }
                }
                index += best_match.length;
            } else {
                // No rule matched, keep original operation
                result.push(ops[index].clone());
                index += 1;
            }
        }

        Ok(result)
    }

    /// Apply rules and collect statistics
    pub fn apply_with_stats(&self, ops: &[WasmOp]) -> (Vec<WasmOp>, ApplyStats) {
        let mut stats = ApplyStats::default();
        let mut result = Vec::new();
        let mut index = 0;

        while index < ops.len() {
            let remaining = &ops[index..];
            let matches = self.matcher.match_sequence(remaining);

            if let Some(best_match) = matches.first() {
                stats.rules_applied += 1;
                stats.instructions_matched += best_match.length;

                for i in 0..best_match.length {
                    if index + i < ops.len() {
                        result.push(ops[index + i].clone());
                    }
                }
                index += best_match.length;
            } else {
                stats.instructions_unchanged += 1;
                result.push(ops[index].clone());
                index += 1;
            }
        }

        stats.total_instructions = ops.len();
        (result, stats)
    }
}

/// Statistics from rule application
#[derive(Debug, Default, Clone)]
pub struct ApplyStats {
    /// Total number of instructions processed
    pub total_instructions: usize,

    /// Number of rules successfully applied
    pub rules_applied: usize,

    /// Number of instructions matched by rules
    pub instructions_matched: usize,

    /// Number of instructions left unchanged
    pub instructions_unchanged: usize,
}

impl ApplyStats {
    /// Get the match rate as a percentage
    pub fn match_rate(&self) -> f64 {
        if self.total_instructions == 0 {
            0.0
        } else {
            (self.instructions_matched as f64 / self.total_instructions as f64) * 100.0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rules::{ArmOp, Cost, Operand2, Reg, Replacement, RuleDatabase};

    fn test_ops() -> Vec<WasmOp> {
        vec![
            WasmOp::I32Const(2),
            WasmOp::I32Const(3),
            WasmOp::I32Add,
            WasmOp::I32Const(4),
            WasmOp::I32Mul,
        ]
    }

    #[test]
    fn test_pattern_matcher_creation() {
        let db = RuleDatabase::new();
        let matcher = PatternMatcher::new(db.rules().to_vec());
        assert!(matcher.rules.len() == 0);
    }

    #[test]
    fn test_match_single_operation() {
        let mut rules = Vec::new();
        rules.push(SynthesisRule {
            name: "test".to_string(),
            priority: 100,
            pattern: Pattern::WasmInstr(WasmOp::I32Add),
            replacement: Replacement::Identity,
            cost: Cost {
                cycles: 1,
                code_size: 2,
                registers: 1,
            },
        });

        let matcher = PatternMatcher::new(rules);
        let ops = vec![WasmOp::I32Add];
        let matches = matcher.match_sequence(&ops);

        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].length, 1);
    }

    #[test]
    fn test_match_sequence() {
        let mut rules = Vec::new();
        rules.push(SynthesisRule {
            name: "add_sequence".to_string(),
            priority: 100,
            pattern: Pattern::Sequence(vec![
                Pattern::WasmInstr(WasmOp::I32Const(0)),
                Pattern::WasmInstr(WasmOp::I32Const(0)),
                Pattern::WasmInstr(WasmOp::I32Add),
            ]),
            replacement: Replacement::Identity,
            cost: Cost {
                cycles: 1,
                code_size: 2,
                registers: 1,
            },
        });

        let matcher = PatternMatcher::new(rules);
        let ops = test_ops();
        let matches = matcher.match_sequence(&ops);

        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].length, 3);
    }

    #[test]
    fn test_rule_applicator() {
        let db = RuleDatabase::with_standard_rules();
        let applicator = RuleApplicator::new(db.rules().to_vec());

        let ops = test_ops();
        let result = applicator.apply_rules(&ops).unwrap();

        // Should return same number of operations (no transformation yet)
        assert_eq!(result.len(), ops.len());
    }

    #[test]
    fn test_apply_with_stats() {
        let db = RuleDatabase::with_standard_rules();
        let applicator = RuleApplicator::new(db.rules().to_vec());

        let ops = test_ops();
        let (result, stats) = applicator.apply_with_stats(&ops);

        assert_eq!(stats.total_instructions, ops.len());
        assert!(stats.match_rate() >= 0.0 && stats.match_rate() <= 100.0);
    }

    #[test]
    fn test_wildcard_matching() {
        let mut rules = Vec::new();
        rules.push(SynthesisRule {
            name: "any".to_string(),
            priority: 1,
            pattern: Pattern::Any,
            replacement: Replacement::Identity,
            cost: Cost {
                cycles: 1,
                code_size: 1,
                registers: 1,
            },
        });

        let matcher = PatternMatcher::new(rules);
        let ops = vec![WasmOp::I32Add];
        let matches = matcher.match_sequence(&ops);

        assert_eq!(matches.len(), 1);
    }
}
