//! #946 tripwire — no catch-all arm regrows in `wcet_loops::may_move_sp`.
//!
//! History of the class: a function that CLAIMS to enumerate a space while a
//! wildcard silently absorbs most of it. #615 was the same shape in the A32
//! encoder ("encode as NOP for now" arms that became user-reachable silent
//! miscompiles). Here it was `writes_sp`, whose doc asserted it was
//! "exhaustive over every `rd`-carrying op the priced instruction set can
//! contain" while a single `_ => false` answered for **175 of `ArmOp`'s 222
//! variants** — including three (`I64Popcnt`, `I64Rotl`, `I64Rotr`) that
//! `op_cost` PRICES and whose encoder expansions really do emit `PUSH`/`POP`.
//!
//! `may_move_sp` is a GIVE-UP predicate: `true` declines, `false` lets the
//! analysis proceed. So `false` is the unsound direction, and a wildcard
//! `_ => false` is the worst possible default.
//!
//! This test stops the class from regrowing, structurally:
//!
//! 1. `may_move_sp` is an exhaustive `match` over `ArmOp` with NO wildcard and
//!    NO bare-identifier binding arm — a new `ArmOp` variant fails compilation
//!    of `wcet_loops.rs` until the author states how SP is affected.
//! 2. Every one of the [`ARM_OP_VARIANT_COUNT`] variant names must appear
//!    inside the function body (so an author cannot satisfy (1) by folding
//!    variants into a catch-all under a different spelling).
//! 3. The REACHABILITY premise that makes the `true` bucket behaviourally free
//!    is pinned too: `op_cost` has no wildcard, `scan_for_decline` runs BEFORE
//!    `analyze_loops`, and `analyze_loops` has exactly one call site.
//!
//! The BEHAVIOURAL half (which answers a re-added `_ => false` would flip)
//! lives in `wcet_loops.rs`'s own `#[cfg(test)] mod tests` — `may_move_sp` is
//! private, and it should stay that way.

/// Bump when adding an `ArmOp` variant — and name it in `may_move_sp`.
/// Deliberately the SAME number the #615 tripwire pins
/// (`a32_no_silent_nop_615.rs`'s `ARM_OP_VARIANT_COUNT`); the two are
/// independent readings of one enum, so they disagree only if one went stale.
const ARM_OP_VARIANT_COUNT: usize = 222;

const RULES_SRC: &str = include_str!("../../synth-synthesis/src/rules.rs");
const WCET_LOOPS_SRC: &str = include_str!("../src/wcet_loops.rs");
const WCET_SRC: &str = include_str!("../src/wcet.rs");
const WCET_COMPOSE_SRC: &str = include_str!("../src/wcet_compose.rs");
const WCET_RECURSION_SRC: &str = include_str!("../src/wcet_recursion.rs");

// ---------------------------------------------------------------------------
// Source-scanning helpers
// ---------------------------------------------------------------------------

/// Drop `//`-comments so brace matching and identifier scanning see only code.
/// (Neither scanned region contains a string literal with `//` in it; the
/// `body_is_really_there` assertions below catch it if that ever changes.)
fn without_comments(src: &str) -> String {
    src.lines()
        .map(|l| l.split("//").next().unwrap_or(l))
        .collect::<Vec<_>>()
        .join("\n")
}

/// The full text of the item introduced by `header`, brace-matched.
fn item_after(src: &str, header: &str) -> String {
    let start = src
        .find(header)
        .unwrap_or_else(|| panic!("source scan found no `{header}` — was it renamed? (#946)"));
    let rest = &src[start..];
    let (mut depth, mut opened, mut end) = (0i32, false, 0usize);
    for (i, c) in rest.char_indices() {
        match c {
            '{' => {
                depth += 1;
                opened = true;
            }
            '}' => {
                depth -= 1;
                if opened && depth == 0 {
                    end = i + 1;
                    break;
                }
            }
            _ => {}
        }
    }
    assert!(end > 0, "unbalanced braces after `{header}` (#946)");
    rest[..end].to_string()
}

/// Is this trimmed line the head of a match arm that matches ANYTHING —
/// either the `_` wildcard or a bare identifier binding (guarded or not)?
fn is_catch_all_arm(trimmed: &str) -> bool {
    let Some((head, _)) = trimmed.split_once("=>") else {
        return false;
    };
    // Strip a match guard: `op if pred(op) =>` binds everything just as
    // `op =>` does, and is how a wildcard usually sneaks back in.
    let head = head.split(" if ").next().unwrap_or(head).trim();
    if head == "_" {
        return true;
    }
    !head.is_empty()
        && head.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && head
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_lowercase() || c == '_')
}

/// Every catch-all arm at the TOP level of the `match` opened by `match_header`.
fn catch_all_arms(item: &str, match_header: &str) -> Vec<String> {
    let at = item
        .find(match_header)
        .unwrap_or_else(|| panic!("no `{match_header}` in the scanned item (#946)"));
    let rest = &item[at + match_header.len()..];
    let mut depth = 0i32;
    let mut found = Vec::new();
    for line in rest.lines() {
        let trimmed = line.trim();
        if depth == 0 && is_catch_all_arm(trimmed) {
            found.push(trimmed.to_string());
        }
        depth += line.matches('{').count() as i32;
        depth -= line.matches('}').count() as i32;
        if depth < 0 {
            break; // closed the match block
        }
    }
    found
}

/// `needle` occurring as a whole identifier, not as a substring of a longer one
/// (`Add` must not be satisfied by `I64Add` or `F32Add`).
fn contains_ident(hay: &str, needle: &str) -> bool {
    let bytes = hay.as_bytes();
    let mut from = 0usize;
    while let Some(rel) = hay[from..].find(needle) {
        let s = from + rel;
        let e = s + needle.len();
        let before_ok = s == 0 || !is_ident_byte(bytes[s - 1]);
        let after_ok = e == bytes.len() || !is_ident_byte(bytes[e]);
        if before_ok && after_ok {
            return true;
        }
        from = s + 1;
    }
    false
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// Every top-level variant name of `pub enum ArmOp`, read from the real source.
fn arm_op_variants() -> Vec<String> {
    let src = without_comments(RULES_SRC);
    let body = item_after(&src, "pub enum ArmOp {");
    let inner = &body[body.find('{').unwrap() + 1..];
    let mut depth = 0i32;
    let mut names = Vec::new();
    for line in inner.lines() {
        let trimmed = line.trim();
        if depth == 0 {
            let ident: String = trimmed
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if !ident.is_empty()
                && ident.starts_with(|c: char| c.is_ascii_uppercase())
                && trimmed[ident.len()..]
                    .trim_start()
                    .starts_with(['{', '(', ',', '}'])
            {
                names.push(ident);
            }
        }
        depth += line.matches('{').count() as i32;
        depth -= line.matches('}').count() as i32;
        if depth < 0 {
            break;
        }
    }
    names
}

// ---------------------------------------------------------------------------
// Negative controls — prove the scanner can actually go red (gate potency).
// ---------------------------------------------------------------------------

#[test]
fn scanner_flags_a_wildcard_arm() {
    let synthetic = "fn may_move_sp(op: &ArmOp) -> bool {\n\
         \x20   match op {\n\
         \x20       Add { rd, .. } => *rd == Reg::SP,\n\
         \x20       Push { .. } | Pop { .. } => true,\n\
         \x20       _ => false,\n\
         \x20   }\n\
         }";
    let arms = catch_all_arms(synthetic, "match op {");
    assert_eq!(
        arms,
        vec!["_ => false,".to_string()],
        "the scanner must flag a bare `_` arm — otherwise this whole test is vacuous"
    );
}

#[test]
fn scanner_flags_a_bare_binding_arm() {
    // The subtler regrowth: `op => …` and `op if pred(op) => …` bind EVERYTHING
    // just as `_` does. `wcet_loops.rs` legitimately uses both shapes elsewhere
    // (`resolve_toplevel_inits`), so a `_`-only scan would be bypassable.
    let synthetic = "fn may_move_sp(op: &ArmOp) -> bool {\n\
         \x20   match op {\n\
         \x20       Add { rd, .. } => *rd == Reg::SP,\n\
         \x20       op if is_odd(op) => true,\n\
         \x20       op => false,\n\
         \x20   }\n\
         }";
    let arms = catch_all_arms(synthetic, "match op {");
    assert_eq!(
        arms.len(),
        2,
        "the scanner must flag bare-identifier bindings too, guarded or not; got {arms:?}"
    );
}

#[test]
fn scanner_does_not_flag_real_variant_arms() {
    let synthetic = "fn f(op: &ArmOp) -> bool {\n\
         \x20   match op {\n\
         \x20       Umull { rdlo, rdhi, .. } => *rdlo == Reg::SP || *rdhi == Reg::SP,\n\
         \x20       I64SetCond { rd, .. } | I64Clz { rd, .. } => {\n\
         \x20           *rd == Reg::SP\n\
         \x20       }\n\
         \x20       Cmp { .. } | Nop\n\
         \x20       | Bx { .. } => false,\n\
         \x20   }\n\
         }";
    assert!(
        catch_all_arms(synthetic, "match op {").is_empty(),
        "false positive: legitimate variant arms must not be read as catch-alls"
    );
}

// ---------------------------------------------------------------------------
// The tripwire itself
// ---------------------------------------------------------------------------

#[test]
fn arm_op_variant_count_is_pinned() {
    let variants = arm_op_variants();
    let mut unique = variants.clone();
    unique.sort();
    unique.dedup();
    assert_eq!(
        unique.len(),
        variants.len(),
        "duplicate variant names parsed out of `pub enum ArmOp` — the scanner is confused"
    );
    assert_eq!(
        variants.len(),
        ARM_OP_VARIANT_COUNT,
        "`ArmOp` variant count changed. Name the new variant(s) in \
         `wcet_loops::may_move_sp` (SP effect audited, not guessed) and bump \
         ARM_OP_VARIANT_COUNT here AND in a32_no_silent_nop_615.rs."
    );
}

#[test]
fn may_move_sp_has_no_catch_all_arm() {
    let src = without_comments(WCET_LOOPS_SRC);
    let body = item_after(&src, "fn may_move_sp(op: &ArmOp) -> bool {");

    // "Count the needle before AND after": a scan over nothing passes silently.
    assert!(
        body.contains("match op {"),
        "extracted `may_move_sp` body has no `match op {{` — the scan found the \
         wrong thing and every assertion below would be vacuous"
    );

    let arms = catch_all_arms(&body, "match op {");
    assert!(
        arms.is_empty(),
        "#946: `may_move_sp` grew a catch-all arm: {arms:?}\n\
         It is a GIVE-UP predicate — a catch-all `false` silently claims \"this op \
         cannot move SP\" for every variant it absorbs, which is exactly the \
         175-of-222 hole this tripwire exists to prevent. State the SP effect per \
         variant instead (see the grouped arms and their reasons)."
    );
}

#[test]
fn may_move_sp_names_every_arm_op_variant() {
    let src = without_comments(WCET_LOOPS_SRC);
    let body = item_after(&src, "fn may_move_sp(op: &ArmOp) -> bool {");
    let variants = arm_op_variants();
    assert_eq!(variants.len(), ARM_OP_VARIANT_COUNT);

    let missing: Vec<&String> = variants
        .iter()
        .filter(|v| !contains_ident(&body, v))
        .collect();
    assert!(
        missing.is_empty(),
        "#946: {} `ArmOp` variant(s) are not named in `may_move_sp`: {:?}\n\
         Exhaustiveness must come from naming every variant, not from a catch-all.",
        missing.len(),
        missing
    );
}

// ---------------------------------------------------------------------------
// The reachability premise `may_move_sp`'s `true` bucket rests on.
//
// 145 of the 175 formerly-absorbed variants answer `true` (give up). That is
// behaviourally free ONLY because `op_cost` pre-declines them before the loop
// analysis ever runs. These three pins keep that premise true.
// ---------------------------------------------------------------------------

#[test]
fn op_cost_still_has_no_catch_all_arm() {
    let src = without_comments(WCET_SRC);
    let body = item_after(&src, "fn op_cost(op: &ArmOp) -> OpCost {");
    assert!(body.contains("match op {"), "op_cost scan found no match");
    let arms = catch_all_arms(&body, "match op {");
    assert!(
        arms.is_empty(),
        "`op_cost` grew a catch-all arm: {arms:?} — a new variant would then be \
         silently PRICED or silently declined, and `may_move_sp`'s reachability \
         argument (#946) would no longer hold."
    );
}

#[test]
fn scan_for_decline_runs_before_analyze_loops() {
    let src = without_comments(WCET_SRC);
    let body = item_after(&src, "pub fn function_wcet_intermediate(");
    let scan = body
        .find("scan_for_decline(instrs)")
        .expect("no `scan_for_decline(instrs)` call in function_wcet_intermediate (#946)");
    let loops = body
        .find("analyze_loops(instrs")
        .expect("no `analyze_loops(instrs` call in function_wcet_intermediate (#946)");
    assert!(
        scan < loops,
        "#946: `analyze_loops` now runs BEFORE `scan_for_decline`. That inverts the \
         premise `may_move_sp` documents: unpriced ops (VFP, MVE, the i64 pseudo \
         family, the off-path pseudo-ops) would reach the loop walk. They answer \
         `true` (decline), so the bound stays SOUND — but every float or vector \
         function silently stops being bounded. Re-audit `may_move_sp` before \
         reordering these."
    );
}

#[test]
fn analyze_loops_has_exactly_one_call_site() {
    let callers = [
        ("wcet.rs", WCET_SRC),
        ("wcet_compose.rs", WCET_COMPOSE_SRC),
        ("wcet_recursion.rs", WCET_RECURSION_SRC),
    ];
    let sites: Vec<(&str, usize)> = callers
        .iter()
        .map(|(name, src)| {
            (
                *name,
                without_comments(src).matches("analyze_loops(").count(),
            )
        })
        .filter(|(_, n)| *n > 0)
        .collect();
    assert_eq!(
        sites,
        vec![("wcet.rs", 1)],
        "#946: `analyze_loops` must have exactly ONE call site \
         (`wcet::function_wcet_intermediate`, gated by `scan_for_decline`). A second \
         entry point would let unpriced ops reach `may_move_sp`; found {sites:?}"
    );
}
