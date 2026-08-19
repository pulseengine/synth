//! #946 tripwire — no catch-all arm regrows in `wasm_stack_effect`.
//!
//! Same class, same style as `wcet_sp_no_wildcard_946.rs` (the `may_move_sp`
//! guard): a function that claims to enumerate a space while a wildcard
//! silently answers for most of it. Here the space is `WasmOp` and the answer
//! is a (pops, pushes) stack effect feeding `infer_i64_locals` — the i64
//! local width inference. The pre-fix table said `if`/`br_if`/`br_table`
//! have no stack effect and let `_ => (0, 0)` absorb ~92 variants including
//! `memory.copy`/`memory.fill` (which pop 3). Wrong rows there are not loose
//! bounds: each stale width entry shifted the inference stack, and an i64
//! local set past one of those shapes was inferred i32, given a 4-byte slot
//! and a single-word store — an EXECUTED silent miscompile (unicorn vs
//! wasmtime: 32 / 0 where wasmtime returns 1), cross-backend because the RV32
//! selector shares the inference (#312).
//!
//! The primary tripwire is rustc itself: the match is now exhaustive with no
//! `_` arm, so a new `WasmOp` variant fails compilation until its stack
//! effect is stated. This test guards what rustc cannot:
//!
//! 1. no catch-all (`_` or bare-binding) arm ever regrows in
//!    `wasm_stack_effect`'s match — re-adding one compiles fine and silently
//!    re-absorbs every future variant;
//! 2. every `WasmOp` variant name appears in the function body, so the
//!    exhaustiveness cannot be quietly re-funneled through a renamed helper;
//! 3. the variant population is pinned, so a count drift is a visible diff
//!    here as well as in the enum.

/// Bump when adding a `WasmOp` variant — and state its stack effect in
/// `wasm_stack_effect`. Independently derived from the enum source below, so
/// this constant and the parser disagree only if one went stale.
const WASM_OP_VARIANT_COUNT: usize = 279;

const SELECTOR_SRC: &str = include_str!("../src/instruction_selector.rs");
const WASM_OP_SRC: &str = include_str!("../../synth-core/src/wasm_op.rs");

// ---------------------------------------------------------------------------
// Source-scanning helpers (the `wcet_sp_no_wildcard_946.rs` set)
// ---------------------------------------------------------------------------

/// Drop `//`-comments so brace matching and identifier scanning see only code.
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
            break;
        }
    }
    found
}

/// `needle` occurring as a whole identifier, not as a substring of a longer
/// one (`I32Add` must not be satisfied by `I32AddCarry`).
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

/// Every top-level variant name of `pub enum WasmOp`, read from the source.
fn wasm_op_variants() -> Vec<String> {
    let src = without_comments(WASM_OP_SRC);
    let body = item_after(&src, "pub enum WasmOp {");
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
    let synthetic = "fn wasm_stack_effect(op: &WasmOp) -> (usize, usize) {\n\
         \x20   match op {\n\
         \x20       I32Add => (2, 1),\n\
         \x20       _ => (0, 0),\n\
         \x20   }\n\
         }";
    let arms = catch_all_arms(synthetic, "match op {");
    assert_eq!(
        arms,
        vec!["_ => (0, 0),".to_string()],
        "the scanner must flag a bare `_` arm — otherwise this whole test is vacuous"
    );
}

#[test]
fn scanner_flags_a_bare_binding_arm() {
    let synthetic = "fn wasm_stack_effect(op: &WasmOp) -> (usize, usize) {\n\
         \x20   match op {\n\
         \x20       I32Add => (2, 1),\n\
         \x20       op if is_simd(op) => (0, 0),\n\
         \x20       other => (0, 0),\n\
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
    let synthetic = "fn f(op: &WasmOp) -> (usize, usize) {\n\
         \x20   match op {\n\
         \x20       MultiMemory { op, .. } => wasm_stack_effect(op),\n\
         \x20       I32Load { .. }\n\
         \x20       | I64Load { .. } => (1, 1),\n\
         \x20       V128Const(_) => (0, 1),\n\
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
fn wasm_op_variant_count_is_pinned() {
    let variants = wasm_op_variants();
    let mut unique = variants.clone();
    unique.sort();
    unique.dedup();
    assert_eq!(
        unique.len(),
        variants.len(),
        "duplicate variant names parsed out of `pub enum WasmOp` — the scanner is confused"
    );
    assert_eq!(
        variants.len(),
        WASM_OP_VARIANT_COUNT,
        "`WasmOp` variant count changed. State the new variant's stack effect \
         in `wasm_stack_effect` (pops/pushes audited against the spec, not \
         guessed) and bump WASM_OP_VARIANT_COUNT here."
    );
}

#[test]
fn wasm_stack_effect_has_no_catch_all_arm() {
    let src = without_comments(SELECTOR_SRC);
    let body = item_after(
        &src,
        "fn wasm_stack_effect(op: &WasmOp) -> (usize, usize) {",
    );

    // "Count the needle before AND after": a scan over nothing passes silently.
    assert!(
        body.contains("match op {"),
        "extracted `wasm_stack_effect` body has no `match op {{` — the scan \
         found the wrong thing and every assertion below would be vacuous"
    );

    let arms = catch_all_arms(&body, "match op {");
    assert!(
        arms.is_empty(),
        "#946: `wasm_stack_effect` grew a catch-all arm: {arms:?}\n\
         Its rows feed the i64 width inference — a wrong row is a SILENT \
         wrong-width local (single-word store, hi half dropped), the executed \
         br_if/if/br_table/memory.copy miscompile class. State the stack \
         effect per variant instead."
    );
}

#[test]
fn wasm_stack_effect_names_every_wasm_op_variant() {
    let src = without_comments(SELECTOR_SRC);
    let body = item_after(
        &src,
        "fn wasm_stack_effect(op: &WasmOp) -> (usize, usize) {",
    );
    let variants = wasm_op_variants();
    assert_eq!(variants.len(), WASM_OP_VARIANT_COUNT);

    let missing: Vec<&String> = variants
        .iter()
        .filter(|v| !contains_ident(&body, v))
        .collect();
    assert!(
        missing.is_empty(),
        "#946: {} `WasmOp` variant(s) are not named in `wasm_stack_effect`: {:?}\n\
         Exhaustiveness must come from naming every variant, not from a catch-all.",
        missing.len(),
        missing
    );
}

// ---------------------------------------------------------------------------
// The consumer premise: `infer_i64_locals` must keep popping call arguments
// against the REAL arg-count tables, not the per-op table (whose Call row is
// necessarily signature-blind).
// ---------------------------------------------------------------------------

#[test]
fn infer_walk_pops_call_args_from_the_tables() {
    let src = without_comments(SELECTOR_SRC);
    let body = item_after(&src, "pub fn infer_i64_locals(");
    for needle in ["func_arg_counts", "type_arg_counts"] {
        assert!(
            contains_ident(&body, needle),
            "#946: `infer_i64_locals` no longer consults `{needle}` — call \
             arguments would leave stale width entries again (the executed \
             call-args miscompile shape)."
        );
    }
}
