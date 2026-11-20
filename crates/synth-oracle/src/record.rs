//! The target record: synth's half of North Star objective O1, as the
//! `north-star-input` file pulseengine.eu consumes (seam pulseengine.eu#393).
//!
//! The SHAPE is not ours. `schema/north-star-input.schema.json` is a
//! byte-identical copy of pulseengine.eu's `data/north-star/input.schema.json`
//! (origin/main 87fc5b0, git blob b2f12f79, sha256 pinned in the tests), and
//! [`validate`] checks a record against THAT FILE, keyword by keyword, rather
//! than against a hand-written list of fields. A keyword the validator does not
//! implement is an error, so a schema change cannot be silently ignored.
//!
//! The three O1 numbers are SEPARATE facts and never summed:
//!
//! - `<target>/reach`: the share of a named corpus that compiles;
//! - `<target>/execution_match`: executed vectors on the linked image, judged
//!   against kiln;
//! - `<target>/wcet`: synth's `--emit-wcet` sidecar, cross-checked against
//!   the executed instruction counts;
//!
//! plus `<target>/hardware_run`, which synth never fills: it runs no silicon.
//!
//! The rules below are the whole of the pass/fail logic, as pure functions of
//! counts, so they are unit-tested without the engines:
//!
//! - a fact is NEVER omitted; a field with nothing behind it is `ran: false`;
//! - zero executed vectors is `ran: false`, `pass: false`, whatever the wrong
//!   count says;
//! - a fact whose negative control did NOT turn red cannot pass: a gate that
//!   cannot fail is not evidence.

use std::collections::BTreeMap;

use serde_json::{Value, json};

/// The consumer's schema, vendored byte-identically.
pub const SCHEMA: &str = include_str!("../schema/north-star-input.schema.json");

/// One fact. `detail` always carries `target`, `field`, `value`,
/// `executed_vectors` and `oracle`.
#[derive(Clone, Debug, PartialEq)]
pub struct Fact {
    pub id: String,
    pub ran: bool,
    pub pass: bool,
    pub control_failed_as_expected: bool,
    pub detail: Value,
    pub evidence: String,
}

impl Fact {
    pub fn to_json(&self) -> Value {
        json!({
            "id": self.id,
            "ran": self.ran,
            "pass": self.pass,
            "control_failed_as_expected": self.control_failed_as_expected,
            "detail": self.detail,
            "evidence": self.evidence,
        })
    }
}

fn detail(target: &str, field: &str, value: Value, executed: u64, oracle: &str) -> Value {
    json!({
        "target": target,
        "field": field,
        "value": value,
        "executed_vectors": executed,
        "oracle": oracle,
    })
}

fn with(mut d: Value, extra: Value) -> Value {
    if let (Value::Object(m), Value::Object(e)) = (&mut d, extra) {
        m.extend(e);
    }
    d
}

/// The counts of one execution leg.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExecCounts {
    /// Cases that produced a judgeable outcome on both sides.
    pub executed: u64,
    pub matched: u64,
    pub wrong: u64,
    /// Neither agreement nor a defect could be concluded (a budget, a kiln
    /// fault). Counted, and a non-zero count fails the fact.
    pub inconclusive: u64,
    /// Cases the harness refused to run (a float signature, ...).
    pub refused: u64,
}

/// `<target>/execution_match`.
#[allow(clippy::too_many_arguments)]
pub fn execution_fact(
    target: &str,
    c: &ExecCounts,
    floor: u64,
    control_red: bool,
    oracle: &str,
    linked: bool,
    extra: Value,
    evidence: &str,
) -> Fact {
    let ran = c.executed > 0;
    let mut why = Vec::new();
    if c.executed == 0 {
        why.push("zero vectors executed".to_string());
    }
    if !linked {
        why.push("not run on a linked self-contained image".to_string());
    }
    if c.executed < floor {
        why.push(format!("executed {} < floor {floor}", c.executed));
    }
    if c.wrong > 0 {
        why.push(format!("{} wrong", c.wrong));
    }
    if c.inconclusive > 0 {
        why.push(format!("{} inconclusive", c.inconclusive));
    }
    if c.refused > 0 {
        why.push(format!("{} refused by the harness", c.refused));
    }
    if !control_red {
        why.push("the planted negative control did not turn the fact red".to_string());
    }
    let pass = ran && why.is_empty();
    Fact {
        id: format!("{target}/execution_match"),
        ran,
        pass,
        control_failed_as_expected: control_red,
        detail: with(
            detail(
                target,
                "execution_match",
                json!({
                    "executed": c.executed,
                    "matched": c.matched,
                    "wrong": c.wrong,
                    "inconclusive": c.inconclusive,
                    "refused": c.refused,
                }),
                c.executed,
                oracle,
            ),
            with(
                json!({"executed_floor": floor, "linked_image": linked, "fail_reasons": why}),
                extra,
            ),
        ),
        evidence: evidence.to_string(),
    }
}

/// What the `synth-wcet-v1` sidecar said, cross-checked against execution.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct WcetSummary {
    /// The sidecar was written and parsed as `synth-wcet-v1`.
    pub sidecar: bool,
    pub core_class: String,
    pub functions: u64,
    pub bounded: u64,
    /// decline reason -> count.
    pub declines: BTreeMap<String, u64>,
    pub max_bounded_cycles: u64,
    /// Bounded functions whose bound is BELOW the instructions one call of
    /// them executed (every instruction costs at least one cycle, so such a
    /// bound is unsound). `name: bound < executed`.
    pub below_executed: Vec<String>,
    /// Bounded functions that were never executed, so their bound was not
    /// cross-checked at all.
    pub unchecked: Vec<String>,
}

/// The cross-check a bound must survive: one call of `name` executed
/// `executed` instructions, and each instruction takes at least one cycle.
pub fn bound_below_executed(cycles: u64, executed: u64) -> bool {
    cycles < executed
}

/// Read a `synth-wcet-v1` sidecar. `max_executed` maps function name to the
/// most instructions one call of it executed on the linked image.
pub fn summarize_wcet(
    sidecar: Option<&Value>,
    max_executed: &BTreeMap<String, u64>,
) -> WcetSummary {
    let mut s = WcetSummary::default();
    let Some(v) = sidecar else { return s };
    if v.get("schema").and_then(Value::as_str) != Some("synth-wcet-v1") {
        return s;
    }
    let Some(funcs) = v.get("functions").and_then(Value::as_array) else {
        return s;
    };
    s.sidecar = true;
    s.core_class = v
        .get("core_class")
        .and_then(Value::as_str)
        .unwrap_or("")
        .to_string();
    for f in funcs {
        s.functions += 1;
        let name = f.get("name").and_then(Value::as_str).unwrap_or("?");
        match f.get("status").and_then(Value::as_str) {
            Some("bounded") => {
                let cyc = f.get("cycles").and_then(Value::as_u64).unwrap_or(0);
                s.bounded += 1;
                s.max_bounded_cycles = s.max_bounded_cycles.max(cyc);
                match max_executed.get(name) {
                    Some(&n) if bound_below_executed(cyc, n) => {
                        s.below_executed.push(format!("{name}: {cyc} < {n}"));
                    }
                    Some(_) => {}
                    None => s.unchecked.push(name.to_string()),
                }
            }
            _ => {
                let r = f
                    .get("reason")
                    .and_then(Value::as_str)
                    .unwrap_or("declined without a reason");
                *s.declines.entry(r.to_string()).or_default() += 1;
            }
        }
    }
    s
}

/// `<target>/wcet`.
pub fn wcet_fact(
    target: &str,
    s: &WcetSummary,
    control_red: bool,
    oracle: &str,
    evidence: &str,
) -> Fact {
    let ran = s.sidecar;
    let mut why = Vec::new();
    if !s.sidecar {
        why.push("no synth-wcet-v1 sidecar".to_string());
    }
    if s.sidecar && s.bounded == 0 {
        let reasons: Vec<_> = s.declines.keys().cloned().collect();
        why.push(format!(
            "no function bounded (declined: {})",
            reasons.join(", ")
        ));
    }
    if !s.unchecked.is_empty() {
        why.push(format!(
            "bound never cross-checked against an executed call: {}",
            s.unchecked.join(", ")
        ));
    }
    if !s.below_executed.is_empty() {
        why.push(format!(
            "bound below the executed instruction count: {}",
            s.below_executed.join("; ")
        ));
    }
    if !control_red {
        why.push("the planted negative control did not turn the fact red".to_string());
    }
    let pass = ran && why.is_empty();
    // A decline reason is not a number and is never rendered as one: with no
    // bounded function the value is null and the reasons sit beside it.
    let value = if s.bounded > 0 {
        json!({
            "bounded_functions": s.bounded,
            "functions": s.functions,
            "max_bounded_cycles": s.max_bounded_cycles,
        })
    } else {
        Value::Null
    };
    Fact {
        id: format!("{target}/wcet"),
        ran,
        pass,
        control_failed_as_expected: control_red,
        detail: with(
            detail(target, "wcet", value, 0, oracle),
            json!({
                "core_class": s.core_class,
                "functions": s.functions,
                "bounded": s.bounded,
                "declines": s.declines,
                "bounds_not_cross_checked": s.unchecked,
                "fail_reasons": why,
            }),
        ),
        evidence: evidence.to_string(),
    }
}

/// One corpus pass.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ReachCounts {
    pub files: u64,
    pub compiled: u64,
    pub panics: u64,
    /// The corpus checked out is not the pinned one (`checked-out != pin`).
    pub corpus_mismatch: Option<String>,
}

/// `<target>/reach`.
#[allow(clippy::too_many_arguments)]
pub fn reach_fact(
    target: &str,
    c: &ReachCounts,
    expected_files: u64,
    floor: u64,
    control_red: bool,
    oracle: &str,
    corpus: Value,
    evidence: &str,
) -> Fact {
    let ran = c.files > 0;
    let mut why = Vec::new();
    if c.files == 0 {
        why.push("empty corpus: nothing compiled".to_string());
    } else if c.files != expected_files {
        why.push(format!(
            "corpus has {} files, pinned {expected_files}",
            c.files
        ));
    }
    if let Some(m) = &c.corpus_mismatch {
        why.push(format!("corpus is not the pinned one: {m}"));
    }
    if c.panics > 0 {
        why.push(format!("{} compiler panics", c.panics));
    }
    if c.compiled < floor {
        why.push(format!("compiled {} < floor {floor}", c.compiled));
    }
    if !control_red {
        why.push("the planted negative control did not turn the fact red".to_string());
    }
    let pass = ran && why.is_empty();
    let value = if c.files > 0 {
        json!({
            "compiled": c.compiled,
            "corpus_size": c.files,
            "fraction": (c.compiled as f64 / c.files as f64 * 10_000.0).round() / 10_000.0,
        })
    } else {
        Value::Null
    };
    Fact {
        id: format!("{target}/reach"),
        ran,
        pass,
        control_failed_as_expected: control_red,
        detail: with(
            detail(target, "reach", value, 0, oracle),
            json!({"corpus": corpus, "compiled_floor": floor, "panics": c.panics, "fail_reasons": why}),
        ),
        evidence: evidence.to_string(),
    }
}

/// A field that was not run this release, with the reason.
pub fn not_run_fact(target: &str, field: &str, reason: &str, evidence: &str) -> Fact {
    Fact {
        id: format!("{target}/{field}"),
        ran: false,
        pass: false,
        control_failed_as_expected: false,
        detail: with(
            detail(target, field, Value::Null, 0, "none"),
            json!({"fail_reasons": [reason]}),
        ),
        evidence: evidence.to_string(),
    }
}

/// `<target>/hardware_run`: synth runs no silicon.
pub fn hardware_fact(target: &str, evidence: &str) -> Fact {
    not_run_fact(
        target,
        "hardware_run",
        "synth runs no silicon; a hardware run is reported by its runner (jess, gale) and filled in by pulseengine.eu, never by this record",
        evidence,
    )
}

/// The objective this record feeds.
pub const OBJECTIVE: &str = "O1";

/// The consumer's asset-name rule (pulseengine.eu#394): the file is
/// `north-star-input.<objective>.json`, named after the record's own
/// `objective` field, and this check is what enforces it. `path`'s file name is checked; a mismatch, or a
/// name of any other shape, is refused.
pub fn check_file_name(path: &std::path::Path, objective: &str) -> Result<(), String> {
    let want = format!("north-star-input.{objective}.json");
    match path.file_name().and_then(|n| n.to_str()) {
        Some(n) if n == want => Ok(()),
        Some(n) => Err(format!(
            "output file name {n:?} does not match the record's objective {objective:?}: the consumer requires {want:?} (pulseengine.eu#394)"
        )),
        None => Err(format!("output path {} has no file name", path.display())),
    }
}

/// The whole input file.
pub struct Record {
    pub version: String,
    pub generated_at: String,
    pub generator_version: String,
    pub facts: Vec<Fact>,
    pub not_measured: Vec<String>,
}

impl Record {
    pub fn to_json(&self) -> Value {
        json!({
            "schema_version": 1,
            "objective": OBJECTIVE,
            "repo": "pulseengine/synth",
            "version": self.version,
            "generated_at": self.generated_at,
            "generator": {"tool": "synth-oracle target-record", "version": self.generator_version},
            "facts": self.facts.iter().map(Fact::to_json).collect::<Vec<_>>(),
            "not_measured": self.not_measured,
        })
    }
}

/// RFC 3339 UTC timestamp for `secs` since the Unix epoch.
pub fn rfc3339_utc(secs: u64) -> String {
    let days = (secs / 86_400) as i64;
    let rem = secs % 86_400;
    // Howard Hinnant's civil_from_days.
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = yoe + era * 400 + i64::from(m <= 2);
    format!(
        "{y:04}-{m:02}-{d:02}T{:02}:{:02}:{:02}Z",
        rem / 3600,
        rem % 3600 / 60,
        rem % 60
    )
}

// ------------------------------------------------------------- validator --

/// Validate `instance` against `schema` (a JSON Schema using only the keywords
/// below). Every error is returned, with its JSON pointer.
pub fn validate(instance: &Value, schema: &Value) -> Result<(), Vec<String>> {
    let mut errs = Vec::new();
    check(instance, schema, "", &mut errs);
    if errs.is_empty() { Ok(()) } else { Err(errs) }
}

/// Validate against the vendored consumer schema.
pub fn validate_against_consumer_schema(instance: &Value) -> Result<(), Vec<String>> {
    let schema: Value = serde_json::from_str(SCHEMA).map_err(|e| vec![format!("schema: {e}")])?;
    validate(instance, &schema)
}

fn date_time_re() -> &'static regex::Regex {
    static RE: std::sync::OnceLock<regex::Regex> = std::sync::OnceLock::new();
    RE.get_or_init(|| {
        regex::Regex::new(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(\.\d+)?(Z|[+-]\d{2}:\d{2})$")
            .expect("static regex")
    })
}

const ANNOTATIONS: &[&str] = &["$comment", "description", "title", "$schema", "$id"];

fn type_ok(v: &Value, t: &str) -> Option<bool> {
    Some(match t {
        "object" => v.is_object(),
        "array" => v.is_array(),
        "string" => v.is_string(),
        "boolean" => v.is_boolean(),
        "number" => v.is_number(),
        "integer" => v.is_i64() || v.is_u64(),
        "null" => v.is_null(),
        _ => return None,
    })
}

fn check(v: &Value, s: &Value, at: &str, errs: &mut Vec<String>) {
    let Some(s) = s.as_object() else {
        errs.push(format!("{at}: schema node is not an object"));
        return;
    };
    let ptr = if at.is_empty() { "/" } else { at };
    for (k, kv) in s {
        match k.as_str() {
            k if ANNOTATIONS.contains(&k) => {}
            "type" => match kv.as_str().and_then(|t| type_ok(v, t)) {
                Some(true) => {}
                Some(false) => errs.push(format!("{ptr}: not of type {kv}")),
                None => errs.push(format!("{ptr}: unsupported type keyword {kv}")),
            },
            "const" => {
                if v != kv {
                    errs.push(format!("{ptr}: must equal {kv}"));
                }
            }
            "enum" => {
                if !kv.as_array().is_some_and(|a| a.contains(v)) {
                    errs.push(format!("{ptr}: not one of {kv}"));
                }
            }
            "pattern" => {
                if let (Some(p), Some(x)) = (kv.as_str(), v.as_str()) {
                    match regex::Regex::new(p) {
                        Ok(re) if re.is_match(x) => {}
                        Ok(_) => errs.push(format!("{ptr}: {x:?} does not match {p}")),
                        Err(e) => errs.push(format!("{ptr}: bad pattern {p}: {e}")),
                    }
                }
            }
            "format" => {
                if let (Some("date-time"), Some(x)) = (kv.as_str(), v.as_str()) {
                    if !date_time_re().is_match(x) {
                        errs.push(format!("{ptr}: {x:?} is not an RFC 3339 date-time"));
                    }
                } else if kv.as_str() != Some("date-time") {
                    errs.push(format!("{ptr}: unsupported format {kv}"));
                }
            }
            "required" => {
                if let (Some(req), Some(o)) = (kv.as_array(), v.as_object()) {
                    for r in req.iter().filter_map(Value::as_str) {
                        if !o.contains_key(r) {
                            errs.push(format!("{ptr}: missing required property {r:?}"));
                        }
                    }
                }
            }
            "properties" => {
                if let (Some(props), Some(o)) = (kv.as_object(), v.as_object()) {
                    for (name, sub) in props {
                        if let Some(x) = o.get(name) {
                            check(x, sub, &format!("{at}/{name}"), errs);
                        }
                    }
                }
            }
            "additionalProperties" => {
                if let Some(o) = v.as_object() {
                    let props = s.get("properties").and_then(Value::as_object);
                    for name in o.keys() {
                        if props.is_some_and(|p| p.contains_key(name)) {
                            continue;
                        }
                        match kv {
                            Value::Bool(false) => errs
                                .push(format!("{ptr}: additional property {name:?} not allowed")),
                            Value::Bool(true) => {}
                            sub => check(&o[name], sub, &format!("{at}/{name}"), errs),
                        }
                    }
                }
            }
            "items" => {
                if let Some(a) = v.as_array() {
                    for (i, x) in a.iter().enumerate() {
                        check(x, kv, &format!("{at}/{i}"), errs);
                    }
                }
            }
            other => errs.push(format!(
                "{ptr}: schema keyword {other:?} is not implemented by this validator"
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EV: &str = "local";

    fn record(facts: Vec<Fact>) -> Value {
        Record {
            version: "0.92.0".into(),
            generated_at: rfc3339_utc(1_795_000_000),
            generator_version: "0.92.0".into(),
            facts,
            not_measured: vec!["x".into()],
        }
        .to_json()
    }

    #[test]
    fn vendored_schema_is_the_consumers_bytes() {
        use sha2::{Digest, Sha256};
        let h = Sha256::digest(SCHEMA.as_bytes());
        let hex: String = h.iter().map(|b| format!("{b:02x}")).collect();
        // pulseengine.eu origin/main 87fc5b0 (pulseengine.eu#394),
        // data/north-star/input.schema.json
        // (git blob b2f12f794d15fb10fc804bc3ccdc4866a3d036ba).
        assert_eq!(
            hex,
            "b97c33abfb45f6be9303b9b5bed67993f062acf2d431386a4f337bbcd9c363fb"
        );
    }

    #[test]
    fn a_full_record_is_schema_valid() {
        let ok = ExecCounts {
            executed: 3024,
            matched: 3024,
            ..Default::default()
        };
        let facts = vec![
            execution_fact("cortex-m4", &ok, 3024, true, "o", true, json!({}), EV),
            reach_fact(
                "cortex-m4",
                &ReachCounts {
                    files: 257,
                    compiled: 20,
                    ..Default::default()
                },
                257,
                20,
                true,
                "o",
                json!("spec"),
                EV,
            ),
            wcet_fact("cortex-m4", &WcetSummary::default(), true, "o", EV),
            hardware_fact("cortex-m4", EV),
        ];
        let r = record(facts);
        validate_against_consumer_schema(&r).unwrap();
        // Every fact carries the five detail fields.
        for f in r["facts"].as_array().unwrap() {
            for k in ["target", "field", "value", "executed_vectors", "oracle"] {
                assert!(f["detail"].get(k).is_some(), "{k} missing in {f}");
            }
        }
    }

    #[test]
    fn zero_vectors_is_never_a_pass_and_never_omitted() {
        let zero = ExecCounts::default();
        let f = execution_fact("cortex-m4", &zero, 0, true, "o", true, json!({}), EV);
        assert!(!f.ran && !f.pass, "{f:?}");
        // Even with a floor of 0 and zero wrong: still ran=false.
        let r = record(vec![f]);
        validate_against_consumer_schema(&r).unwrap();
        assert_eq!(r["facts"].as_array().unwrap().len(), 1, "omitted");
        assert_eq!(r["facts"][0]["detail"]["executed_vectors"], 0);
        // Executed but below the floor: ran, not pass.
        let few = ExecCounts {
            executed: 10,
            matched: 10,
            ..Default::default()
        };
        let f = execution_fact("cortex-m4", &few, 3024, true, "o", true, json!({}), EV);
        assert!(f.ran && !f.pass);
        // An empty corpus: reach did not run.
        let f = reach_fact(
            "cortex-m4",
            &ReachCounts::default(),
            257,
            0,
            true,
            "o",
            json!("c"),
            EV,
        );
        assert!(!f.ran && !f.pass);
        assert_eq!(f.detail["value"], Value::Null);
    }

    #[test]
    fn each_fail_rule_fails_the_fact() {
        let good = ExecCounts {
            executed: 100,
            matched: 100,
            ..Default::default()
        };
        assert!(execution_fact("t", &good, 100, true, "o", true, json!({}), EV).pass);
        for (c, ctl, linked) in [
            (
                ExecCounts {
                    wrong: 1,
                    ..good.clone()
                },
                true,
                true,
            ),
            (
                ExecCounts {
                    inconclusive: 1,
                    ..good.clone()
                },
                true,
                true,
            ),
            (
                ExecCounts {
                    refused: 1,
                    ..good.clone()
                },
                true,
                true,
            ),
            (good.clone(), false, true),
            (good.clone(), true, false),
        ] {
            assert!(!execution_fact("t", &c, 100, ctl, "o", linked, json!({}), EV).pass);
        }
        // WCET: a decline-only sidecar ran but does not pass, and its value
        // is null, never a decline string.
        let mut s = WcetSummary {
            sidecar: true,
            functions: 2,
            ..Default::default()
        };
        s.declines.insert("unsupported-core".into(), 2);
        let f = wcet_fact("cortex-m7dp", &s, true, "o", EV);
        assert!(f.ran && !f.pass);
        assert_eq!(f.detail["value"], Value::Null);
        // A bound below the executed count fails.
        let side = json!({"schema": "synth-wcet-v1", "core_class": "cortex-m4", "functions": [
            {"status": "bounded", "name": "add", "cycles": 3}]});
        let exe = BTreeMap::from([("add".to_string(), 4u64)]);
        let s = summarize_wcet(Some(&side), &exe);
        assert_eq!(s.below_executed.len(), 1);
        assert!(!wcet_fact("cortex-m4", &s, true, "o", EV).pass);
        let exe = BTreeMap::from([("add".to_string(), 3u64)]);
        let s = summarize_wcet(Some(&side), &exe);
        assert!(wcet_fact("cortex-m4", &s, true, "o", EV).pass);
        // Reach: a short corpus and a panic each fail.
        let rc = ReachCounts {
            files: 257,
            compiled: 30,
            ..Default::default()
        };
        assert!(reach_fact("t", &rc, 257, 30, true, "o", json!(0), EV).pass);
        let short = ReachCounts {
            files: 200,
            ..rc.clone()
        };
        assert!(!reach_fact("t", &short, 257, 30, true, "o", json!(0), EV).pass);
        let panic = ReachCounts {
            panics: 1,
            ..rc.clone()
        };
        assert!(!reach_fact("t", &panic, 257, 30, true, "o", json!(0), EV).pass);
        assert!(!reach_fact("t", &rc, 257, 31, true, "o", json!(0), EV).pass);
        let moved = ReachCounts {
            corpus_mismatch: Some("a != b".into()),
            ..rc.clone()
        };
        assert!(!reach_fact("t", &moved, 257, 30, true, "o", json!(0), EV).pass);
        // A bound with no executed call behind it is not a pass.
        let s = summarize_wcet(Some(&side), &BTreeMap::new());
        assert_eq!(s.unchecked, vec!["add".to_string()]);
        assert!(!wcet_fact("cortex-m4", &s, true, "o", EV).pass);
    }

    #[test]
    fn validator_rejects_what_the_schema_rejects() {
        let base = record(vec![hardware_fact("cortex-m4", EV)]);
        validate_against_consumer_schema(&base).unwrap();
        let mutate = |f: &dyn Fn(&mut Value)| {
            let mut v = base.clone();
            f(&mut v);
            validate_against_consumer_schema(&v).is_err()
        };
        assert!(mutate(&|v| {
            v.as_object_mut().unwrap().remove("not_measured");
        }));
        assert!(mutate(&|v| v["schema_version"] = json!(2)));
        assert!(mutate(&|v| v["objective"] = json!("O9")));
        assert!(mutate(&|v| v["repo"] = json!("someone/synth")));
        assert!(mutate(&|v| v["version"] = json!("0.92")));
        assert!(mutate(&|v| v["generated_at"] = json!("2026-11-20")));
        assert!(mutate(&|v| v["extra"] = json!(1)));
        assert!(mutate(&|v| v["facts"][0]["ran"] = json!("false")));
        assert!(mutate(&|v| {
            v["facts"][0].as_object_mut().unwrap().remove("pass");
        }));
        assert!(mutate(&|v| v["facts"][0]["surprise"] = json!(true)));
        assert!(mutate(&|v| v["generator"]["extra"] = json!("x")));
        // An unimplemented keyword in the schema is an error, not a pass.
        let schema = json!({"type": "object", "minProperties": 1});
        assert!(validate(&json!({"a": 1}), &schema).is_err());
    }

    #[test]
    fn file_name_must_match_the_objective() {
        use std::path::Path;
        assert!(check_file_name(Path::new("out/north-star-input.O1.json"), "O1").is_ok());
        for bad in [
            "north-star-input.json",
            "north-star-input.O5.json",
            "north-star-input.o1.json",
            "target-record.json",
            "north-star-input.O1.json.tmp",
        ] {
            assert!(check_file_name(Path::new(bad), "O1").is_err(), "{bad}");
        }
        assert!(check_file_name(Path::new("/"), "O1").is_err());
        // The record's own objective field is the one named.
        let r = record(vec![]);
        assert_eq!(r["objective"], OBJECTIVE);
    }

    #[test]
    fn rfc3339() {
        assert_eq!(rfc3339_utc(0), "1970-01-01T00:00:00Z");
        assert_eq!(rfc3339_utc(951_782_400), "2000-02-29T00:00:00Z");
        assert_eq!(rfc3339_utc(1_795_132_800), "2026-11-20T00:00:00Z");
    }
}
