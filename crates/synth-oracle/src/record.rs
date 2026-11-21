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

/// The outcome of a fact's negative control.
///
/// `None` means no control exists for that fact, which is stated as such and
/// never reported as a control that was planted (REVIEW_17 finding 7).
pub type Control = Option<bool>;

/// Apply the control rule: a control that did not red fails the fact; a fact
/// with no control says so. Returns `control_failed_as_expected`.
fn control_rule(control: Control, why: &mut Vec<String>) -> bool {
    match control {
        Some(true) => true,
        Some(false) => {
            why.push("the planted negative control did not turn the fact red".to_string());
            false
        }
        None => {
            why.push("no negative control exists for this fact".to_string());
            false
        }
    }
}

/// The probe set's scope, stated where the number is.
pub const PROBE_SCOPE: &str = "probe set (21 probes, 3024 vectors): call-free, memory-free integer probes; not the spec suite, not a consumer ELF";

/// The wcet facts' scope: the probe module's functions, not the 21 judged
/// probes alone (the 22nd, `spin`, is in the sidecar and declines).
pub const WCET_SCOPE: &str = "probe set: the probe module's 22 functions, each bound checked against its worst call over 144 vector pairs; not the spec suite, not a consumer ELF";

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

/// `<target>/execution_match`. `boot_error` is set when the image did not
/// boot or broke its boot contract: nothing then executes.
#[allow(clippy::too_many_arguments)]
pub fn execution_fact(
    target: &str,
    c: &ExecCounts,
    floor: u64,
    control: Control,
    oracle: &str,
    boot_error: Option<&str>,
    extra: Value,
    evidence: &str,
) -> Fact {
    let ran = c.executed > 0;
    let mut why = Vec::new();
    if let Some(e) = boot_error {
        why.push(format!("the linked image did not boot: {e}"));
    }
    if c.executed == 0 {
        why.push("zero vectors executed".to_string());
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
    let cfe = control_rule(control, &mut why);
    let pass = ran && why.is_empty();
    Fact {
        id: format!("{target}/execution_match"),
        ran,
        pass,
        control_failed_as_expected: cfe,
        detail: with(
            detail(
                target,
                "execution_match",
                json!({
                    "scope": PROBE_SCOPE,
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
                json!({
                    "executed_floor": floor,
                    "pass_means": format!("every one of at least {floor} probe-set vectors agreed with kiln on the linked image, and the planted controls turned red; it is not a statement about the spec suite or any consumer's code"),
                    "fail_reasons": why,
                }),
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
    /// Bounded functions whose bound is BELOW the worst executed cost of one
    /// call, priced in Cortex-M4 cycles by [`crate::cycles`]: such a bound is
    /// unsound. `name: bound < cycles`.
    pub below_executed: Vec<String>,
    /// Bounded functions with no priced executed call, so their bound was
    /// not cross-checked at all (never executed, or a trace that could not
    /// be priced).
    pub unchecked: Vec<String>,
}

/// The cross-check a bound must survive: the worst priced call of the
/// function cost `executed_cycles`.
pub fn bound_below_executed(bound: u64, executed_cycles: u64) -> bool {
    bound < executed_cycles
}

/// Read a `synth-wcet-v1` sidecar. `max_cycles` maps a function name to the
/// worst executed cost of one call of it, in Cortex-M4 cycles.
pub fn summarize_wcet(sidecar: Option<&Value>, max_cycles: &BTreeMap<String, u64>) -> WcetSummary {
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
                match max_cycles.get(name) {
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

/// `<target>/wcet`. `bounded_floor` is the measured bounded-function count
/// for a target with a sound cycle model; `None` for a target without one.
pub fn wcet_fact(
    target: &str,
    s: &WcetSummary,
    bounded_floor: Option<u64>,
    control: Control,
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
    match bounded_floor {
        Some(f) if s.bounded < f => {
            why.push(format!("{} functions bounded < floor {f}", s.bounded));
        }
        Some(_) => {}
        None => {
            why.push("no bounded-function floor: no sound cycle model for this target".to_string())
        }
    }
    if !s.unchecked.is_empty() {
        why.push(format!(
            "bound never cross-checked against a priced executed call: {}",
            s.unchecked.join(", ")
        ));
    }
    if !s.below_executed.is_empty() {
        why.push(format!(
            "bound below the executed call's cost in cycles: {}",
            s.below_executed.join("; ")
        ));
    }
    let cfe = control_rule(control, &mut why);
    let pass = ran && why.is_empty();
    // A decline reason is not a number and is never rendered as one: with no
    // bounded function the value is null and the reasons sit beside it.
    let value = if s.bounded > 0 {
        json!({
            "scope": WCET_SCOPE,
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
        control_failed_as_expected: cfe,
        detail: with(
            detail(target, "wcet", value, 0, oracle),
            json!({
                "scope": WCET_SCOPE,
                "core_class": s.core_class,
                "functions": s.functions,
                "bounded": s.bounded,
                "bounded_floor": bounded_floor,
                "declines": s.declines,
                "bounds_not_cross_checked": s.unchecked,
                "pass_means": "on the probe set: at least the floor of functions bounded, and no bound below the worst executed cost of its function priced in Cortex-M4 TRM worst-case cycles (necessary, not a soundness proof); not a statement about any other code",
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
    /// Compiles stopped by the per-compile timeout (a hang is a defect).
    pub timeouts: u64,
    /// The corpus cannot be shown to be the pinned one: not a git checkout,
    /// no gitlink, or checked-out != pin. Fails the fact.
    pub corpus_mismatch: Option<String>,
}

/// `<target>/reach`.
///
/// `pass` is a REGRESSION GATE against `floor` (the count measured at the
/// commit the floor was set on), not a reach threshold: no external target
/// exists. That is written into the fact, beside the fraction.
#[allow(clippy::too_many_arguments)]
pub fn reach_fact(
    target: &str,
    c: &ReachCounts,
    expected_files: u64,
    floor: u64,
    floor_set_at: &str,
    control: Control,
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
        why.push(format!("corpus is not shown to be the pinned one: {m}"));
    }
    if c.panics > 0 {
        why.push(format!("{} compiler panics", c.panics));
    }
    if c.timeouts > 0 {
        why.push(format!("{} compiles timed out", c.timeouts));
    }
    if c.compiled < floor {
        why.push(format!("compiled {} < floor {floor}", c.compiled));
    }
    let cfe = control_rule(control, &mut why);
    let pass = ran && why.is_empty();
    let value = if c.files > 0 {
        json!({
            "fraction": (c.compiled as f64 / c.files as f64 * 10_000.0).round() / 10_000.0,
            "compiled": c.compiled,
            "corpus_size": c.files,
        })
    } else {
        Value::Null
    };
    Fact {
        id: format!("{target}/reach"),
        ran,
        pass,
        control_failed_as_expected: cfe,
        detail: with(
            detail(
                target,
                "reach",
                value,
                0,
                &format!(
                    "{oracle}; pass is a regression gate against floor {floor}, not a reach threshold"
                ),
            ),
            json!({
                "corpus": corpus,
                "compiled_floor": floor,
                "pass_means": format!("REGRESSION GATE: compiled >= floor {floor} measured at {floor_set_at}, on the pinned corpus, with no panic or timeout. It is NOT a reach threshold and says nothing about whether the fraction is good; read `value.fraction`."),
                "panics": c.panics,
                "timeouts": c.timeouts,
                "fail_reasons": why,
            }),
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

/// The field ranges of an RFC 3339 date-time whose shape already matched
/// [`date_time_re`]: month 1-12, a day that exists in that month, hour < 24,
/// minute < 60, second <= 60 (leap second), offset hours < 24.
fn date_time_in_range(x: &str) -> bool {
    let n = |r: std::ops::Range<usize>| x.get(r).and_then(|t| t.parse::<u32>().ok());
    let (Some(y), Some(mo), Some(d), Some(h), Some(mi), Some(se)) =
        (n(0..4), n(5..7), n(8..10), n(11..13), n(14..16), n(17..19))
    else {
        return false;
    };
    let leap = (y % 4 == 0 && y % 100 != 0) || y % 400 == 0;
    let dim = match mo {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if leap => 29,
        2 => 28,
        _ => return false,
    };
    let offset_ok = match x.rfind(['+', '-']).filter(|&i| i > 18) {
        Some(i) => {
            n(i + 1..i + 3).is_some_and(|oh| oh < 24) && n(i + 4..i + 6).is_some_and(|om| om < 60)
        }
        None => true,
    };
    (1..=dim).contains(&d) && h < 24 && mi < 60 && se <= 60 && offset_ok
}

/// The four fields every target carries.
pub const FIELDS: [&str; 4] = ["reach", "execution_match", "wcet", "hardware_run"];

/// What the schema cannot express (REVIEW_17 finding 8): the facts array is
/// non-empty, every requested target carries exactly the four fields, no
/// other fact and no duplicate id appears, and `ran: false` never pairs with
/// `pass: true`.
pub fn check_complete(rec: &Value, targets: &[&str]) -> Result<(), Vec<String>> {
    let mut errs = Vec::new();
    let facts = rec["facts"].as_array().cloned().unwrap_or_default();
    if facts.is_empty() {
        errs.push("the facts array is empty".to_string());
    }
    if targets.is_empty() {
        errs.push("no target requested".to_string());
    }
    let mut seen = std::collections::BTreeSet::new();
    for f in &facts {
        let id = f["id"].as_str().unwrap_or("");
        if !seen.insert(id.to_string()) {
            errs.push(format!("duplicate fact id {id:?}"));
        }
        if f["ran"] == false && f["pass"] == true {
            errs.push(format!("{id}: ran=false with pass=true"));
        }
        let known = targets
            .iter()
            .any(|t| FIELDS.iter().any(|fl| id == format!("{t}/{fl}")));
        if !known {
            errs.push(format!("{id:?} is not a requested target's field"));
        }
    }
    for t in targets {
        for fl in FIELDS {
            let id = format!("{t}/{fl}");
            if !seen.contains(&id) {
                errs.push(format!("fact {id} is missing"));
            }
        }
    }
    if errs.is_empty() { Ok(()) } else { Err(errs) }
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
                    if !date_time_re().is_match(x) || !date_time_in_range(x) {
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

    fn ok_exec() -> ExecCounts {
        ExecCounts {
            executed: 3024,
            matched: 3024,
            ..Default::default()
        }
    }

    fn rc(files: u64, compiled: u64) -> ReachCounts {
        ReachCounts {
            files,
            compiled,
            ..Default::default()
        }
    }

    fn reach(c: &ReachCounts, floor: u64, ctl: Control) -> Fact {
        reach_fact("t", c, 257, floor, "c0ffee", ctl, "o", json!(0), EV)
    }

    fn exec(c: &ExecCounts, floor: u64, ctl: Control, boot: Option<&str>) -> Fact {
        exec_t("t", c, floor, ctl, boot)
    }

    fn exec_t(t: &str, c: &ExecCounts, floor: u64, ctl: Control, boot: Option<&str>) -> Fact {
        execution_fact(t, c, floor, ctl, "o", boot, json!({}), EV)
    }

    fn side(bound: u64) -> Value {
        json!({"schema": "synth-wcet-v1", "core_class": "cortex-m4", "functions": [
            {"status": "bounded", "name": "add", "cycles": bound}]})
    }

    fn all_four(t: &str) -> Vec<Fact> {
        vec![
            exec_t(t, &ok_exec(), 3024, Some(true), None),
            reach_fact(
                t,
                &rc(257, 20),
                257,
                20,
                "c0ffee",
                Some(true),
                "o",
                json!("spec"),
                EV,
            ),
            wcet_fact(t, &WcetSummary::default(), Some(20), Some(true), "o", EV),
            hardware_fact(t, EV),
        ]
    }

    #[test]
    fn a_full_record_is_schema_valid_and_complete() {
        let r = record(all_four("cortex-m4"));
        validate_against_consumer_schema(&r).unwrap();
        check_complete(&r, &["cortex-m4"]).unwrap();
        // Every fact carries the five detail fields.
        for f in r["facts"].as_array().unwrap() {
            for k in ["target", "field", "value", "executed_vectors", "oracle"] {
                assert!(f["detail"].get(k).is_some(), "{k} missing in {f}");
            }
        }
        // The probe set is named where the number is.
        let x = &r["facts"][0];
        assert_eq!(x["detail"]["value"]["scope"], PROBE_SCOPE);
        // Reach states that pass is a regression gate.
        let rr = &r["facts"][1];
        assert!(
            rr["detail"]["oracle"]
                .as_str()
                .unwrap()
                .contains("regression gate")
        );
        assert!(
            rr["detail"]["pass_means"]
                .as_str()
                .unwrap()
                .contains("NOT a reach threshold")
        );
        assert!(rr["detail"]["value"]["fraction"].is_number());
    }

    #[test]
    fn completeness_refuses_what_the_schema_cannot_see() {
        let full = record(all_four("cortex-m4"));
        // An omitted field.
        let mut f = all_four("cortex-m4");
        f.remove(2);
        assert!(check_complete(&record(f), &["cortex-m4"]).is_err());
        // A requested target with no facts at all.
        assert!(check_complete(&full, &["cortex-m4", "cortex-m7dp"]).is_err());
        // An empty facts array.
        assert!(check_complete(&record(vec![]), &["cortex-m4"]).is_err());
        assert!(check_complete(&record(vec![]), &[]).is_err());
        // A duplicate id.
        let mut f = all_four("cortex-m4");
        f.push(hardware_fact("cortex-m4", EV));
        assert!(check_complete(&record(f), &["cortex-m4"]).is_err());
        // A fact for a target nobody asked for.
        let mut f = all_four("cortex-m4");
        f.push(hardware_fact("cortex-m0plus", EV));
        assert!(check_complete(&record(f), &["cortex-m4"]).is_err());
        // ran=false with pass=true.
        let mut v = full.clone();
        v["facts"][3]["pass"] = json!(true);
        assert!(check_complete(&v, &["cortex-m4"]).is_err());
    }

    #[test]
    fn zero_vectors_is_never_a_pass_and_never_omitted() {
        let f = exec(&ExecCounts::default(), 0, Some(true), None);
        assert!(!f.ran && !f.pass, "{f:?}");
        // Even with a floor of 0 and zero wrong: still ran=false.
        let r = record(vec![f]);
        validate_against_consumer_schema(&r).unwrap();
        assert_eq!(r["facts"].as_array().unwrap().len(), 1, "omitted");
        assert_eq!(r["facts"][0]["detail"]["executed_vectors"], 0);
        // A boot failure: nothing executed, ran=false, the reason recorded.
        let f = exec(
            &ExecCounts::default(),
            3024,
            None,
            Some("boot contract broken"),
        );
        assert!(!f.ran && !f.pass);
        // Executed but below the floor: ran, not pass.
        let few = ExecCounts {
            executed: 10,
            matched: 10,
            ..Default::default()
        };
        let f = exec(&few, 3024, Some(true), None);
        assert!(f.ran && !f.pass);
        // An empty corpus: reach did not run.
        let f = reach(&ReachCounts::default(), 0, Some(true));
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
        assert!(exec(&good, 100, Some(true), None).pass);
        for c in [
            ExecCounts {
                wrong: 1,
                ..good.clone()
            },
            ExecCounts {
                inconclusive: 1,
                ..good.clone()
            },
            ExecCounts {
                refused: 1,
                ..good.clone()
            },
        ] {
            assert!(!exec(&c, 100, Some(true), None).pass);
        }
        assert!(!exec(&good, 100, Some(false), None).pass);
        assert!(!exec(&good, 100, Some(true), Some("x")).pass);
        // No control: fails, and says there was none (never "planted").
        let f = exec(&good, 100, None, None);
        assert!(!f.pass && !f.control_failed_as_expected);
        let why = f.detail["fail_reasons"].to_string();
        assert!(
            why.contains("no negative control exists") && !why.contains("planted"),
            "{why}"
        );

        // WCET: a decline-only sidecar ran but does not pass, and its value
        // is null, never a decline string.
        let mut s = WcetSummary {
            sidecar: true,
            functions: 2,
            ..Default::default()
        };
        s.declines.insert("unsupported-core".into(), 2);
        let f = wcet_fact("cortex-m7dp", &s, None, Some(true), "o", EV);
        assert!(f.ran && !f.pass);
        assert_eq!(f.detail["value"], Value::Null);
        // CYCLES, not instructions: `add` executes 4 instructions costing 11
        // cycles (see cycles.rs). A 4-cycle bound must fail; 11 passes.
        let cost = BTreeMap::from([("add".to_string(), 11u64)]);
        let s = summarize_wcet(Some(&side(4)), &cost);
        assert_eq!(s.below_executed.len(), 1);
        assert!(!wcet_fact("cortex-m4", &s, Some(1), Some(true), "o", EV).pass);
        let s = summarize_wcet(Some(&side(11)), &cost);
        assert!(wcet_fact("cortex-m4", &s, Some(1), Some(true), "o", EV).pass);
        // The floor: 1 bounded against a floor of 20 fails.
        assert!(!wcet_fact("cortex-m4", &s, Some(20), Some(true), "o", EV).pass);
        // No floor (no sound model) never passes.
        assert!(!wcet_fact("cortex-m4", &s, None, Some(true), "o", EV).pass);
        // A bound with no priced executed call behind it is not a pass.
        let s = summarize_wcet(Some(&side(11)), &BTreeMap::new());
        assert_eq!(s.unchecked, vec!["add".to_string()]);
        assert!(!wcet_fact("cortex-m4", &s, Some(1), Some(true), "o", EV).pass);

        // Reach: a short corpus, a panic, a timeout, an unpinned corpus and
        // a drop below the floor each fail.
        let ok = rc(257, 30);
        assert!(reach(&ok, 30, Some(true)).pass);
        assert!(!reach(&rc(200, 30), 30, Some(true)).pass);
        assert!(
            !reach(
                &ReachCounts {
                    panics: 1,
                    ..ok.clone()
                },
                30,
                Some(true)
            )
            .pass
        );
        assert!(
            !reach(
                &ReachCounts {
                    timeouts: 1,
                    ..ok.clone()
                },
                30,
                Some(true)
            )
            .pass
        );
        assert!(!reach(&ok, 31, Some(true)).pass);
        let unpinned = ReachCounts {
            corpus_mismatch: Some("not a git checkout (commit unknown)".into()),
            ..ok.clone()
        };
        assert!(!reach(&unpinned, 30, Some(true)).pass);
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
        // Out-of-range fields with the right shape (REVIEW_17 finding 8).
        for t in [
            "2026-13-45T99:99:99Z",
            "2026-02-30T00:00:00Z",
            "2025-02-29T00:00:00Z",
            "2026-11-20T24:00:00Z",
            "2026-11-20T00:60:00Z",
            "2026-11-20T00:00:61Z",
            "2026-11-20T00:00:00+24:00",
        ] {
            assert!(mutate(&|v| v["generated_at"] = json!(t)), "{t}");
        }
        for t in ["2024-02-29T23:59:60Z", "2026-11-20T00:00:00.5+05:30"] {
            assert!(!mutate(&|v| v["generated_at"] = json!(t)), "{t}");
        }
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
