//! The REFERENCE: run a wasm export on kiln, PulseEngine's interpreter.
//!
//! Loading follows kiln's own spec driver
//! (`kiln-build-core/src/wast_execution.rs`, `WastEngine::load_module`, v0.7.3)
//! minus the spectest and multi-module linking, which a single-module oracle
//! has no use for. Validation is wasmparser's, run first, because kiln's
//! validator lives in its build tool rather than its runtime.
//!
//! Imports resolve EXACTLY: every function import must be named in
//! [`Imports`], and a module with any other import (memory, table, global,
//! tag) is refused before it runs. kiln itself returns default zeros for a
//! function import nothing serves on some call paths, so the harness refuses
//! the module rather than trusting that.

use std::sync::{Arc, Mutex};

use kiln_decoder::decoder::decode_module;
use kiln_foundation::values::{FloatBits32, FloatBits64, Value};
use kiln_runtime::module::{ExportKind, Module};
use kiln_runtime::module_instance::ModuleInstance;
use kiln_runtime::stackless::StacklessEngine;

use crate::compare::{RefOutcome, TrapClass};
use crate::value::WasmValue;

/// kiln's fuel-exhaustion message (engine.rs, the per-instruction charge).
/// Exhaustion is reported through `Error::runtime_trap`, the SAME constructor
/// and code as a real trap, so this message is what separates them.
const FUEL_EXHAUSTED: &str = "fuel exhausted: execution exceeded the configured instruction budget";

/// kiln interprets with deep native recursion in debug builds; its own driver
/// runs on a large-stack thread, and so does this one.
const KILN_STACK: usize = 256 << 20;

/// A host function. `Err` traps the guest ([`TrapClass::HostTrap`]).
pub type HostFn = Arc<dyn Fn(&[WasmValue]) -> Result<Vec<WasmValue>, String> + Send + Sync>;

/// One recorded host call, e.g. one MMIO access.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HostCall {
    pub module: String,
    pub field: String,
    pub args: Vec<WasmValue>,
    /// `None` when the host function trapped.
    pub results: Option<Vec<WasmValue>>,
}

/// The exact import resolver: `(module, field)` -> host function.
#[derive(Clone, Default)]
pub struct Imports {
    funcs: Vec<(String, String, HostFn)>,
}

impl Imports {
    pub fn new() -> Self {
        Self::default()
    }

    /// Serve `module::field` with `f`.
    pub fn func<F>(mut self, module: &str, field: &str, f: F) -> Self
    where
        F: Fn(&[WasmValue]) -> Result<Vec<WasmValue>, String> + Send + Sync + 'static,
    {
        self.funcs.push((module.into(), field.into(), Arc::new(f)));
        self
    }

    /// Serve `module::field` with a function that only returns `results`. Its
    /// calls are still logged, so this is an MMIO-write trace point.
    pub fn trace(self, module: &str, field: &str, results: Vec<WasmValue>) -> Self {
        self.func(module, field, move |_| Ok(results.clone()))
    }

    fn get(&self, module: &str, field: &str) -> Option<&HostFn> {
        self.funcs
            .iter()
            .find(|(m, f, _)| m == module && f == field)
            .map(|(_, _, h)| h)
    }
}

struct Handler {
    imports: Imports,
    log: Arc<Mutex<Vec<HostCall>>>,
}

impl kiln_foundation::HostImportHandler for Handler {
    fn resolves(&self, module: &str, function: &str) -> bool {
        self.imports.get(module, function).is_some()
    }

    fn call_import(
        &mut self,
        module: &str,
        function: &str,
        args: &[Value],
        _memory: Option<&dyn kiln_foundation::traits::MemoryAccessor>,
    ) -> kiln_error::Result<Vec<Value>> {
        let Some(f) = self.imports.get(module, function) else {
            return Err(kiln_error::Error::runtime_trap(
                "synth-oracle: unresolved import",
            ));
        };
        let args: Vec<WasmValue> = match args.iter().map(from_kiln).collect() {
            Ok(a) => a,
            Err(_) => {
                return Err(kiln_error::Error::runtime_trap(
                    "synth-oracle: host argument of an unsupported type",
                ));
            }
        };
        let r = f(&args);
        self.log.lock().expect("host log poisoned").push(HostCall {
            module: module.into(),
            field: function.into(),
            args,
            results: r.as_ref().ok().cloned(),
        });
        match r {
            Ok(v) => Ok(v.into_iter().map(to_kiln).collect()),
            Err(_) => Err(kiln_error::Error::runtime_trap(HOST_TRAP)),
        }
    }
}

const HOST_TRAP: &str = "synth-oracle: host function trapped";

fn to_kiln(v: WasmValue) -> Value {
    match v {
        WasmValue::I32(x) => Value::I32(x as i32),
        WasmValue::I64(x) => Value::I64(x as i64),
        WasmValue::F32(x) => Value::F32(FloatBits32(x)),
        WasmValue::F64(x) => Value::F64(FloatBits64(x)),
    }
}

fn from_kiln(v: &Value) -> Result<WasmValue, String> {
    match v {
        Value::I32(x) => Ok(WasmValue::I32(*x as u32)),
        Value::I64(x) => Ok(WasmValue::I64(*x as u64)),
        Value::F32(x) => Ok(WasmValue::F32(x.0)),
        Value::F64(x) => Ok(WasmValue::F64(x.0)),
        other => Err(format!("unsupported kiln value {other:?}")),
    }
}

/// The module could not be run at all (as opposed to running and trapping).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RefError {
    Invalid(String),
    UnresolvedImport { module: String, field: String },
    Unsupported(String),
    Instantiate(String),
    NoExport(String),
}

/// One reference run.
#[derive(Clone, Debug)]
pub struct RefRun {
    pub outcome: RefOutcome,
    /// Every host call, in order.
    pub calls: Vec<HostCall>,
    /// Fuel consumed.
    pub fuel_used: u64,
}

struct ImportScan {
    imported_funcs: u32,
}

fn scan_imports(wasm: &[u8], imports: &Imports) -> Result<ImportScan, RefError> {
    use wasmparser::{Parser, Payload, TypeRef};
    let mut result_counts: Vec<usize> = Vec::new();
    let mut imported_funcs = 0;
    for p in Parser::new(0).parse_all(wasm) {
        match p.map_err(|e| RefError::Invalid(e.to_string()))? {
            Payload::TypeSection(r) => {
                for rec in r {
                    for sub in rec
                        .map_err(|e| RefError::Invalid(e.to_string()))?
                        .into_types()
                    {
                        result_counts.push(match &sub.composite_type.inner {
                            wasmparser::CompositeInnerType::Func(ft) => ft.results().len(),
                            _ => 0,
                        });
                    }
                }
            }
            Payload::ImportSection(r) => {
                for imp in r.into_imports() {
                    let imp = imp.map_err(|e| RefError::Invalid(e.to_string()))?;
                    match imp.ty {
                        TypeRef::Func(t) => {
                            if imports.get(imp.module, imp.name).is_none() {
                                return Err(RefError::UnresolvedImport {
                                    module: imp.module.into(),
                                    field: imp.name.into(),
                                });
                            }
                            // kiln's host path pushes only the FIRST result.
                            if result_counts.get(t as usize).copied().unwrap_or(0) > 1 {
                                return Err(RefError::Unsupported(format!(
                                    "import {}::{} returns more than one value",
                                    imp.module, imp.name
                                )));
                            }
                            imported_funcs += 1;
                        }
                        other => {
                            return Err(RefError::Unsupported(format!(
                                "non-function import {}::{} ({other:?})",
                                imp.module, imp.name
                            )));
                        }
                    }
                }
            }
            _ => {}
        }
    }
    Ok(ImportScan { imported_funcs })
}

thread_local! {
    /// The kiln worker's cache of CONVERTED modules, keyed by their bytes.
    /// `Module::from_kiln_module` is the expensive step (measured ~12 ms per
    /// call in a Linux VM, against microseconds for decode, instantiation and
    /// execution), and a `Module` is immutable: every call still gets a fresh
    /// engine and a fresh `ModuleInstance`, so no state crosses calls.
    static MODULES: std::cell::RefCell<std::collections::HashMap<Vec<u8>, Arc<Module>>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
}

fn converted_module(wasm: &[u8]) -> kiln_error::Result<Arc<Module>> {
    if let Some(m) = MODULES.with(|c| c.borrow().get(wasm).cloned()) {
        return Ok(m);
    }
    let km = decode_module(wasm)?;
    let m = Arc::new(*Module::from_kiln_module(&km)?);
    MODULES.with(|c| {
        let mut c = c.borrow_mut();
        if c.len() >= 64 {
            c.clear();
        }
        c.insert(wasm.to_vec(), Arc::clone(&m));
    });
    Ok(m)
}

/// Load and instantiate. The start function, if any, runs under `fuel`, so a
/// looping start function ends as a refusal instead of hanging.
fn load(
    engine: &mut StacklessEngine,
    wasm: &[u8],
    fuel: u64,
) -> Result<(Arc<Module>, usize), RefError> {
    let e = |stage: &str, err: kiln_error::Error| RefError::Instantiate(format!("{stage}: {err}"));
    let module = converted_module(wasm).map_err(|x| e("decode/convert", x))?;
    let id = engine.peek_next_instance_id();
    let inst =
        Arc::new(ModuleInstance::new(Arc::clone(&module), id).map_err(|x| e("instance", x))?);
    inst.populate_memories_from_module()
        .map_err(|x| e("memories", x))?;
    inst.populate_globals_from_module()
        .map_err(|x| e("globals", x))?;
    inst.reevaluate_deferred_globals()
        .map_err(|x| e("globals", x))?;
    inst.populate_tables_from_module()
        .map_err(|x| e("tables", x))?;
    inst.evaluate_table_init_exprs()
        .map_err(|x| e("tables", x))?;
    inst.initialize_dropped_segments()
        .map_err(|x| e("segments", x))?;
    let idx = engine
        .set_current_module(Arc::clone(&inst))
        .map_err(|x| e("register", x))?;
    inst.initialize_element_segments()
        .map_err(|x| e("elements", x))?;
    inst.initialize_data_segments().map_err(|x| e("data", x))?;
    if let Some(start) = module.start {
        engine.reset_call_depth();
        engine.set_fuel(fuel);
        engine
            .execute(idx, start as usize, vec![])
            .map_err(|x| e("start function", x))?;
    }
    Ok((module, idx))
}

fn classify(err: &kiln_error::Error) -> RefOutcome {
    let msg = err.message;
    if msg == FUEL_EXHAUSTED {
        return RefOutcome::Budget;
    }
    let class = if msg == HOST_TRAP {
        TrapClass::HostTrap
    } else {
        TrapClass::from_kiln_message(msg)
    };
    let trap_shaped = matches!(
        err.category,
        kiln_error::ErrorCategory::Runtime | kiln_error::ErrorCategory::RuntimeTrap
    );
    if !trap_shaped && class == TrapClass::Unclassified {
        return RefOutcome::EngineFault(format!("{:?} {}: {msg}", err.category, err.code));
    }
    RefOutcome::Trap {
        code: err.code,
        category: format!("{:?}", err.category),
        class,
        message: msg.to_string(),
    }
}

/// One reference call, executed on a fresh engine and instance.
fn execute_once(
    wasm: &[u8],
    export: &str,
    args: Vec<Value>,
    fuel: u64,
    imports: Imports,
    imported_funcs: u32,
) -> Result<RefRun, RefError> {
    let log = Arc::new(Mutex::new(Vec::new()));
    let mut engine = StacklessEngine::new();
    engine.set_host_handler(Box::new(Handler {
        imports,
        log: Arc::clone(&log),
    }));
    let (module, inst) = load(&mut engine, wasm, fuel)?;
    let ex = module
        .get_export(export)
        .filter(|x| x.kind == ExportKind::Function)
        .ok_or_else(|| RefError::NoExport(export.to_string()))?;
    if ex.index < imported_funcs {
        // kiln's direct-execute path for an import swallows host errors and
        // substitutes zeros.
        return Err(RefError::Unsupported(format!(
            "export `{export}` re-exports an import"
        )));
    }
    engine.reset_call_depth();
    engine.set_fuel(fuel);
    let r = engine.execute(inst, ex.index as usize, args);
    let left = engine.remaining_fuel().unwrap_or(0);
    let outcome = match r {
        Ok(vals) => match vals.iter().map(from_kiln).collect() {
            Ok(v) => RefOutcome::Values(v),
            Err(m) => RefOutcome::EngineFault(m),
        },
        Err(err) => classify(&err),
    };
    let calls = log.lock().expect("host log poisoned").clone();
    Ok(RefRun {
        outcome,
        calls,
        fuel_used: fuel - left.min(fuel),
    })
}

type Job = Box<dyn FnOnce() + Send>;

thread_local! {
    /// This thread's kiln worker: a long-lived large-stack thread that runs
    /// every reference call made from here, each on a FRESH engine and
    /// instance. Spawning a new thread per call was the cost that dominated
    /// on Linux: measured in an aarch64 Ubuntu VM (debug build), one call was
    /// ~14-20 ms although decode, conversion, instantiation and execution
    /// together took ~2 ms on a long-lived thread (kiln's per-thread
    /// initialization is paid on each new thread); the CI runner, x86_64,
    /// spent ~470 ms per case. The worker exits when this thread does.
    static WORKER: std::sync::mpsc::Sender<Job> = {
        let (tx, rx) = std::sync::mpsc::channel::<Job>();
        std::thread::Builder::new()
            .name("kiln-reference".into())
            .stack_size(KILN_STACK)
            .spawn(move || {
                for job in rx {
                    job();
                }
            })
            .expect("spawn the kiln worker");
        tx
    };
}

/// Run `export(args)` on kiln with `fuel` instructions of budget.
pub fn run(
    wasm: &[u8],
    export: &str,
    args: &[WasmValue],
    fuel: u64,
    imports: &Imports,
) -> Result<RefRun, RefError> {
    wasmparser::validate(wasm).map_err(|e| RefError::Invalid(e.to_string()))?;
    let scan = scan_imports(wasm, imports)?;
    let wasm = wasm.to_vec();
    let export = export.to_string();
    let args: Vec<WasmValue> = args.to_vec();
    let imports = imports.clone();
    let (tx, rx) = std::sync::mpsc::channel();
    let job: Job = Box::new(move || {
        // A panic inside kiln is this call's failure, not the worker's end.
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let args = args.into_iter().map(to_kiln).collect();
            execute_once(&wasm, &export, args, fuel, imports, scan.imported_funcs)
        }))
        .unwrap_or_else(|_| Err(RefError::Instantiate("kiln panicked".into())));
        let _ = tx.send(r);
    });
    WORKER
        .with(|w| w.send(job))
        .map_err(|_| RefError::Instantiate("kiln worker is gone".into()))?;
    rx.recv()
        .map_err(|_| RefError::Instantiate("kiln worker dropped the call".into()))?
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classify_separates_traps_budget_and_faults() {
        // A recognised spec trap.
        assert!(matches!(
            classify(&kiln_error::Error::runtime_trap("integer divide by zero")),
            RefOutcome::Trap {
                class: TrapClass::IntegerDivideByZero,
                ..
            }
        ));
        // kiln's own internal error through the SAME trap constructor: it must
        // stay Unclassified (which the matrix never accepts as agreement).
        assert!(matches!(
            classify(&kiln_error::Error::runtime_trap(
                "table.set: expected value on stack"
            )),
            RefOutcome::Trap {
                class: TrapClass::Unclassified,
                ..
            }
        ));
        // Fuel exhaustion: Budget, never a trap.
        assert_eq!(
            classify(&kiln_error::Error::runtime_trap(FUEL_EXHAUSTED)),
            RefOutcome::Budget
        );
        // A host error is a HostTrap.
        assert!(matches!(
            classify(&kiln_error::Error::runtime_trap(HOST_TRAP)),
            RefOutcome::Trap {
                class: TrapClass::HostTrap,
                ..
            }
        ));
        // A non-trap category with an unknown message: an engine fault.
        assert!(matches!(
            classify(&kiln_error::Error::validation_error("bad module")),
            RefOutcome::EngineFault(_)
        ));
    }
}
