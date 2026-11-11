//! RQ-91-NAMECOLL (#1698): an imported function's object symbol must not
//! collide with anything else in the object.
//!
//! Every object builder (ARM Thumb-2/A32 `build_relocatable_elf`, RV32
//! `build_multi_func_riscv_elf`, AArch64 `build_multi_func_aarch64_elf`)
//! rewrites an import call's `func_N` label to the import's wasm FIELD name
//! (#173/#197/#871/#1017) and emits it as an `SHN_UNDEF` symbol for the
//! embedder to define. All three then resolved that name in the SAME
//! namespace as the object's own definitions, and a definition won. So
//! `(import "env" "get")` beside `(export "get")` bound the import call to
//! the module's own export, rc 0 and no undefined symbol. The same held for an
//! import named after a `func_N` label or a `__synth_*` data symbol (a `BL`
//! into data). Two imports with the same field from different modules
//! collapsed onto one undefined symbol.
//!
//! The fix is a refusal, not a renaming. The import's plain field name IS the
//! embedder ABI (gale, kiln, falcon and Zephyr link against `k_spin_lock`, not
//! a mangled name), so every non-colliding object keeps its bytes. A colliding
//! object could not be used before either: a linker that is given the host
//! function fails `multiple definition`, and one that is not runs the wrong
//! function.
//!
//! This module holds only the RULE. Each builder supplies the DEFINED set
//! from its own symbol table. There is no hand list of reserved names here:
//! a list would be a second copy that drifts the first time a builder defines a
//! new symbol.

use std::collections::HashMap;

/// One CALLED imported function: the import's wasm `(module, field)`.
/// "Called" means an emitted relocation names it: a `call`, or (AArch64) a
/// funcref-table trampoline. A declared but uncalled import never becomes a
/// symbol, so it never collides.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CalledImport<'a> {
    pub module: &'a str,
    pub field: &'a str,
}

/// Refuse when a called import's symbol (its field name) would not be a
/// distinct `SHN_UNDEF` symbol of its own.
///
/// * `called`: every called import, in relocation order. Repeats are fine.
/// * `is_defined`: does this builder DEFINE a symbol of this name (an export,
///   a `func_N` label, a `__synth_*` data or region symbol, the funcref
///   table, ...)? Derived from the builder's own symbol table.
/// * `is_other_external`: does this object reference this name as an
///   undefined external for a purpose OTHER than this import (a runtime
///   helper such as `__aeabi_f2lz`, `__meld_dispatch_import`, an uncompiled
///   callee's `func_N`)? Both would share one symbol.
///
/// Two imports of the same `(module, field)` are the same host function in
/// wasm, so sharing one symbol is correct and is not refused.
///
/// The first collision found, in `called` order, is returned. The message
/// names the import and the symbol it would bind to.
pub fn check_called_import_symbols<'a>(
    called: impl IntoIterator<Item = CalledImport<'a>>,
    is_defined: impl Fn(&str) -> bool,
    is_other_external: impl Fn(&str) -> bool,
) -> Result<(), String> {
    let mut owner: HashMap<&'a str, &'a str> = HashMap::new();
    for imp in called {
        if is_defined(imp.field) {
            return Err(format!(
                "import `{}`.`{}` is called, but its symbol `{}` is a name this \
                 object already DEFINES (the module's own export, a `func_N` \
                 label, or a synth symbol such as `__synth_globals`). The call \
                 would bind to that definition instead of the host import, so \
                 refusing (RQ-91-NAMECOLL, #1698). Rename the export or the \
                 import so the names differ",
                imp.module, imp.field, imp.field
            ));
        }
        if is_other_external(imp.field) {
            return Err(format!(
                "import `{}`.`{}` is called, but its symbol `{}` is also an \
                 external this object references for a different purpose (a \
                 runtime helper or an uncompiled callee). Both would bind the \
                 one symbol, so refusing (RQ-91-NAMECOLL, #1698)",
                imp.module, imp.field, imp.field
            ));
        }
        match owner.get(imp.field) {
            Some(&m) if m != imp.module => {
                return Err(format!(
                    "imports `{m}`.`{f}` and `{}`.`{f}` are both called, and both \
                     would bind the one undefined symbol `{f}`. The host can \
                     supply only one function for two different imports, so \
                     refusing (RQ-91-NAMECOLL, #1698)",
                    imp.module,
                    f = imp.field
                ));
            }
            Some(_) => {}
            None => {
                owner.insert(imp.field, imp.module);
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ci<'a>(module: &'a str, field: &'a str) -> CalledImport<'a> {
        CalledImport { module, field }
    }

    #[test]
    fn import_named_like_a_definition_refuses_1698() {
        let e =
            check_called_import_symbols([ci("env", "get")], |n| n == "get", |_| false).unwrap_err();
        assert!(
            e.contains("`env`.`get`") && e.contains("symbol `get`"),
            "{e}"
        );
        assert!(e.contains("#1698"), "{e}");
    }

    #[test]
    fn import_named_like_another_external_refuses_1698() {
        let e = check_called_import_symbols(
            [ci("env", "__aeabi_f2lz")],
            |_| false,
            |n| n == "__aeabi_f2lz",
        )
        .unwrap_err();
        assert!(e.contains("different purpose"), "{e}");
    }

    #[test]
    fn same_field_from_two_modules_refuses_1698() {
        let e = check_called_import_symbols(
            [ci("a", "get"), ci("a", "get"), ci("b", "get")],
            |_| false,
            |_| false,
        )
        .unwrap_err();
        assert!(e.contains("`a`.`get` and `b`.`get`"), "{e}");
    }

    #[test]
    fn same_module_and_field_twice_is_one_host_function_1698() {
        check_called_import_symbols([ci("env", "get"), ci("env", "get")], |_| false, |_| false)
            .unwrap();
    }

    #[test]
    fn distinct_names_pass_1698() {
        check_called_import_symbols(
            [ci("env", "get"), ci("env", "put")],
            |n| n == "get7" || n == "func_2",
            |n| n == "__aeabi_l2f",
        )
        .unwrap();
    }

    #[test]
    fn nothing_called_passes_1698() {
        check_called_import_symbols(std::iter::empty(), |_| true, |_| true).unwrap();
    }
}
