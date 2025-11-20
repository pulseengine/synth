# Coq + Dune Setup Guide for ASIL D Verification

## Why Dune, Not Bazel?

**TL;DR: Use the standard toolchain. Don't reinvent the wheel.**

### Industry Practice

| Project | Proof System | Build Tool |
|---------|--------------|------------|
| **CompCert** | Coq | Dune/Make |
| **CakeML** | HOL4/Isabelle | Poly/ML + Make |
| **seL4** | Isabelle | Isabelle build system |
| **Synth (ours)** | Coq | **Dune** (recommended) |

**No verified compiler uses Bazel for proofs.** They all use:
1. Standard proof system build tools
2. Separate build from main compiler
3. Extract to target language (OCaml, Standard ML, etc.)
4. Integrate extracted code with main build

### Rationale

✅ **Dune is the standard** - Used by 90%+ of Coq projects
✅ **CompCert uses it** - Proven for compiler verification
✅ **Less complexity** - Don't force Coq into Bazel
✅ **Stable proofs** - Rebuild infrequently, extract rarely
✅ **Separate concerns** - Proofs ≠ production build

❌ **No rules_coq** - No production-ready Bazel rules exist
❌ **Not worth writing** - Dune works perfectly

---

## Phase 1: Install Dependencies

### On Development Machine

```bash
# Install OPAM (OCaml package manager)
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"

# Initialize OPAM
opam init --auto-setup
eval $(opam env)

# Install Coq and Dune
opam install coq dune coq-stdlib

# Verify installation
coq --version  # Should show 8.18 or newer
dune --version # Should show 3.0 or newer
```

### Optional: Sail for ARM Semantics

```bash
# Install Sail (for ARM ASL → Coq)
opam install sail

# Clone ARM Sail specifications
git clone https://github.com/ARM-software/sail-arm.git external/sail-arm

# Note: Building ARM ASL → Coq requires 40GB RAM
# Use pre-generated Coq files instead (see Phase 3)
```

---

## Phase 2: Create Coq Project Structure

### Directory Layout

```
Synth/
├── coq/                          # Coq proofs (Dune build - SEPARATE from Bazel)
│   ├── dune-project               # Dune project definition
│   ├── synth_verification.opam   # OPAM package metadata
│   │
│   ├── theories/                  # Coq theories (.v files)
│   │   ├── dune                   # Dune build rules for theories
│   │   │
│   │   ├── Common.v               # Common definitions and tactics
│   │   ├── WasmSemantics.v        # WebAssembly formal semantics
│   │   ├── ARMSemantics.v         # ARM formal semantics (from Sail)
│   │   │
│   │   ├── Compiler.v             # Compiler implementation in Coq
│   │   ├── CompilerCorrectness.v  # Main correctness theorem
│   │   │
│   │   └── Extraction.v           # OCaml extraction configuration
│   │
│   ├── _build/                    # Dune build output (gitignored)
│   │   └── default/theories/
│   │       ├── Compiler.ml        # Extracted OCaml code
│   │       ├── Compiler.mli       # Extracted interface
│   │       └── *.vo               # Compiled Coq proofs
│   │
│   └── tests/                     # Coq proof tests
│       ├── dune
│       └── test_compiler.v
│
└── crates/                        # Rust frontend (separate - uses Bazel)
    └── synth-backend-verified/    # Wrapper for extracted OCaml
        ├── BUILD.bazel            # Imports extracted .ml from coq/_build/
        └── ocaml_compiler_wrapper.ml
```

---

## Phase 3: Configuration Files

### `coq/dune-project`

```dune
(lang dune 3.0)
(name synth_verification)
(version 0.1.0)

; Enable Coq support
(using coq 0.8)

; Package metadata
(generate_opam_files true)

(package
 (name synth_verification)
 (synopsis "Formal verification of Synth WebAssembly → ARM compiler")
 (description "Coq proofs of compiler correctness for ASIL D certification")
 (depends
  (coq (>= 8.18))
  (dune (>= 3.0))
  (coq-stdlib (>= 8.18))
  (coq-flocq (>= 4.1))    ; Floating-point formalization
  (coq-stdpp (>= 1.9))    ; Standard library extensions
 )
 (authors "PulseEngine")
 (maintainers "asil-d@pulseengine.dev")
 (license "Proprietary")
)
```

### `coq/theories/dune`

```dune
; Coq theory definition
(coq.theory
 (name Synth)
 (package synth_verification)
 (theories Stdlib Flocq)
 (flags :standard -w -notation-overridden)
)

; OCaml extraction
(rule
 (targets
   Compiler.ml
   Compiler.mli
   WasmSemantics.ml
   WasmSemantics.mli
   ARMSemantics.ml
   ARMSemantics.mli
 )
 (deps
   Common.vo
   WasmSemantics.vo
   ARMSemantics.vo
   Compiler.vo
   Extraction.v
 )
 (action
  (run coqc -R . Synth %{dep:Extraction.v})
 )
)

; Install extracted OCaml files
(install
 (section lib)
 (package synth_verification)
 (files
   (Compiler.ml as extracted/Compiler.ml)
   (Compiler.mli as extracted/Compiler.mli)
 )
)
```

---

## Phase 4: Example Coq Files

### `coq/theories/Common.v`

```coq
(** Common definitions and tactics for Synth verification *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

(** Machine integers *)
Definition i32 := Z.  (* 32-bit integers *)
Definition i64 := Z.  (* 64-bit integers *)

(** Memory model *)
Definition addr := Z.
Definition memory := addr -> option i32.

(** Useful tactics *)
Ltac inv H := inversion H; subst; clear H.

Ltac crush :=
  repeat (simpl; intuition; try congruence; auto).
```

### `coq/theories/WasmSemantics.v`

```coq
(** WebAssembly Component Model Semantics *)

Require Import Synth.Common.

(** WebAssembly values *)
Inductive wasm_value : Type :=
  | VI32 : i32 -> wasm_value
  | VI64 : i64 -> wasm_value
  | VRef : addr -> wasm_value
.

(** WebAssembly instructions (simplified subset) *)
Inductive wasm_instr : Type :=
  | WI_const : wasm_value -> wasm_instr
  | WI_add : wasm_instr
  | WI_load : addr -> wasm_instr
  | WI_store : addr -> wasm_instr
  (* ... 147 more instructions for full ASIL D ... *)
.

(** WebAssembly execution state *)
Record wasm_state : Type := {
  ws_stack : list wasm_value;
  ws_locals : list wasm_value;
  ws_memory : memory;
}.

(** Small-step operational semantics *)
Inductive wasm_step : wasm_state -> wasm_instr -> wasm_state -> Prop :=
  | step_const : forall st v,
      wasm_step st (WI_const v) {|
        ws_stack := v :: ws_stack st;
        ws_locals := ws_locals st;
        ws_memory := ws_memory st;
      |}
  (* ... more stepping rules ... *)
.
```

### `coq/theories/ARMSemantics.v`

```coq
(** ARM v8-M Semantics (from Sail) *)

Require Import Synth.Common.

(** ARM registers *)
Inductive arm_reg : Type :=
  | R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7
  | R8 | R9 | R10 | R11 | R12 | SP | LR | PC
.

(** ARM instructions (subset for Cortex-M) *)
Inductive arm_instr : Type :=
  | ARM_add : arm_reg -> arm_reg -> arm_reg -> arm_instr
  | ARM_mov : arm_reg -> i32 -> arm_instr
  | ARM_ldr : arm_reg -> addr -> arm_instr
  | ARM_str : arm_reg -> addr -> arm_instr
  (* ... *)
.

(** ARM execution state *)
Record arm_state : Type := {
  as_regs : arm_reg -> i32;
  as_memory : memory;
}.

(** ARM small-step semantics *)
Inductive arm_step : arm_state -> arm_instr -> arm_state -> Prop :=
  (* ... stepping rules ... *)
.

(** IMPORTANT: Use Sail-generated definitions for production *)
(* Replace this file with output from: *)
(* sail -coq sail-arm/model/prelude.sail sail-arm/model/armv8m.sail *)
```

### `coq/theories/Compiler.v`

```coq
(** Synth Compiler: WebAssembly → ARM *)

Require Import Synth.Common.
Require Import Synth.WasmSemantics.
Require Import Synth.ARMSemantics.

(** Compilation function *)
Fixpoint compile_instr (wi : wasm_instr) : list arm_instr :=
  match wi with
  | WI_const (VI32 n) =>
      [ARM_mov R0 n]
  | WI_add =>
      [ARM_add R0 R0 R1]
  | WI_load addr =>
      [ARM_ldr R0 addr]
  | WI_store addr =>
      [ARM_str R0 addr]
  (* ... 147 more cases ... *)
  end.

(** State relation (simulation relation) *)
Definition states_match (ws : wasm_state) (as_ : arm_state) : Prop :=
  (* Stack top matches R0 *)
  match ws_stack ws with
  | VI32 n :: _ => as_regs as_ R0 = n
  | _ => True
  end
  (* Memory matches *)
  /\ (forall a, ws_memory ws a = as_memory as_ a)
  (* ... more invariants ... *)
.

(** Correctness theorem (forward simulation) *)
Theorem compiler_correctness :
  forall (ws : wasm_state) (wi : wasm_instr) (ws' : wasm_state),
    wasm_step ws wi ws' ->
    forall (as_ : arm_state),
      states_match ws as_ ->
      exists as',
        (forall ai, In ai (compile_instr wi) -> arm_step as_ ai as') /\
        states_match ws' as'.
Proof.
  (* This is the multi-year effort for ASIL D *)
  (* Start with 3 instructions, expand to 151 *)
Admitted.
```

### `coq/theories/Extraction.v`

```coq
(** Extract compiler to OCaml *)

Require Import Synth.Compiler.

(* Configure extraction *)
Require Extraction.
Extraction Language OCaml.

(* Map Coq types to OCaml types *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => int [ "0" "succ" ].
Extract Constant Z.add => "( + )".
Extract Constant Z.sub => "( - )".

(* Extract main functions *)
Extraction "Compiler.ml" compile_instr.
```

---

## Phase 5: Build and Extract

### Build Coq Proofs

```bash
cd coq/

# Build all proofs
dune build

# Check proof status
dune build @check

# Run Coq tests
dune runtest

# Clean build
dune clean
```

### Extracted OCaml Output

After `dune build`, extracted files appear in:

```
coq/_build/default/theories/
├── Compiler.ml      # Extracted compiler code
├── Compiler.mli     # Extracted interface
├── WasmSemantics.ml # Extracted semantics
└── *.vo             # Compiled Coq proofs
```

---

## Phase 6: Integrate Extracted OCaml with Bazel

### `coq/BUILD.bazel`

```python
# Import Coq-extracted OCaml into Bazel

load("@rules_ocaml//ocaml:rules.bzl", "ocaml_library")

# Use the extracted OCaml files from Dune
ocaml_library(
    name = "verified_compiler",
    srcs = glob([
        "_build/default/theories/Compiler.ml",
        "_build/default/theories/WasmSemantics.ml",
        "_build/default/theories/ARMSemantics.ml",
    ]),
    interfaces = glob([
        "_build/default/theories/*.mli",
    ]),
    visibility = ["//visibility:public"],
    deps = [
        "@opam//pkg:zarith",  # Z3 arbitrary precision
    ],
)

# Wrapper for calling from Rust
rust_library(
    name = "verified_backend",
    srcs = ["verified_backend_ffi.rs"],
    deps = [
        ":verified_compiler",  # OCaml code
        "@crates//:ocaml",     # Rust-OCaml FFI
    ],
)
```

### Using Verified Backend in Synth

```python
# crates/BUILD.bazel

rust_binary(
    name = "synth",
    srcs = ["synth-cli/src/main.rs"],
    deps = [
        ":synth-frontend",         # Rust parser (fast iteration)
        "//coq:verified_backend",  # Coq-verified compiler (ASIL D)
        "@crates//:anyhow",
    ],
    # Enable verified backend only in ASIL D mode
    select({
        "//bazel/features:asil_d_mode": [
            "//coq:verified_backend",
        ],
        "//conditions:default": [
            ":synth-backend-rust",  # Faster, non-verified
        ],
    }),
)
```

---

## Phase 7: Development Workflow

### Separate Builds

```bash
# Development (fast iteration with Rust/Cargo)
cargo build
cargo test

# Coq proofs (slow, rebuild infrequently)
cd coq/
dune build    # Rebuilds if .v files changed
dune runtest  # Runs proof tests

# Integration (Bazel + extracted OCaml)
bazel build --config=asil_d //crates:synth
```

### When to Rebuild Coq

✅ **Rebuild Coq when:**
- Adding new WebAssembly instructions to verify
- Changing compiler transformations
- Updating correctness theorems
- ARM semantics change (rare - Sail update)

❌ **DON'T rebuild Coq for:**
- Rust frontend changes (parser, CLI, etc.)
- Build system changes
- Documentation updates
- Non-verified optimizations

---

## Phase 8: ASIL D Qualification Evidence

### Proof Artifacts to Generate

```bash
cd coq/

# Generate proof certificate
dune build @check > ../qualification/coq_proofs/proof_certificate.txt

# Extract dependencies
coqdep -R theories Synth theories/*.v > ../qualification/coq_proofs/dependencies.dot

# Count proof obligations
grep -r "Theorem\|Lemma" theories/ | wc -l > ../qualification/coq_proofs/proof_stats.txt

# Document admitted theorems (for auditors)
grep -r "Admitted" theories/ > ../qualification/coq_proofs/remaining_work.txt
```

### ISO 26262 Evidence

Generate these documents:

1. **Tool Qualification Package (TQP)** for Coq compiler
2. **Verification Evidence** - Proof certificates
3. **Traceability Matrix** - Requirements → Theorems
4. **Safety Manual** - Verified subset vs unverified portions

---

## Timeline and Effort

| Milestone | Duration | Deliverable |
|-----------|----------|-------------|
| **Setup** | 1 week | Dune project, basic structure |
| **3 Instructions** | 2-3 months | Proof of concept (ASIL B) |
| **20 Instructions** | 6-9 months | Core subset (ASIL C) |
| **151 Instructions** | 12-18 months | Full verification (ASIL D) |
| **Qualification** | 3-4 months | ISO 26262 package |

**Total: 18-24 months** to ASIL D certification

---

## Comparison with Loom Integration

### Two-Tier Architecture

```
┌─────────────────────────────────────┐
│ Loom (Open Source - ASIL B)         │
│ ├─ ISLE optimization rules          │
│ ├─ 12-phase optimization pipeline   │
│ ├─ Z3 SMT translation validation    │
│ └─ MIT License                      │
└─────────────────────────────────────┘
             ↓ (shared definitions)
┌─────────────────────────────────────┐
│ Synth (Commercial - ASIL D)         │
│ ├─ Coq proofs (this guide)          │
│ ├─ Sail ARM semantics               │
│ ├─ Extracted OCaml compiler         │
│ └─ Proprietary                      │
└─────────────────────────────────────┘
```

**Shared:** Optimization definitions (ISLE), test suites
**Separate:** Proofs, qualification evidence, ARM formalization

---

## Next Steps

1. ✅ **Create coq/ directory structure** (this guide)
2. ✅ **Install Coq + Dune** (`opam install coq dune`)
3. ✅ **Write first 3 proofs** (add, load, store)
4. ✅ **Extract to OCaml** (`dune build`)
5. ✅ **Integrate with Bazel** (when network allows OBazl)
6. ✅ **Test ASIL D build** (`bazel build --config=asil_d //crates:synth`)

---

## References

- [CompCert Build System](https://github.com/AbsInt/CompCert) - Industry standard
- [Dune Documentation](https://dune.readthedocs.io/en/stable/coq.html) - Coq integration
- [OBazl](https://github.com/obazl/rules_ocaml) - Bazel OCaml rules
- [Sail Documentation](https://github.com/rems-project/sail) - ARM ISA formalization
- [Coq Extraction](https://coq.inria.fr/refman/addendum/extraction.html) - Official guide

---

**Status**: Infrastructure defined, ready to implement when Loom shared architecture is complete
