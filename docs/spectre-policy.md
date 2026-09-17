# Synth Spectre / Speculative-Execution Policy

Status: living document. Last reviewed against Wasmtime 44.0.0 release notes (2026-04)
and the Bytecode Alliance security advisories of 2026-04-09.

## 1. Policy intent and scope

**Scope — which backends this policy analyses.** synth ships four code
generators. This document analyses **two** of them:

* **Thumb-2** (ARMv7-M / ARMv8-M, Cortex-M0/M3/M4/M7/M33/M55 — `--cortex-m`
  or a `-t cortex-m*` target), and
* **RV32** (`-b riscv`).

The other two are **UNANALYSED** — no row below applies to them, and nothing
here should be read as a speculation decision about their output:

* **A32** (Arm32 ISA, `-t cortex-r5`). Note that an ARM compile with neither
  `--target` nor `--cortex-m` also selects the Arm32 ISA (the untargeted
  default in `synth-cli`'s target resolution), so the default untargeted
  `synth compile` output is outside this policy.
* **A64** (`-b aarch64`). This is the backend where the analysis matters most,
  because both premises the rows below rely on fail for it: it emits the
  canonical Spectre-v1 bounds-check-bypass shape — bounds-checked by default,
  a compare-and-branch guard immediately before the dereference
  (`CMP w_addr, w_lim; B.LS ok; BRK #0; ok: ADD x, x28, w_addr; LDR`, the
  `bounds_check` closure in `crates/synth-backend-aarch64/src/selector.rs`,
  measured on the v0.68 base), with no `csdb` — and its `--relocatable`
  object links into ordinary arm64-Linux programs that CI executes natively.
  Those run on speculating application cores that share caches and are not
  single-tenant, which is exactly the configuration Wasmtime's `use_csdb`
  setting exists for. Analysing A64 (and A32) is open work, not a
  conclusion (#1288).

For the two analysed backends the threat model and the mitigation calculus
differ from Wasmtime/Cranelift on a desktop or cloud aarch64 / x86-64 host:

* On Cortex-M0/M0+/M3/M4/M33 the core is in-order and does **no speculation
  past mispredicted branches**. There is no transient-execution attack surface
  for those parts.
* On Cortex-M7 there is limited dual-issue and limited speculation, but no
  shared cache with another security domain (single-tenant MCU).
* On Cortex-M55 the Helium MVE pipeline can speculate, but again only within
  one security domain.
* The analysed targets are single-tenant: there is no cross-guest sandbox. The
  threat model is *one* untrusted WASM module running on bare metal with
  optional MPU/PMP isolation, not many WASM guests sharing one host process.

What that means for Spectre-v1 (bounds-check bypass): the Wasmtime concern
("guest tricks the host into speculatively executing past a CMP/BHS and the
host caches a secret") **does not directly translate**, because there is no
secret of a different security domain inside the same address space on a
single-tenant MCU. The relevant residual concern is the MPU boundary
(privileged vs unprivileged) and any future multi-component scenario in
[kiln](https://github.com/pulseengine/kiln).

We therefore follow the Wasmtime 44.0.0 default (csdb off by default) for
performance, **but** we make the decision *explicit per lowering* using the
[Crocus](https://dl.acm.org/doi/abs/10.1145/3617232.3624862) policy taxonomy:

1. **F — emit a fence.** On Cortex-M the fence equivalent of aarch64 `csdb`
   is `DSB SY` (data synchronization barrier) optionally paired with `ISB SY`.
   On RV32 the equivalent is the `fence iorw, iorw` instruction. **No lowering
   emits either today.** The only `DSB SY; ISB SY` pair synth emits is in the
   FPU-enable sequence of the Cortex-M startup, after the CPACR write where
   ARM requires a barrier (`generate_minimal_startup` in
   `crates/synth-cli/src/main.rs`, and `StartupCode::generate_thumb` in
   `crates/synth-backend/src/cortex_m.rs`) — present in a `cortex-m4f` image,
   absent from a `cortex-m4` image — and it is not a speculation fence. The
   RV32 opcode exists (`RiscVOp::Fence` in
   `crates/synth-backend-riscv/src/riscv_op.rs`, encoded by the RV32 encoder)
   but no selector emits it.
2. **D — rely on a different mitigation.** Compile-time bounds check;
   MPU region; hardware does not speculate.
3. **A — accept the residual risk** with explicit rationale, e.g. because the
   op is not attacker-controlled, or because the attacker model is
   single-tenant.

## 2. Per-rule decisions

Rules below are the lowerings the analysed backends ship. Each row cites a
**symbol** (function, type or match arm) and its file — never a line number,
which went stale on every refactor (#1288). The shapes quoted were re-measured
by disassembling output of the v0.68 compiler. The ARM rows cover both shipped
ARM selectors: the direct selector (`select_with_stack`, forced by
`--relocatable`) calls the `generate_*_with_bounds_check` helpers, and the
optimized path (`OptimizerBridge`) calls the same `software_bounds_guard`
through `push_software_bounds_guard`.

| # | Rule / Lowering | Speculative-sensitive op | Decision | Mitigation in place / TODO | Rationale |
|---|---|---|---|---|---|
| 1 | `InstructionSelector::generate_load_with_bounds_check` (Software mode), guard from `InstructionSelector::software_bounds_guard` — `crates/synth-synthesis/src/instruction_selector.rs` | bounds-checked i32 load (#752 wraparound-safe, #377 inline trap): `SUB R12,R10,#k; CMP R10,R12; BHS ok1; UDF; ok1: CMP addr,R12; BLS ok2; UDF; ok2: LDR rd,[R11,addr]` with `k = offset + size` | **D** | The in-bounds path takes a forward branch over an inline `UDF`; the out-of-bounds path falls into the `UDF`. On Cortex-M0/M3/M4/M33 the core does not speculate, so the `LDR` never executes on a mispredicted in-bounds prediction. (On a speculating core the `LDR` is the predicted-taken successor of `BLS` — see #2.) | In-order Cortex-M; single-tenant. Matches Wasmtime 44.0.0 "csdb off by default" on aarch64, which itself was justified by other in-order cores doing the same. |
| 2 | Same lowering on Cortex-M7 / M55 | bounds-checked i32 load | **F (opt-in)** | TODO: add a `--mitigate-spectre-v1` CLI flag that inserts `DSB SY` between the `BLS` and the `LDR`. No such flag exists today; falls back to **D**. | M7 has limited speculation but no cross-domain secret. Provide the knob (per Wasmtime `use_csdb` setting) but default off; mirrors Wasmtime 44.0.0. |
| 3 | `generate_load_with_bounds_check` (Masking mode), mask from `InstructionSelector::mask_effective_address` — `crates/synth-synthesis/src/instruction_selector.rs` | bounds-checked load via `ADD addr,#offset; SUB R12,R10,#1; AND addr,addr,R12; SUB R12,R12,#(size-1); CMP addr,R12; IT HI; MOVHI addr,R12` then `LDR rd,[R11,addr]` (power-of-two sizes) | **D** | The AND-mask plus the IT-HI clamp make the effective address unconditionally in-bounds at the architectural level; there is no branch, so no mispredict and no transient window. This is the [Blade](https://cseweb.ucsd.edu/~dstefan/pubs/vassena:2021:blade.pdf)-style index-masking mitigation. The optimized path declines masked memory access and routes the function to the direct selector (the `BoundsCheckConfig::Masking` decline in `OptimizerBridge`, `crates/synth-synthesis/src/optimizer_bridge.rs`). | Masking is itself the strongest mitigation against Spectre-v1 BCB. Recommended config for Cortex-M55. |
| 4 | `generate_load_with_bounds_check` (`BoundsCheckConfig::None` / `BoundsCheckConfig::Mpu`) — `crates/synth-synthesis/src/instruction_selector.rs` | `LDR rd,[R11,addr]` with **no** check | **D** | No inline check is emitted, so there is no software check to bypass speculatively. **This is not a trap:** an out-of-bounds access faults only if a platform- or embedder-programmed MPU region covers the boundary. synth programs no MPU region in this mode — `--safety-bounds mpu` emits bytes identical to `--safety-bounds none` on both `--relocatable` and `--cortex-m` (every PROGBITS section compared, v0.68; see #1284). Without such a region an out-of-bounds read returns whatever sits at `R11 + addr` (the compliance envelope in `CLAUDE.md`). | Speculation-wise there is nothing to bypass. Memory-safety-wise this mode relies on the integrator's MPU or on a trusted module. |
| 5 | `InstructionSelector::generate_store_with_bounds_check` (Software) — `crates/synth-synthesis/src/instruction_selector.rs` | bounds-checked i32 store (same `software_bounds_guard`) | **D** | Same reasoning as #1. Additionally, stores do not produce speculative-data values, so the canonical Spectre-v1 BCB chain (load → use-in-second-load) is broken at the source. | Same as #1. Stores are not a Spectre-v1 read primitive. |
| 6 | `InstructionSelector::generate_subword_load_with_bounds_check` (LDRB / LDRH / LDRSB / LDRSH) — `crates/synth-synthesis/src/instruction_selector.rs` | sub-word bounds-checked load | **D** | Identical structure to #1 with smaller `access_size`. The bounds check `addr <= R10 - k` (`k = offset + access_size`, #752 wraparound-safe shape) is exact, no rounding error. | In-order core; same reasoning as #1. |
| 7 | `InstructionSelector::generate_i64_load_with_bounds_check` — `crates/synth-synthesis/src/instruction_selector.rs` | bounds-checked 8-byte load (LDR+LDR pair) | **D** | The guard is `software_bounds_guard(addr, offset, 8)`, so the high word's read is covered by the same compare. | Same as #1, plus the i64 read is split into two ARM `LDR` issues that the in-order core executes sequentially. |
| 8 | `add_with_shift` standard rule in `RuleDatabase::with_standard_rules` — `crates/synth-synthesis/src/rules.rs` (Pattern: `I32Shl` then `I32Add` → `ADD rd, rn, rm LSL #amount`) | scaled-index address arithmetic — analog of Cranelift `load(iadd(base, ishl(index, amt)))` | **A (with constraint)** | The shift `amount` is still hard-coded to `2` in the replacement ("Would be extracted from pattern"). **Constraint:** no shipped ARM path emits rule replacements. `InstructionSelector::select` *does* emit them (via `apply_replacement` in `instruction_selector/select_default.rs`), but every call to it is in test code; production enters through `select_with_stack` and `OptimizerBridge`, neither of which consults the pattern matcher. `RuleApplicator::apply_rules` (`crates/synth-synthesis/src/pattern_matcher.rs`) keeps the original ops. See §3 and `crates/synth-synthesis/tests/regression_spectre_cve_2026_34971.rs`. | **This is the closest synth analog to GHSA-jhxm-h53p-jm7w (CVE-2026-34971).** Residual accepted while the rule is inert; §3 records which half of that is gated by a test and which half is not. |
| 9 | `select` — `rule_i32_select` (`crates/synth-synthesis/src/sel_dsl/generated.rs`), used by `select_with_stack` | conditional move: `CMP rc,#0; IT NE; MOVNE rd,rn` (measured) | **D** | Cortex-M `IT`/`MOVNE` is *architecturally* conditional, not speculative — the move occurs (or not) after the flag is settled. There is no transient bypass window. | ARM IT-blocks are predicated execution, not branch speculation. |
| 10 | `br_if` — the `BrIf` arm of `select_with_stack` (`crates/synth-synthesis/src/instruction_selector/select_with_stack.rs`) and `Opcode::CondBranch` in `OptimizerBridge` (`crates/synth-synthesis/src/optimizer_bridge.rs`) | branch on attacker-controlled condition | **D** | On Cortex-M0/M3/M4 there is no branch predictor; on M7 the predictor exists but the secret-of-another-domain prerequisite is absent (single tenant). | Single-tenant threat model. |
| 11 | `br_table` — the `BrTable` arm of `select_with_stack`; the optimized path routes every function containing `br_table` to the direct selector (`has_br_table` in `crates/synth-backend/src/arm_backend.rs`) | branch on attacker-controlled index | **D** | The lowering is a *linear chain of compares* (`CMP rn,#i; BEQ target_i; …; B default`, measured), **not** a memory-indexed jump table (`LDR pc,[base,index,LSL #2]`). A linear chain has no speculative load primitive at all. | Cortex-M `TBB`/`TBH` is not used here, eliminating the indirect-jump speculation path that exists on aarch64. If we later add `TBB`/`TBH`, revisit this row. |
| 12 | `call_indirect` — the `ArmOp::CallIndirect` pseudo-op expanded by the encoder (`encode_arm_call_indirect` and its Thumb-2 twin in `crates/synth-backend/src/arm_encoder.rs`); type-check selection in `InstructionSelector::resolve_runtime_type_check` | indirect call via table | **D** | Measured shape: a table-size bounds check (`CMP idx,#size; BLO ok; UDF`), then — **only for a table holding more than one function type** (#676) — a runtime type-id check (`LDR r12,[r11,idx*4+type_off]; CMP r12,#id; BEQ ok; UDF`), then `LDR r12,[r11,idx*4]; BLX r12`. For a single-type table the type check is discharged at compile time and nothing is emitted. Speculation past the guard would only execute attacker-chosen code across a security domain, and there is no second domain. Cortex-M0/M3/M4 has no indirect branch predictor. | Single-tenant; in-order cores. M7 has a BTAC but again no cross-domain secret. |
| 13 | `memory.grow` — the `MemoryGrow` arm of `select_with_stack` (`ArmOp::MemoryGrow`) | grow memory by attacker-controlled count | **D** | Memory is *fixed* on these targets: `memory.grow(n)` lowers to `MVN rd,#0` (−1), and `memory.grow(0)` to the current size (`LSR rd,R10,#16`, #539) — both measured. No actual growth happens, so no speculative window into a yet-unallocated region. | Fixed memory; no allocation to race. |
| 14 | `memory.size` — the `MemorySize` arm of `select_with_stack` (`ArmOp::MemorySize`) | read memory size | **D** | `LSR rd,R10,#16` (pages = bytes >> 16, measured). No memory access. | Architectural read of a fixed register. |
| 15 | `global.get` / `global.set` — the `GlobalGet` / `GlobalSet` arms of `select_with_stack` | indexed load/store of WASM globals | **D** | Index is *static* (a WASM immediate, not a stack value). The lowering is `LDR`/`STR` at a fixed immediate offset from R9 (global 0 measured as `STR r0,[r9]` / `LDR r1,[r9]`). No attacker-controllable address arithmetic. | Static index ⇒ no Spectre-v1 vector. |
| 16 | RISC-V `lower_load_word`, guard from `emit_bounds_check` — `crates/synth-backend-riscv/src/selector.rs` | i32 load on RV32 | **D** | The per-access knob exists (`RvBoundsMode`: `None` / `Pmp` / `Software` / `Mask`, selected by `--safety-bounds`). Software mode emits `lui/addi lim,(mem_size-k); bltu lim,addr,Ltrap; j ok; Ltrap: ebreak; ok: add tmp,s11,addr; lw`. Mask mode clamps with `and` + `bgeu`. Measured on one `i32.load` + one `i32.store` module (rv32imac, v0.68): `.text` 52 B with `none`, 92 B with `software` (2 × `bltu`/`ebreak`), 108 B with `mask` (2 × `and`/`bgeu`). `None`/`Pmp` emit no check — "rely on PMP", which, as on ARM (#4), synth does not program. | RV32IM bare-metal microcontroller cores (e.g. ESP32-C3) do not speculate. Formerly an accepted residual because the knob did not exist; that residual is retired. |
| 17 | RISC-V `lower_load_subword` — `crates/synth-backend-riscv/src/selector.rs` | sub-word load on RV32 | **D** | Same guard (`emit_bounds_check`) as #16. | Same as #16. |
| 18 | RISC-V `lower_store` — `crates/synth-backend-riscv/src/selector.rs` | i32/sub-word store on RV32 | **D** | Stores are not a read primitive; same guard as #16 when enabled. | Same as #5 / #16. |
| 19 | RISC-V `lower_if` / `lower_br_if` — `crates/synth-backend-riscv/src/selector.rs` | branch on attacker-controlled condition (RV32) | **D** | RV32 simple bare-metal cores do not have a branch predictor with cross-domain reach. | Single-tenant. |
| 20 | Strength reduction (MUL by power of two → LSL) — `PeepholeOptimizer::try_optimize_3`, `crates/synth-synthesis/src/peephole.rs` | constant-fold of multiply by power of two | **D (pass not shipped)** | Pure arithmetic rewrite, no memory access, no branch. **This ARM-level pass is not on any shipped path** — its only callers outside its own unit tests are the `benchmark_suite` and `led_blink_test` integration tests. The optimized path runs synth-opt's IR-level `PeepholeOptimization` instead (`crates/synth-opt/src/lib.rs`, added by `OptimizerBridge`), which rewrites redundant constants only. | Not a speculation-sensitive op either way. |
| 21 | Store→load forwarding — `PeepholeOptimizer::try_optimize_2`, `crates/synth-synthesis/src/peephole.rs` | store-load forwarding when registers match | **D (pass not shipped)** | The rewrite *removes* a load whose value is already in a register; it never *introduces* a speculative load. Same shipping caveat as #20: this pass is reached only from tests. | Forwarding is a compile-time identity; no transient state. |

### Coverage summary

Over the 21 rows above (two analysed backends only):

* **F (fence required):** 0 rules require a mandatory fence.
* **F (opt-in):** 1 row (#2 — Cortex-M7/M55 software bounds check), for a
  future `--mitigate-spectre-v1` flag that does not exist yet.
* **D (other mitigation suffices):** 19 rows (two of them, #20 and #21, about
  a pass that is not shipped).
* **A (accepted residual):** 1 row (#8 `add_with_shift` standard rule; see §3
  for what is and is not gated). The former second residual — the RV32
  bounds-check knob — was retired when the knob was measured working (#1288).
* **Not analysed:** every A32 and A64 lowering (§1).

## 3. aarch64 CVE analog audit

### GHSA-jhxm-h53p-jm7w (CVE-2026-34971) — aarch64 Cranelift sandbox escape

**Source:** [Wasmtime advisory](https://github.com/bytecodealliance/wasmtime/security/advisories/GHSA-jhxm-h53p-jm7w).
The bug: an ISLE lowering rule on aarch64 mis-masks the `amt` field when
pattern-matching `load(iadd(base, ishl(index, amt)))`. The faulty mask causes
Cranelift to pick the rule for `amt` values it should reject; the address
actually loaded then differs from the address bounds-checked, defeating the
Spectre-mitigated bounds-check guard pages and yielding an
arbitrary-read/write primitive for guests.

**Synth analog:** the closest pattern in synth is the unused standard rule
`add_with_shift`, registered by `RuleDatabase::with_standard_rules` in
`crates/synth-synthesis/src/rules.rs`:

```rust
// RuleDatabase::with_standard_rules, crates/synth-synthesis/src/rules.rs
db.add_rule(SynthesisRule {
    name: "add_with_shift".to_string(),
    priority: 80,
    pattern: Pattern::Sequence(vec![
        Pattern::WasmInstr(WasmOp::I32Shl),
        Pattern::WasmInstr(WasmOp::I32Add),
    ]),
    replacement: Replacement::ArmInstr(ArmOp::Add {
        rd: Reg::R0,
        rn: Reg::R1,
        op2: Operand2::RegShift {
            rm: Reg::R2,
            shift: ShiftType::LSL,
            amount: 2, // Would be extracted from pattern
        },
    }),
    ...
});
```

Two issues are visible by inspection:

1. The `amount` field is hard-coded to `2` rather than read from the matched
   `I32Const(_)` immediate. This is the *same class of bug* as the aarch64
   ISLE one — a lowering rule that fires on a more general pattern than its
   replacement supports.
2. The pattern matches *any* `I32Shl` followed by `I32Add` regardless of
   whether the LHS of the `I32Shl` is the matched index or the matched base,
   and regardless of the shift constant.

**Why synth is not exploitable today — corrected in v0.68 (#1288).** An
earlier version of this section gave one reason: `RuleApplicator::apply_rules`
(`crates/synth-synthesis/src/pattern_matcher.rs`) does not rewrite matched ops
to the rule's `Replacement`. That is still true, but it is not the whole
story. There is a **second** consumer of the rule table,
`InstructionSelector::select` (`instruction_selector/select_default.rs`), and
it **does** emit replacements through `apply_replacement` — including the
unbound `amount = 2`. What keeps the shape latent is that `select` is not on
a shipped path: every call site `git grep` finds is in the test module of
`instruction_selector.rs`. `arm_backend.rs` hands the rule table to the
selector but enters through `select_with_stack`, and neither
`select_with_stack` nor `OptimizerBridge` consults the pattern matcher.
The aarch64 sandbox-escape shape is latent, not live.

**Mitigation applied — and what it does not cover:** the regression test
`crates/synth-synthesis/tests/regression_spectre_cve_2026_34971.rs` asserts
that the standard rule's hard-coded `amount` is *either* fixed (extracted
from the pattern) *or* `RuleApplicator` still does not rewrite. It fails
loudly if `RuleApplicator` starts rewriting without extracting `amount`. It
does **not** watch `InstructionSelector::select`: wiring that API into a
shipped path would make the shape live with the test still green. Gating that
route is open work.

The **patch principle** from the aarch64 CVE applies: a pattern-match
condition and its replacement must be on the same set. Verus contracts in
`crates/synth-synthesis/src/contracts.rs` could formalize this; left for a
follow-up.

### GHSA-qqfj-4vcm-26hv (CVE-2026-34944) — x86-64 `f64x2.splat` over-read

**Source:** [Wasmtime advisory](https://github.com/bytecodealliance/wasmtime/security/advisories/GHSA-qqfj-4vcm-26hv).
The bug: on x86-64 without SSE3, the Cranelift lowering for `f64x2.splat`
reading from memory issues a 128-bit load instead of the required 64-bit
load. On systems with guard pages disabled (or with signals-based-traps
disabled) this leaks up to 8 bytes outside the WASM heap.

**Synth analog:** none.

* Synth does not target x86-64 at all.
* `f64x2.splat` on Cortex-M55 / Helium MVE would be `VDUP.64`, not a memory
  load + broadcast — Helium loads 128-bit lanes via `VLDRW.32 Qd, [Rn]`
  (`ArmOp::MveLoad`, `crates/synth-synthesis/src/rules.rs`) which by construction is a 128-bit access for
  a 128-bit lane. There is no 64-bit-to-128-bit "broadcast that secretly
  over-reads" path because MVE doesn't have an `f64x2.splat`-style
  short-load + replicate lowering — the splat goes through scalar load +
  VDUP, which are two distinct instructions sized correctly each.
* RV32 has no SIMD at all in synth today.

**Conclusion:** the f64x2.splat over-read shape has no analog in synth. No
regression test is added because there is no code path to gate.

### Future CVE classes to watch

The 2026-04 Wasmtime advisory cluster also includes:

* GHSA-hx6p-xpx3-jvvv / GHSA-jxhv-7h78-9775 — Component Model UTF-16 string
  transcoding bugs. Synth's canonical-ABI code lives in `crates/synth-abi/`,
  a library the `synth` binary does not link today (#1277); its transcoding
  helpers should be audited against these advisories before any compile path
  consumes it.
* GHSA-xx5w-cvp6-jv83 — Winch sandbox escape. Synth does not use Winch;
  N/A.
* GHSA-f984-pcp8-v2p7, GHSA-q49f-xg75-m9xw, GHSA-m9w2-8782-2946 — Winch
  table-grow / table-fill / 64-bit table issues. N/A.

## 4. References

* **Wasmtime 44.0.0 release notes** — csdb default change on aarch64.
  Quoted: *"the `csdb` instruction, a defense-in-depth measure for spectre,
  is no longer emitted by default on aarch64 to match what peer runtimes are
  doing. In some situations this is known to provide up to a 6x performance
  boost on macOS as well."* The `use_csdb` Cranelift setting remains for
  opt-in. See
  [github.com/bytecodealliance/wasmtime/releases/tag/v44.0.0](https://github.com/bytecodealliance/wasmtime/releases/tag/v44.0.0).
* **Bytecode Alliance security advisory bulletin, 2026-04-09** —
  [bytecodealliance.org/articles/wasmtime-security-advisories](https://bytecodealliance.org/articles/wasmtime-security-advisories).
* **GHSA-jhxm-h53p-jm7w / CVE-2026-34971** — aarch64 Cranelift sandbox escape.
  [Advisory](https://github.com/bytecodealliance/wasmtime/security/advisories/GHSA-jhxm-h53p-jm7w).
* **GHSA-qqfj-4vcm-26hv / CVE-2026-34944** — x86-64 `f64x2.splat` over-read.
  [Advisory](https://github.com/bytecodealliance/wasmtime/security/advisories/GHSA-qqfj-4vcm-26hv).
* **Crocus (VanHattum et al., ASPLOS 2024)** — *Lightweight, Modular
  Verification for WebAssembly-to-Native Instruction Selection.* Provides
  the policy taxonomy (F / D / A) used in §2.
  [DOI 10.1145/3617232.3624862](https://dl.acm.org/doi/abs/10.1145/3617232.3624862).
* **Blade (Vassena et al.)** — *Automatically Eliminating Speculative Leaks
  from Cryptographic Code.* Provides the index-masking mitigation cited in
  row #3. [POPL 2021](https://cseweb.ucsd.edu/~dstefan/pubs/vassena:2021:blade.pdf).
* **ARM Cortex-M architecture reference manuals** — for the
  "no speculation past mispredicted branch" property of M0/M3/M4/M33.
* **RISC-V Zicond / Zk* extensions** — for the future RV32 fence semantics
  (the `fence iorw, iorw` opcode already exists as `RiscVOp::Fence` in
  `crates/synth-backend-riscv/src/riscv_op.rs`; no selector emits it).

## 5. Review cadence

This document is reviewed:

* on every Wasmtime major release (currently every ~6 weeks);
* on every new Bytecode Alliance security advisory cluster;
* when the synth lowering pipeline changes shape (new pass, new rule, new
  target architecture).

The maintainer of each touched lowering must update the row in §2 and either
add a regression test or extend the policy rationale.
