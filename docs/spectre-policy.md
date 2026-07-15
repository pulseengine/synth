# Synth Spectre / Speculative-Execution Policy

Status: living document. Last reviewed against Wasmtime 44.0.0 release notes (2026-04)
and the Bytecode Alliance security advisories of 2026-04-09.

## 1. Policy intent

Synth compiles WebAssembly to **ARMv7-M / Thumb-2** (Cortex-M0/M3/M4/M7/M33/M55)
and to **RV32IM**. It is *not* a JIT for a server-class CPU. The threat model
and the mitigation calculus therefore differ from Wasmtime/Cranelift on a
desktop or cloud aarch64 / x86-64 host:

* On Cortex-M0/M0+/M3/M4/M33 the core is in-order and does **no speculation
  past mispredicted branches**. There is no transient-execution attack surface
  for those parts.
* On Cortex-M7 there is limited dual-issue and limited speculation, but no
  shared cache with another security domain (single-tenant MCU).
* On Cortex-M55 the Helium MVE pipeline can speculate, but again only within
  one security domain.
* Synth is single-tenant: there is no cross-guest sandbox. The threat model is
  *one* untrusted WASM module running on bare metal with optional MPU
  isolation, not many WASM guests sharing one host process.

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
   On RV32 the equivalent is the `fence iorw, iorw` instruction
   (`RiscVOp::Fence`). Synth already emits these in startup
   (`crates/synth-backend/src/cortex_m.rs:131`) and has the RV32 opcode
   (`crates/synth-backend-riscv/src/riscv_op.rs:159`).
2. **D — rely on a different mitigation.** Compile-time bounds check;
   MPU region; hardware does not speculate.
3. **A — accept the residual risk** with explicit rationale, e.g. because the
   op is not attacker-controlled, or because the attacker model is
   single-tenant.

## 2. Per-rule decisions

Rules below are real, current Synth lowerings. Source location is given so a
reviewer can re-check the decision after refactors.

| # | Rule / Lowering | Speculative-sensitive op | Decision | Mitigation in place / TODO | Rationale |
|---|---|---|---|---|---|
| 1 | `generate_load_with_bounds_check` (Software mode) — `instruction_selector.rs:2950` | bounds-checked i32 load (`ADD temp,addr,#end_offset; CMP temp,R10; BHS Trap_Handler; LDR rd,[R11,addr,#offset]`) | **D** | The `BHS Trap_Handler` is a *taken* branch when out-of-bounds. On Cortex-M0/M3/M4/M33 the pipeline does not speculate the not-taken path past the load. Thumb-2 `BHS` is resolved in EX, the `LDR` is the next fetch — there is no speculative window long enough on these cores. | In-order Cortex-M; single-tenant. Matches Wasmtime 44.0.0 "csdb off by default" on aarch64, which itself was justified by other in-order cores doing the same. |
| 2 | Same lowering on Cortex-M7 / M55 | bounds-checked i32 load | **F (opt-in)** | TODO: add `--mitigate-spectre-v1` CLI flag that inserts `DSB SY` between `BHS` and `LDR`. Falls back to **D** today. | M7 has limited speculation but no cross-domain secret. Provide the knob (per Wasmtime `use_csdb` setting) but default off; mirrors Wasmtime 44.0.0. |
| 3 | `generate_load_with_bounds_check` (Masking mode) — `instruction_selector.rs:2989` | bounds-checked load via `AND addr,addr,R10` (mask = `memory_size - 1`, power-of-2) | **D** | AND-mask makes the address unconditionally in-bounds at the architectural level; there is no mispredict, no transient window. This is the [Blade](https://cseweb.ucsd.edu/~dstefan/pubs/vassena:2021:blade.pdf)-style index-masking mitigation. | Masking is itself the strongest mitigation against Spectre-v1 BCB. Recommended config for Cortex-M55. |
| 4 | `generate_load_with_bounds_check` (None mode) — `instruction_selector.rs:2965` | `LDR rd,[R11,addr,#offset]` with **no** check | **D** | This mode is the documented "rely on MPU" path (`BoundsCheckConfig::None` docstring at `instruction_selector.rs:19`). Out-of-bounds loads fault via the MemManage exception. No speculative bypass possible because there is no software check to bypass. | Hardware MPU is the architectural mitigation; the attacker cannot speculate past an MPU fault. |
| 5 | `generate_store_with_bounds_check` (Software) — `instruction_selector.rs:3014` | bounds-checked i32 store | **D** | Same reasoning as #1. Additionally, stores do not produce speculative-data values, so the canonical Spectre-v1 BCB chain (load → use-in-second-load) is broken at the source. | Same as #1. Stores are not a Spectre-v1 read primitive. |
| 6 | `generate_subword_load_with_bounds_check` (LDRB / LDRH / LDRSB / LDRSH) — `instruction_selector.rs:892-905` | sub-word bounds-checked load | **D** | Identical structure to #1 with smaller `access_size`. The bounds check `addr <= R10 - k` (`k = offset + access_size`, #752 wraparound-safe shape) is exact, no rounding error. | In-order core; same reasoning as #1. |
| 7 | i64 load lowering `generate_i64_load_with_bounds_check` — `instruction_selector.rs:1721` | bounds-checked 8-byte load (LDR+LDR pair) | **D** | The bounds check uses `access_size = 8`, so the high word's read is covered by the same compare. | Same as #1, plus the i64 read is split into two ARM `LDR` issues that the in-order core executes sequentially. |
| 8 | `add_with_shift` pattern rule — `rules.rs:1887` (Pattern: `I32Shl` then `I32Add` → `ADD rd, rn, rm LSL #amount`) | scaled-index address arithmetic — analog of Cranelift `load(iadd(base, ishl(index, amt)))` | **A (with constraint)** | The shift `amount` is currently hard-coded to `2` in the synthesized replacement (`rules.rs:1901`) and is documented as "would be extracted from pattern". **Constraint**: this rule is currently *not* selected for address computation in real codegen (it's an unused standard rule until `RuleApplicator::apply_rules` performs the rewrite at `pattern_matcher.rs:201-208`). The arm_backend path uses `InstructionSelector::select_with_stack` which lowers loads via `generate_load_with_bounds_check`, not via this fusion rule. See regression test `tests/regression_spectre_cve_2026_34971.rs`. | **This is the closest synth analog to GHSA-jhxm-h53p-jm7w (CVE-2026-34971).** We accept residual risk while the rule is inert, but the regression test fails fast if anyone wires the unbound-`amount` rule into the real lowering pipeline without also extracting `amount` from the matched `I32Const`. |
| 9 | `Select` lowering — `instruction_selector.rs:1305` (`CMP rcond,#0; MOV rd,rval1; SelectMove rd,rval2`) | conditional move used for masking | **D** | Cortex-M `IT`/`MOVEQ` is *architecturally* conditional, not speculative — the move occurs (or not) after the flag is settled. There is no transient bypass window. | ARM IT-blocks are predicated execution, not branch speculation. |
| 10 | `BrIf` (conditional branch) — `instruction_selector.rs:1082` | branch on attacker-controlled condition | **D** | On Cortex-M0/M3/M4 there is no branch predictor; on M7 the predictor exists but the secret-of-another-domain prerequisite is absent (single tenant). | Single-tenant threat model. |
| 11 | `BrTable` (cascading CMP/BEQ) — `instruction_selector.rs:1266` | branch on attacker-controlled index | **D** | The lowering is a *linear chain of compares* (`CMP rn,#i; BEQ target_i`), **not** a memory-indexed jump table (`LDR pc,[base,index,LSL #2]`). A linear chain has no speculative load primitive at all. | Cortex-M `TBB`/`TBH` is not used here, eliminating the indirect-jump speculation path that exists on aarch64. If we later add `TBB`/`TBH`, revisit this row. |
| 12 | `CallIndirect` — `instruction_selector.rs:1055` (pseudo-op expanded by encoder) | indirect call via table | **D** | Synth's call_indirect lowering does a *runtime type check* (sig match) before the indirect branch. Speculation past the BL would only execute attacker-chosen code if the indirect target itself were attacker-controlled in a way that crosses a security domain — and there is no second domain. Cortex-M0/M3/M4 has no indirect branch predictor. | Single-tenant; in-order cores. M7 has a BTAC but again no cross-domain secret. |
| 13 | `MemoryGrow` — `instruction_selector.rs:1013` | grow memory by attacker-controlled count | **D** | On bare-metal targets memory is *fixed*: `MemoryGrow` returns −1 (compile-time wired). No actual growth happens, so no speculative window into a yet-unallocated region. | Documented in README §Features: "memory.grow returns −1 on embedded (fixed memory)". |
| 14 | `MemorySize` — `instruction_selector.rs:1008` | read memory size | **D** | Returns the static R10 value (pages = bytes >> 16). No memory access. | Architectural read of a fixed register. |
| 15 | `GlobalGet` / `GlobalSet` — `instruction_selector.rs:1288-1303` | indexed load/store of WASM globals | **D** | Index is *static* (compile-time constant — it's a WASM immediate, not a stack value). The lowering is `LDR rd, [R9, #index*4]` with a fixed immediate. No attacker-controllable address arithmetic. | Static index ⇒ no Spectre-v1 vector. |
| 16 | RISC-V `lower_load_word` — `selector.rs:507` | i32 load on RV32 | **A (documented gap)** | The RV32 lowering currently emits `add tmp, s11, addr; lw dst, offset(tmp)` with **no bounds check** (`crates/synth-backend-riscv/src/selector.rs:507`). This is the documented "rely on PMP" path. **Gap**: the equivalent `BoundsCheckConfig` selector knob does not exist on the RV32 side yet. | RV32 PMP (Physical Memory Protection) is the analog of the Cortex-M MPU. Out-of-bounds loads fault via access exception; no speculative bypass. RV32IM (no Zicond, no branch predictor in the typical bare-metal microcontroller core e.g. ESP32-C3, K210) does not speculate. Document the gap; do not synthesise a fence. |
| 17 | RISC-V `lower_load_subword` — `selector.rs:527` | sub-word load on RV32 | **D** | Same as #16. | Same as #16. |
| 18 | RISC-V `lower_store` — `selector.rs:569` | i32/sub-word store on RV32 | **D** | Stores are not a read primitive; PMP enforces bounds at hardware level. | Same as #5 / #16. |
| 19 | RISC-V `lower_if` — `selector.rs:607` (`beq cond, zero, Lelse`) | branch on attacker-controlled condition (RV32) | **D** | RV32 simple bare-metal cores do not have a branch predictor with cross-domain reach. | Single-tenant. |
| 20 | Peephole `try_optimize_3` strength reduction (MUL → LSL) — `peephole.rs:170` | constant-fold of multiply by power of two | **D** | Pure arithmetic rewrite, no memory access in either direction, no branch. | Not a speculation-sensitive op. |
| 21 | Peephole STR→LDR forwarding — `peephole.rs:124` | store-load forwarding when registers match | **D** | The optimization is *removing* a load whose value the compiler can prove is already in a register; it never *introduces* a speculative load. Cortex-M has no store-to-load forwarding speculation. | Forwarding is a compile-time identity; no transient state. |

### Coverage summary

* **F (fence required):** 0 rules require a mandatory fence.
* **F (opt-in):** 1 row (#2 — Cortex-M7/M55 software bounds check) is wired
  for a future `--mitigate-spectre-v1` flag.
* **D (other mitigation suffices):** 19 rules.
* **A (accepted residual):** 2 rules (#8 `add_with_shift` standard rule, gated
  by a regression test; #16 RV32 missing bounds-check knob, gated by docs).

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
`add_with_shift` (`rules.rs:1887`):

```rust
// rules.rs:1887
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

**Why synth is not exploitable today:** `RuleApplicator::apply_rules`
(`pattern_matcher.rs:201-208`) currently **does not actually rewrite** the
matched ops to the rule's `Replacement` — it returns the original ops. The
unbound `amount = 2` therefore never reaches generated code. The aarch64
sandbox-escape shape is latent, not live.

**Mitigation applied:** a regression test
`crates/synth-synthesis/tests/regression_spectre_cve_2026_34971.rs` asserts
that the standard rule's hard-coded `amount` is *either* fixed (to extract
from the pattern) *or* the rule remains gated (the applicator does not
actually rewrite). The test fails loudly if a future patch enables rewriting
without extracting `amount`, preventing the GHSA-jhxm-h53p-jm7w shape from
landing.

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
  (`rules.rs:1052`, `MveLoad`) which by construction is a 128-bit access for
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
  transcoding bugs. Synth's component-model path lives in
  `crates/synth-abi/`; the transcoding helpers there should be audited
  against these advisories in a follow-up.
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
  (`fence iorw, iorw` already present at
  `crates/synth-backend-riscv/src/riscv_op.rs:159`).

## 5. Review cadence

This document is reviewed:

* on every Wasmtime major release (currently every ~6 weeks);
* on every new Bytecode Alliance security advisory cluster;
* when the synth lowering pipeline changes shape (new pass, new rule, new
  target architecture).

The maintainer of each touched lowering must update the row in §2 and either
add a regression test or extend the policy rationale.
