# Binary safety checks for synth's ARM + RISC-V targets

Status: design / proposal — no code in this PR. Targets a follow-up
implementation series tracked in §Roadmap.

Last reviewed: 2026-05-14. Reviewer: synth-core.

## 0. Scope and non-goals

Synth compiles WebAssembly to bare-metal ELF for ARMv7-M / ARMv8-M
(Cortex-M3/M4/M7/M33/M55) and RV32IM / RV32IMAC / RV32GC. The PulseEngine
threat model is **single-tenant** (one WASM module per MCU, no co-resident
adversary) but the *failure model* still needs runtime guards: silent
memory corruption on a flight-controller MCU or a medical-pump MCU is just
as bad as a sandbox escape on a hyperscaler.

This document specifies the **opt-in safety check surface** synth will
expose. Each check is independently selectable, has a documented fast
path that exploits hardware, and a documented slow software fallback for
silicon that lacks the hardware.

### Out of scope

* Multi-tenant sandboxing — that is loom / kiln territory and lives in
  `docs/architecture/SYNTH_LOOM_RELATIONSHIP.md`.
* Spectre / transient-execution coverage — already specified in
  `docs/spectre-policy.md`. This document only references it.
* Memory *allocator* hardening for the host runtime (synth produces ROM
  + RW images; the linear-memory base is fixed at link time).
* RISC-V CFI extension Zicfi**lp**/Zicfi**ss** detailed encodings — only
  the policy surface is fixed here; the encoder is a follow-up.

### Existing coverage (synth as of 2026-05-14)

* **Divide-by-zero traps** — `crates/synth-synthesis/src/instruction_selector.rs:3895`
  (I32DivU/I32DivS/I32RemU/I32RemS, ARM `UDF #0`).
* **Signed-division overflow (INT_MIN / -1) traps** —
  `instruction_selector.rs:3967` (ARM `UDF #1`).
* **Software bounds check (`--bounds-check` CLI flag)** —
  `instruction_selector.rs:2950` (`CMP/BHS Trap_Handler` before each load /
  store). Three modes: `None`, `Software`, `Masking`.
* **MPU configuration** — `crates/synth-backend/src/mpu.rs` and
  `mpu_allocator.rs`. Cortex-M MPU regions are programmable from the
  generated startup code.
* **PMP configuration** — `crates/synth-backend-riscv/src/pmp.rs`. RV32
  Physical Memory Protection entries (NAPOT and TOR modes).
* **Trap handler** — `crates/synth-cli/src/main.rs:1894` (ARM,
  `generate_trap_handler`) and `crates/synth-backend-riscv/src/startup.rs:88`
  (RV32, `synth_trap_handler` weak symbol).

What this document adds: a unified `--safety` profile surface, the missing
checks (stack overflow, CFI, type-confusion at component boundaries,
linear-memory poisoning), and the per-check selection of hardware-assisted
fast path vs software slow fallback.

## 1. Threat model

Synth's defensive posture has to cover the following bug / attack classes:

| Class | Example | Detection latency we want |
|---|---|---|
| Linear-memory out-of-bounds load/store | Off-by-one in a WASM-side buffer copy | Instruction-level (trap on the offending insn) |
| Integer divide-by-zero | WASM-side `i32.div_s` with a zero divisor | Instruction-level |
| Signed-division overflow | `INT_MIN / -1` (ARM SDIV silently returns INT_MIN, WASM requires trap) | Instruction-level |
| Stack overflow | Deeply-recursive WASM, or an attacker-controlled allocation pattern in a generated call chain | Function-prologue-level (one cycle) |
| Indirect-call type confusion | `call_indirect` with a forged signature, or a corrupted function table | Call-site, before the BL/JALR is taken |
| Return-address corruption | Stack-based memory bug overwrites LR / `ra` on the stack | At RET / `jr ra` |
| AAPCS-invariant violation | Callee-saved register R4–R11 not restored, or SP misaligned at return | Function-epilogue-level |
| Linear-memory use-after-free / use-uninitialised | Reading not-yet-written bytes in the WASM heap | First read (poisoned bytes are well-known) |
| Component-model type confusion | A host call lifts a `string` from `(ptr, len)` where `len` exceeds the linear memory or where the bytes are not UTF-8 | At the lift boundary |

### Beneficiaries

| Audience | What they care about | Profile they'll select |
|---|---|---|
| ASIL-D / IEC 62304 auditor | Documented, deterministic trap on every UB path | `--safety asil-d` (all checks on, no masking — wants explicit trap, not silent recovery) |
| Fuzz-test harness author (cargo-fuzz, AFL++) | Crash on bug, fast cycles | `--safety fuzz` (bounds + div + overflow on, CFI off for speed, poison on) |
| Defensive RTOS author (Zephyr/Mbed/FreeRTOS) | Survive a misbehaving component | `--safety rtos` (MPU/PMP bounds, MSPLIM stack guard, BTI on if available) |
| Performance-first embedded developer | Pay only for what they need | `--safety none` (current default) |
| Confidential-compute / mission-critical | Spectre + CFI + canaries | `--safety paranoid` (everything + Spectre-v1 fence on M7/M55) |

## 2. CLI surface (proposed)

### Profile flag

```text
--safety <PROFILE>
```

Where `<PROFILE>` is one of `none | fuzz | rtos | asil-d | paranoid`.

### Per-check overrides

For fine-grained control, individual `--safety-X` flags override the profile.

```text
--safety-bounds      <mpu|pmp|soft|mask|off>
--safety-div         <on|off>                    # already implemented
--safety-div-overflow <on|off>                   # already implemented
--safety-stack       <msplim|psplim|soft|off>
--safety-cfi-fwd     <bti|landingpad|soft|off>
--safety-cfi-bwd     <pac|shadowstack|soft|off>
--safety-prologue    <on|off>                    # AAPCS canary on saved regs
--safety-poison      <on|off>                    # linear-mem poisoning
--safety-cm-types    <on|off>                    # component-model lift checks
--safety-spectre-v1  <fence|mask|off>            # see spectre-policy.md
```

### Profile expansion (semantics)

| Check | `none` | `fuzz` | `rtos` | `asil-d` | `paranoid` |
|---|---|---|---|---|---|
| bounds | off | mpu→soft | mpu / pmp | soft | soft + mpu |
| div / div-overflow | on | on | on | on | on |
| stack | off | off | msplim / psplim | msplim / psplim | msplim + soft canary |
| cfi-fwd | off | off | bti (if M33/M55) | bti / landingpad | bti / landingpad |
| cfi-bwd | off | off | off | pac (if v8.1-M) / shadowstack | pac / shadowstack |
| prologue canary | off | off | off | on | on |
| poison | off | on | off | on | on |
| cm-types | on | on | on | on | on |
| spectre-v1 | off | off | off | off | fence on M7/M55 |

The `div` / `div-overflow` columns are `on` everywhere because they are
WASM spec-required traps; they cannot be turned off without making the
output non-WASM-compliant. They are listed for completeness.

### Output

The `synth compile` command will emit, alongside the ELF, a
`safety-manifest.json` describing exactly which checks are active. This
is consumed by the verifier (`synth verify`) and by `synth disasm` to
annotate the disassembly.

## 3. Per-check design

Notation in each subsection:
* **Threat** — concrete bug or attack class.
* **Fast path** — hardware-assisted lowering. Target gate listed.
* **Slow path** — software fallback. Estimated cycle cost.
* **Trade-off** — when each is appropriate.
* **Code locations** — files that need to change. No code in this PR.

---

### 3.1 Memory bounds (MPU / PMP / software / mask)

**Threat.** WASM `i32.load`, `i32.store`, `i64.load`, `f32.load`,
`f64.load`, etc. with an attacker-controlled address can read or
write outside the linear-memory region. WASM semantics require a trap.

**Fast path A — ARM MPU.** Program one MPU region covering the linear
memory (R/W, NX). Allocate the WASM heap inside that region. The MPU
faults on out-of-bounds accesses via the **MemManage exception** — zero
runtime cost per load/store. Already implemented in
`crates/synth-backend/src/mpu.rs` and configurable via the existing
`BoundsCheckConfig::None` mode (which relies on hardware).

**Fast path B — RV32 PMP.** Same idea via PMP entries. NAPOT mode
supports power-of-2 regions cheaply; TOR mode supports arbitrary
ranges. Already implemented in `crates/synth-backend-riscv/src/pmp.rs`.

**Fast path C — index masking.** When linear memory is a power of 2,
`AND addr, addr, #(size-1)` makes every access architecturally in-bounds.
Zero branches, ~1 cycle. Already implemented as
`BoundsCheckConfig::Masking`. *Note:* this is **also** the strongest
Spectre-v1 mitigation (see `docs/spectre-policy.md` row #3); it does not
fault on OOB, it wraps, which is wrong for ASIL-D — only use for `fuzz`
profile where wrap-on-fault is acceptable.

**Slow path — software CMP/BHS.** Already implemented at
`instruction_selector.rs:2950`:
```
ADD temp, addr_reg, #(offset + access_size - 1)
CMP temp, R10            ; R10 = linear-mem size
BHS Trap_Handler
LDR rd, [R11, addr_reg, #offset]
```
Cost: ~3 cycles + 1 mispredict penalty on M7. ~25 % bytecode size
inflation on memory-heavy WASM. This is the only portable mode for
Cortex-M0/M0+ (no MPU) and bare RV32I cores without PMP.

**Trade-off.** Default for `--safety asil-d` is **soft + mpu** —
software check first (deterministic, auditable trap address), MPU as
defense in depth. `fuzz` uses MPU for speed because the crash is the
signal. `rtos` uses MPU alone (zero overhead in the hot path) and lets
the RTOS reload the offending module.

**Code locations.**
* `crates/synth-synthesis/src/instruction_selector.rs:2950` (ARM, exists)
* `crates/synth-backend-riscv/src/selector.rs:507` (RV32 — needs the
  equivalent `BoundsCheckConfig` knob; documented gap in
  `spectre-policy.md` row #16)
* `crates/synth-cli/src/main.rs:156` (CLI flag plumbing; replace
  `--bounds-check` with the unified `--safety-bounds`)

---

### 3.2 Integer divide-by-zero (existing, generalize)

**Threat.** WASM `i32.div_s`, `i32.div_u`, `i32.rem_s`, `i32.rem_u`,
`i64.div_*`, `i64.rem_*` must trap when the divisor is zero. ARM SDIV /
UDIV silently return 0 (architectural quirk); RV32M `div` / `divu` return
−1 / `2^32 − 1`.

**Fast path (ARM).** 4-instruction sequence at
`instruction_selector.rs:3895`:
```
CMP  divisor, #0
BNE  +0                 ; skip UDF if non-zero
UDF  #0                 ; UsageFault -> Trap_Handler
UDIV rd, dividend, divisor
```
Cost: 3 cycles in the happy path (CMP + predicted-taken BNE + UDIV);
the UDF is one half-word and is never executed unless trapping. Zero
branch mispredicts in the steady state on Cortex-M.

**Fast path (RV32).** Equivalent sequence using `beq divisor, x0, .Ltrap`
and `unimp` (or `ecall`). Same cost. **Needs implementation** on the
RISC-V backend — selector currently does not emit the guard.

**Slow path.** No software-only fallback is meaningfully slower; the
4-instruction guard *is* the slow path. There is no hardware
divide-by-zero exception on ARMv7-M (the FPU has one, the integer unit
does not).

**Trade-off.** `--safety-div` is **always on** because turning it off
makes the output non-conformant. Listed for completeness.

**Code locations.**
* `crates/synth-synthesis/src/instruction_selector.rs:3877` (ARM, exists)
* `crates/synth-backend-riscv/src/selector.rs` (RV32, missing — open
  question §5.2)

---

### 3.3 Signed-division overflow (INT_MIN / -1)

**Threat.** `INT_MIN / -1` is mathematically `2^31`, which overflows
signed 32-bit. WASM requires a trap. ARM SDIV silently returns INT_MIN;
RV32M `div` silently returns INT_MIN; CompCert's [PR 442] documents the
same. (Same applies for i64: `INT64_MIN / -1`.)

**Fast path (ARM).** Already implemented at
`instruction_selector.rs:3967`:
```
MOVW tmp, #0 ; MOVT tmp, #0x8000     ; tmp = INT_MIN
CMP  dividend, tmp
BNE  skip
CMN  divisor, #1                     ; check divisor == -1
BNE  skip
UDF  #1
skip:
SDIV rd, dividend, divisor
```
Cost: 7 cycles in the unlikely INT_MIN path; 4 cycles in the common case
(CMP + predicted-not-taken). Negligible footprint expansion.

**Fast path (ARMv8.1-M, future).** ARMv8.1-M Mainline (Cortex-M55) has
`SQRDMULH`-style saturating instructions but **no saturating divide**.
The above sequence is the canonical lowering.

**Slow path.** Same. There is no faster encoding.

**Trade-off.** Same as 3.2 — always on for WASM compliance.

**Code locations.**
* `crates/synth-synthesis/src/instruction_selector.rs:3947` (exists for
  ARM, missing for RV32 and for i64 — open question §5.3)

---

### 3.4 Stack overflow (MSPLIM / PSPLIM / soft canary)

**Threat.** Deep recursion or attacker-controlled call-graph explosion
exhausts the MCU's tiny RAM and silently corrupts whatever lives below
the stack (heap, BSS, `.data`). On Cortex-M without MSPLIM, a stack
overflow is **silent** — execution continues with corrupted globals
until a fault is hit elsewhere.

**Fast path A — ARMv8-M MSPLIM / PSPLIM (Cortex-M33, M55, M23).**
ARMv8-M adds two stack-limit registers: `MSPLIM` for the main stack
and `PSPLIM` for the process stack. The CPU compares SP against the
limit on every push/pop. If SP would go below the limit, a **UsageFault
(STKOF)** is raised. **Zero per-call overhead.** Set once at startup
from the generated `Reset_Handler`.

**Fast path B — RV32 hardware stack-limit.** RISC-V does *not* have a
hardware stack-limit register in the base RV32I privileged
architecture. The RISC-V Hypervisor extension has `henvcfg.STCE` but
that is unrelated. **No RV32 hardware fast path exists** — must fall
back to the soft canary.

**Slow path — soft canary.** Emit a per-call prologue check:
```
LDR  r12, =__stack_limit       ; or keep in a callee-saved reg
CMP  sp, r12
BLS  Trap_Handler              ; SP <= limit ⇒ overflow
```
Cost: 2–3 cycles per function call. Acceptable for `--safety asil-d` on
Cortex-M3/M4 (which lack MSPLIM). On RV32, the equivalent is:
```
lui   t0, %hi(__stack_limit)
addi  t0, t0, %lo(__stack_limit)
bgeu  t0, sp, .Ltrap
```

**Slow path B — stack canary.** A magic word at the bottom of each
frame, validated at epilogue. Costs ~4 cycles per call. Catches stack
*smashing* (heap-side buffer overruns that scribble into the stack)
but not exhaustion. Different threat — listed under §3.7 (prologue
invariants).

**Trade-off.** ARMv8-M targets should always use MSPLIM (zero cost).
ARMv7-M targets pay the soft check in `--safety rtos+`. RV32 has no
free path; only `--safety asil-d` / `paranoid` pays for the soft check.

**Code locations.**
* `crates/synth-backend/src/cortex_m.rs` (Reset_Handler — needs to set
  `MSPLIM` and `PSPLIM` for v8-M targets)
* `crates/synth-synthesis/src/optimizer_bridge.rs:4441` (prologue
  insertion point — add the soft canary emission here for v7-M)
* `crates/synth-backend-riscv/src/startup.rs` (RV32 startup — symbol
  `__stack_limit` and the prologue helper)

---

### 3.5 CFI forward-edge (BTI / landing pad / soft)

**Threat.** An attacker who can corrupt the function-table entry or
the `call_indirect` index can transfer control to an arbitrary code
address. On a stripped ROM image this is restricted to legal function
entries, but anywhere the WASM-side has writeable function pointers
(globals, exception tables) the attacker can pivot to mid-function gadgets.

**Fast path A — ARMv8.1-M Branch Target Identification (BTI).**
Cortex-M55, Cortex-M85 (and ARMv8.5-A on the application side).
Insert a `BTI` instruction (encoded as a hint, executes as NOP on
non-BTI-aware CPUs) at every legal indirect-branch target. The MMU /
SAU enforces that an indirect branch (`BX`, `BLX`, `BXNS`, `BLXNS`)
*must* land on a `BTI` instruction or the CPU faults. **One half-word
per function, zero runtime cost** when the BTI executes (it's a NOP);
~2 bytes of code size per indirect target.

Encoding: `BTI` = `0xF3AF 8B0F` (Thumb-2 hint, NOP on older cores).

**Fast path B — RV32 Zicfilp (CFI Landing Pad).** RISC-V Zicfilp
(ratified 2024-06; `Zicfilp` in the *Control Flow Integrity*
extension family) defines a `lpad` instruction inserted at every
indirect-branch target. JALR with non-zero `rd` will fault unless
the next instruction is `lpad` with a matching label. Same idea, same
zero-cost. Encoder support: pending — see `riscv_op.rs`. Software
support: Linux kernel has BTI/Zicfilp wiring since 2025.

**Slow path — software CFI.** Emit a target-table check at every
`call_indirect`:
```
; assume r0 = target address from function table
LDR  r1, =CFI_VALID_TARGETS_TABLE
LDR  r2, =CFI_VALID_TARGETS_END
.Lscan:
  LDR  r3, [r1], #4
  CMP  r3, r0
  BEQ  .Lok
  CMP  r1, r2
  BLO  .Lscan
  B    Trap_Handler
.Lok:
  BLX  r0
```
Cost: O(N) per indirect call. Acceptable when N is small
(< 32 entries). Better: use a sorted table and binary search (~log N).
Even better: use a bloom filter (~3 cycles) when false positives are
acceptable (which they are — BTI doesn't catch every gadget either).

**Trade-off.** Cortex-M55 / M85 get BTI for free. M33 has it
optionally (depends on the silicon vendor). M3/M4/M7 must use software
CFI or accept the residual risk. RV32 with Zicfilp gets the free path;
RV32 without falls back to software.

**Code locations.**
* `crates/synth-backend/src/encoder.rs` (ARM encoder — add `BTI`
  encoding; emit at function entry when the function is reachable via
  `call_indirect`)
* `crates/synth-backend-riscv/src/encoder.rs` (RV32 — add `lpad`)
* `crates/synth-synthesis/src/instruction_selector.rs:1055`
  (`CallIndirect` lowering — emit the software-table check when BTI is
  off and `--safety-cfi-fwd=soft`)
* `crates/synth-backend/src/elf_builder.rs` (note program header
  `PT_GNU_PROPERTY` with `GNU_PROPERTY_AARCH64_FEATURE_1_BTI` for
  loaders that consult it — relevant only when the ELF is loaded by a
  hypervisor / dynamic loader; bare-metal images don't need this)

---

### 3.6 CFI backward-edge (PAC / shadow stack / soft)

**Threat.** A stack-based buffer overflow (or a Spectre-v1 style
gadget) overwrites the saved LR / `ra` on the stack, redirecting the
function's return to attacker-chosen code. This is the classic ROP /
return-into-libc primitive.

**Fast path A — ARMv8.1-M Pointer Authentication (PAC).** Cortex-M85
and later (and Cortex-M55 *optionally*) implement a stripped-down PAC.
At function entry: `PAC R12, LR, SP` signs LR using a hardware key and
SP-as-modifier and stores the signed pointer in R12. At return:
`AUT R12, LR, SP` verifies — if the signature is wrong, the CPU faults.
**One half-word at entry + one at exit; zero RAM cost** (the signature
lives in an unused-by-AAPCS register, R12).

Encoding: `PAC R12, LR, SP` = ARMv8.1-M hint encoding; on older cores
it executes as `MOV R12, LR` (degraded but functional). The CLI must
gate this behind `cortex-m85` / `cortex-m55+pac` target flags.

**Fast path B — RV32 Zicfiss (Shadow Stack).** RISC-V Zicfiss adds a
hardware shadow stack manipulated by `sspush` / `sspopchk`. At
prologue: `sspush ra` (writes to a CSR-controlled shadow stack). At
epilogue: `sspopchk ra` (faults if the on-stack `ra` differs from the
shadow). **Zero RAM cost in the user stack**, ~1 cycle per call.

**Slow path A — software shadow stack.** Reserve a separate region
(allocated via MPU/PMP at startup, made non-writable to the WASM
heap), and maintain a parallel stack of return addresses:
```
; prologue
LDR  r12, =shadow_sp
LDR  r1,  [r12]
STR  LR,  [r1], #4
STR  r1,  [r12]
; epilogue
LDR  r12, =shadow_sp
LDR  r1,  [r12]
LDR  r2,  [r1, #-4]!
STR  r1,  [r12]
CMP  r2,  LR
BNE  Trap_Handler
BX   LR
```
Cost: ~6 cycles per call (3 prologue + 3 epilogue). Significant
bytecode-size hit. Acceptable for `--safety asil-d` on cores without
PAC; the shadow stack itself must be MPU-protected from WASM-side
writes.

**Slow path B — return-address canary.** Cheaper than a full shadow
stack: XOR LR with a random word stored in a callee-saved register at
prologue, XOR back at epilogue and check it matches the original. ~2
cycles per call. *Not* a strong defense — a single corrupted byte can
unmask the canary — but useful for the `fuzz` profile to catch
non-targeted corruption.

**Trade-off.** PAC / Zicfiss for the free path; software shadow stack
for `--safety asil-d` on older silicon; the XOR canary is `fuzz`-only.
Synth should *never* default to "off" on ARMv8.1-M targets when the
profile is `asil-d` or `paranoid`.

**Code locations.**
* `crates/synth-backend/src/encoder.rs` (PAC encoding for ARMv8.1-M)
* `crates/synth-backend-riscv/src/encoder.rs` (sspush/sspopchk for
  Zicfiss)
* `crates/synth-synthesis/src/optimizer_bridge.rs:4441` (prologue —
  emit the shadow-stack helper when PAC/Zicfiss is unavailable)
* `crates/synth-backend/src/mpu_allocator.rs` (carve out an MPU region
  for the software shadow stack, R/W to privileged, no access to
  unprivileged / WASM side)

---

### 3.7 Prologue / epilogue AAPCS invariants

**Threat.** A pass-internal bug (synth's own optimizer) or a WASM-side
inline assembly trick (not currently supported but loom may allow it)
violates AAPCS — e.g., a function fails to restore R4–R11, or leaves SP
unaligned, or returns through a non-LR register. This is not an attack
vector against the WASM module; it's a **compiler defect detector**.

PR #108 in this repository (`fix(opt): systematic AAPCS-clobber audit`)
showed how easy it is to clobber R0–R3 across an i64 op and have the
test pass anyway because the immediate caller happened not to use R3.
A runtime check would have caught that fuzz target on the first run.

**Fast path.** None. AAPCS is a software contract; the CPU does not
enforce it. (ARM's R28-only push/pop forms are an architectural hint,
not a guarantee.)

**Slow path — XOR-checksum of callee-saved.** At prologue:
```
EOR r12, r4, r5
EOR r12, r12, r6
EOR r12, r12, r7
... (r8, r9, r10, r11)
PUSH {r12}        ; checksum on stack
```
At epilogue:
```
EOR r12, r4, r5
EOR r12, r12, r6 ; etc.
POP {lr}
CMP r12, lr      ; lr is wrong here — use a temp, structure differs;
                 ; sketch only
BNE Trap_Handler
```
Cost: ~10 cycles per call. Only useful during fuzz / regression-test
campaigns, not production. Listed under `--safety-prologue` as a
debug-build aid.

**Trade-off.** `asil-d` audit benefits from this even though it is
expensive — it's a *compiler-bug* canary, not a runtime-attack canary.
Default OFF; `fuzz` and `paranoid` flip it on.

**Code locations.**
* `crates/synth-synthesis/src/optimizer_bridge.rs:4441` (prologue) and
  `:4450` (epilogue insertion)
* New: `crates/synth-synthesis/src/safety/prologue_check.rs`

---

### 3.8 Linear-memory poisoning

**Threat.** A WASM module reads bytes from its linear memory that it
never wrote, getting whatever the previous tenant left behind. In a
single-tenant MCU this is "garbage from boot"; in a kiln multi-component
future it is **a confidentiality leak** between WASM components
sharing one MCU.

**Fast path.** None — there is no hardware "uninitialised memory"
detection on Cortex-M or RV32. (Application-class CPUs may have MTE /
LAM; not relevant here.)

**Slow path A — zero-on-allocation.** The generated startup code
zeros the entire linear-memory region at Reset_Handler. Cost: O(N)
once at boot. Already standard for `.bss` — synth just has to extend
it to the linear-memory region. This is the cheapest correctness
fix and catches all use-uninitialised bugs at the WASM semantic level
(reads return 0 ⇒ deterministic).

**Slow path B — pattern fill (debug only).** Fill with `0xDEADBEEF`
or `0xA5A5A5A5` at startup so that a use-uninitialised access has a
distinctive value an analyst can spot. Cost: same as A. Off in
production builds.

**Slow path C — shadow-byte tracking (MSan-style).** Track a 1-bit
shadow per byte ("written?"). Every store sets the shadow; every load
checks it. Cost: ~3x slower, doubles memory footprint. Only viable
during **fuzz / dev**; never production.

**Trade-off.** Path A (zero-on-boot) is *de facto* free in cycle terms
because boot time is amortised across the whole device uptime. It
should be the default for every profile from `none` upward. Path C is
opt-in for the `fuzz` profile.

**Code locations.**
* `crates/synth-backend/src/cortex_m.rs` (Reset_Handler — extend
  `.bss` zero-fill to cover the WASM linear-memory region)
* `crates/synth-memory/src/lib.rs` (allocation API — already supports
  zeroed pages)
* New: `crates/synth-synthesis/src/safety/msan.rs` (only if Path C is
  pursued; expected ~6-month follow-up)

---

### 3.9 Component-model type confusion

**Threat.** A host call lifts a `string` argument from a `(ptr, len)`
pair. If `ptr` or `len` is corrupt (e.g., from a buggy WASM-side
implementation, or a forged ABI struct from another component), the
host could read out-of-bounds bytes, present them as UTF-8 strings, or
interpret arbitrary numbers as enum tags. This is **the canonical
WIT/Canonical-ABI failure mode**.

**Fast path.** None directly in hardware. However, the *bounds*
component of the check piggybacks on §3.1 (MPU/PMP). What remains is
the semantic check: "len fits in the memory region" and "bytes are
valid for the lifted type".

**Slow path — generated lift wrappers.** Synth's `synth-abi` crate
already lowers/lifts Component Model values. Add a guarded
`safe_lift_*` family that:
1. Checks `ptr + len <= linear_memory_size` (covered by §3.1 if active).
2. For `string`: validates UTF-8 byte-by-byte.
3. For `list<T>`: validates per-element type for `T` recursively.
4. For `variant`/`enum`: validates the discriminant against the
   known-good tags.
5. For `flags`: masks unknown bits.

Cost: O(len) per lift — same order as the lift itself. Effectively
free for small data; ~2x cost for large `list<u8>` due to the bounds
sweep.

**Trade-off.** `--safety-cm-types` is **on by default** for every
profile because it is the contract guard at a trust boundary. Turning
it off means the host trusts WASM-side bookkeeping completely — a bad
default. `none` keeps it on; only an explicit `--safety-cm-types=off`
turns it off.

**Code locations.**
* `crates/synth-abi/src/lift.rs` (new `lift_string_checked`,
  `lift_list_checked`, `lift_variant_checked`)
* `crates/synth-abi/src/lower.rs` (no changes — lowering writes data we
  trust)
* `crates/synth-wit/src/parser.rs` (no changes — type info already
  available)
* `crates/synth-synthesis/src/instruction_selector.rs` (component
  trampolines — emit the checked lift wrappers when configured)

---

## 4. Target × check support matrix

| Check | M3 | M4 | M7 | M33 | M55 | M85 | RV32I | RV32IM | RV32IMAC | RV32GC |
|---|---|---|---|---|---|---|---|---|---|---|
| MPU/PMP bounds | yes (8 rg) | yes | yes | yes (v8) | yes (v8) | yes (v8) | optional | optional | optional | optional |
| Software bounds | yes | yes | yes | yes | yes | yes | yes | yes | yes | yes |
| Index masking | yes | yes | yes | yes | yes | yes | yes | yes | yes | yes |
| Div-by-zero trap | yes | yes | yes | yes | yes | yes | needs RV32M | yes | yes | yes |
| Signed div overflow trap | yes | yes | yes | yes | yes | yes | needs RV32M | yes | yes | yes |
| MSPLIM/PSPLIM stack guard | no | no | no | **yes** | **yes** | **yes** | no | no | no | no |
| Software stack canary | yes | yes | yes | yes | yes | yes | yes | yes | yes | yes |
| BTI / Zicfilp | no | no | no | optional | **yes** | **yes** | no | Zicfilp (opt) | Zicfilp (opt) | Zicfilp (opt) |
| Software CFI fwd | yes | yes | yes | yes | yes | yes | yes | yes | yes | yes |
| PAC / Zicfiss | no | no | no | no | optional | **yes** | no | Zicfiss (opt) | Zicfiss (opt) | Zicfiss (opt) |
| Software shadow stack | yes | yes | yes | yes | yes | yes | yes | yes | yes | yes |
| Linear-mem zero-fill | yes | yes | yes | yes | yes | yes | yes | yes | yes | yes |
| MSan shadow (debug) | yes | yes | yes | yes | yes | yes | yes | yes | yes | yes |
| Component-model lift checks | yes | yes | yes | yes | yes | yes | yes | yes | yes | yes |

Legend: **yes** = hardware fast path. *yes* = software fallback only.
*optional* = silicon-vendor option (BTI on M33 is one such — has to be
queried at compile time per the target spec).

## 5. Verification impact

Each runtime check has a follow-on effect on the Rocq proof suite at
`coq/Synth/`:

### 5.1 Helps proofs

* **Bounds (§3.1)** — when active, the proof obligation for memory
  loads simplifies: instead of "either trap or value `v`", the
  postcondition becomes "if in-bounds then `v`, else execution does
  not reach the next instruction". This collapses many disjunctions
  in `Correctness*.v` for `WasmOp::I32Load`, `I32Store`, etc. Expected
  to eliminate ~6 of the 10 current `Admitted` proofs.
* **Div-by-zero (§3.2)** — already integrated. `Correctness*.v` for
  `I32DivS` has T1 result-correspondence proofs.
* **Component-model lift (§3.9)** — type checks at the boundary make
  the proof of `lift ∘ lower = id` go through *without* an additional
  precondition about caller well-typedness.

### 5.2 Complicates proofs

* **Stack overflow (§3.4)** — adds a precondition on every function
  call ("SP is at least N bytes above the limit") that needs to be
  threaded through the proof. Mitigated by: when MSPLIM is used, the
  hardware enforces the property, so the proof just relies on the
  ARMv8-M architectural axiom.
* **CFI (§3.5, §3.6)** — adds a global invariant ("LR has not been
  altered since prologue") that needs to be propagated through every
  call site. PAC makes this easier: the invariant becomes a local
  property of the signed pointer.

### 5.3 Neutral

* **Index masking (§3.1 path C)** — semantics change (out-of-bounds
  wraps rather than traps); the proof works but proves a *different*
  theorem (wrap-correctness instead of trap-correctness). This is why
  masking is `fuzz`-only.
* **Prologue canary (§3.7)** — pure debug-time check; not in the
  proven semantics.

Recommendation: synth's correctness theorems should be parameterised
by the safety profile. The `Compilation.v` `compile_wasm_to_arm`
function would take an additional `safety: SafetyProfile` argument and
the lemma statements would condition on it. This is a ~2-week effort
post-implementation.

## 6. Roadmap & open questions

### Phase 1 — unification (2 weeks)

* Replace the existing `--bounds-check` boolean with a `--safety-bounds`
  enum and a `--safety` profile umbrella flag.
* Emit `safety-manifest.json` alongside each ELF.
* Port the ARM bounds-check selector to RISC-V (fills the gap
  documented in `spectre-policy.md` row #16).
* Add the divide-by-zero + signed-overflow trap for RV32M
  (currently ARM-only).

### Phase 2 — hardware fast paths (4 weeks)

* MSPLIM/PSPLIM initialisation in `cortex_m.rs` for v8-M targets.
* BTI encoding + emission at indirect-call targets for M55/M85.
* PAC encoding for M85 (and M55-optional).
* Verify CompCert-style ELF program headers signal the BTI/PAC
  property for hypervisor-loaded targets.

### Phase 3 — software fallbacks (6 weeks)

* Software stack canary in optimizer_bridge prologue/epilogue.
* Software CFI table for `call_indirect` when BTI is unavailable.
* Software shadow stack as an MPU-protected region.
* Linear-memory zero-fill in startup (likely a 1-day task; already
  half-done).

### Phase 4 — component-model + RV32 CFI (~6 weeks)

* `lift_string_checked`, `lift_list_checked`, `lift_variant_checked`
  in `synth-abi`.
* RV32 Zicfilp / Zicfiss encoder support (depends on opcode
  finalisation; track ratified spec).
* MSan-style shadow byte tracking (only if a fuzz-team request
  materialises).

### Phase 5 — verification integration (2 weeks)

* Parameterise `Compilation.v` and `Correctness*.v` by safety profile.
* Re-prove the existing T1 lemmas under each profile.
* Add new T1 lemmas for the bounds-checked path (currently T2).

### Open questions

1. **Trap handler unification.** ARM uses a `Trap_Handler` label, RV32
   uses `synth_trap_handler` weak symbol. Should the safety-manifest
   describe a single trap callback or one per check class (so the
   firmware can demux div-by-zero from bounds from CFI)?
2. **R10 / R11 reservation on RV32.** ARM reserves R10 = memsize and
   R11 = membase. The RV32 backend uses `s11` for the analog. With
   `--safety-bounds=soft`, do we also reserve `s10` for a stack-limit
   pointer, costing one allocatable callee-saved on every function?
3. **Profile-vs-target precedence.** If the user asks for
   `--safety asil-d` on Cortex-M3 (no MSPLIM, no BTI, no PAC), do we
   (a) silently fall back to software, (b) warn and fall back, or
   (c) refuse to compile? Default plan: (b).
4. **Linear-memory poisoning of MPU-protected pages.** If the WASM
   linear memory is also the shadow stack region (per §3.6), the
   zero-fill might overwrite the prologue's signature on first call.
   Need to sequence the startup carefully — zero-fill first, then
   place the shadow stack.
5. **PAC on Cortex-M55 — is the key per-firmware or per-boot?** A
   per-boot random key defeats offline attacks but breaks
   reproducible builds. Per-firmware (linked in by synth) reduces to
   "secret in ROM" which is trivially extractable on hostile
   silicon. Recommendation: per-boot from TRNG, accept the
   non-reproducible-PAC-fields in the post-PAC binary.
6. **MSan in production?** Path C in §3.8 is documented as fuzz-only,
   but a customer might want it in production for ASIL-D logging.
   The 3x overhead is a tough sell for embedded; default OFF and
   require an explicit `--safety-poison=shadow` to enable.
7. **BTI/Zicfilp interaction with synth's WASM-side `call_indirect`
   type check.** Today synth emits a runtime signature check before
   the indirect branch (per `spectre-policy.md` row #12). Once BTI is
   in place, is the runtime sig-check redundant? **Answer (proposed):**
   no — BTI prevents control transfer to a non-target instruction,
   but it does not prevent calling a function with the wrong WASM
   signature (which would crash later via argument-type mismatch).
   Both checks stay.
8. **kiln integration.** Per
   `docs/architecture/SYNTH_LOOM_RELATIONSHIP.md`, future kiln will
   host multiple WASM components on one MCU. Several checks
   change from defense-in-depth to **required** (linear-mem
   poisoning becomes a confidentiality control between components,
   CFI becomes load-bearing). The `--safety` flag should grow a
   `kiln` profile that's a superset of `asil-d`.

## 7. References

### WebAssembly + Component Model

* WebAssembly Core Specification 2.0,
  [https://www.w3.org/TR/wasm-core-2/](https://www.w3.org/TR/wasm-core-2/) —
  defines the trap semantics for `i32.div_s`, `i32.load`, etc.
* Component Model Canonical ABI,
  [github.com/WebAssembly/component-model](https://github.com/WebAssembly/component-model/blob/main/design/mvp/CanonicalABI.md) —
  defines lift/lower obligations.

### ARM architecture references

* *Armv7-M Architecture Reference Manual* (DDI 0403E.e), §B3.5 "Memory
  Protection Unit"; §B1.5.7 "UsageFault".
* *Armv8-M Architecture Reference Manual* (DDI 0553B.x), §D1.2.137
  "MSPLIM, Main Stack Pointer Limit"; §D1.2.179 "PSPLIM, Process Stack
  Pointer Limit".
* *Armv8.1-M Architecture Reference Manual Supplement — Pointer
  Authentication and Branch Target Identification* (DDI 0610A.b).
  Encodes `BTI`, `PAC`, `AUT`, the SAU interaction.
* *Cortex-M55 Technical Reference Manual* — silicon-vendor-specific
  details of the optional PAC implementation.
* *AAPCS32* (IHI 0042F) — the ABI synth follows for callee-saved
  registers and SP alignment.

### RISC-V references

* *RISC-V Instruction Set Manual, Privileged Architecture*, version
  20211203, Chapter 3.7 ("Physical Memory Protection").
* *RISC-V Zicfilp Extension* (Landing Pads), ratified 2024-06,
  [https://github.com/riscv/riscv-cfi](https://github.com/riscv/riscv-cfi).
* *RISC-V Zicfiss Extension* (Shadow Stack), same family, same repo.
* *RISC-V Zicond Extension* (Integer Conditional Operations), ratified
  2023, for branchless guard sequences.

### Prior art — compilers

* **CompCert** — *Formal verification of a realistic compiler* (Leroy,
  CACM 2009). Pattern for parameterising correctness theorems by
  optimisation level; synth's safety profile is analogous.
* **Cranelift / Wasmtime** — `enable_probestack` setting for stack
  overflow checks, `use_csdb` for Spectre v1, `bounds_check_strategy`
  for memory access checks. See
  [github.com/bytecodealliance/wasmtime/blob/main/cranelift/codegen/src/settings.rs](https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/codegen/src/settings.rs).
  Synth's `--safety` profile is the embedded-target equivalent.
* **V8 — TurboFan / TurboShaft** — runtime check elision for known-safe
  WASM accesses (e.g., post-loop-induction-variable analysis).
  Reference: V8 design doc on "WebAssembly memory bounds checks",
  [v8.dev/blog/wasm-memory-bounds-checks](https://v8.dev/blog/wasm-memory-bounds-checks).
* **Crocus** (VanHattum et al., ASPLOS 2024) —
  [DOI 10.1145/3617232.3624862](https://dl.acm.org/doi/abs/10.1145/3617232.3624862).
  Already cited in `docs/spectre-policy.md`; the F/D/A taxonomy
  applies directly to safety-check rationale.
* **Blade** (Vassena et al., POPL 2021) —
  [arXiv 2005.00294](https://arxiv.org/abs/2005.00294). The
  index-masking mitigation for §3.1 path C.

### Synth-internal references

* `docs/spectre-policy.md` — Spectre / transient-execution coverage;
  this document defers all speculative-execution concerns to that
  policy.
* `docs/design/MEMORY_ARCHITECTURE.md` — linear-memory layout that the
  bounds-check and poisoning sections build upon.
* `docs/design/PORTABLE_MEMORY_DESIGN.md` — abstraction layer over
  Zephyr / Linux / bare-metal memory; the safety checks must respect
  this abstraction (no hard-coded `0x2000_0000` SRAM base).
* `crates/synth-backend/src/mpu.rs` and `mpu_allocator.rs` — current
  MPU plumbing.
* `crates/synth-backend-riscv/src/pmp.rs` — current PMP plumbing.
* `crates/synth-synthesis/src/instruction_selector.rs` — current
  bounds-check and divide-trap lowerings.
* `coq/Synth/Compilation.v` — `compile_wasm_to_arm` function that will
  grow a `SafetyProfile` parameter in Phase 5.

## 8. Follow-up

A companion document, `docs/binary-safety-implementation.md`, will be
written once Phase 1 is in flight to track the per-PR changes.
