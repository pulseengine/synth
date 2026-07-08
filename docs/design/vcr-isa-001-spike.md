# VCR-ISA-001 Feasibility Spike — Sail/ASL-derived ARM semantics (2026-07-08)

**Verdict: GO — but on the transcribe-and-bridge path, not the import path.**
Importing the Sail-generated Rocq model wholesale is a no-go at synth's scale
(measured below). Hand-transcribing the Sail execute semantics per instruction
with line-level provenance, then proving a bridge lemma against
`ArmSemantics.v`, works end-to-end today: this spike shipped
`coq/Synth/ARM/SailArmBridge.v` with **23 Qed (3 bridge theorems + 6 per-flag
lemmas + helpers) / 0 Admitted**
covering the AArch32 ADD (register) family — ADD, ADDS (all four NZCV flags),
and CMP — compiled by the existing hermetic Rocq 9 Bazel toolchain and wired
into `//coq:verify_proofs` (green).

Epic: #242. Roadmap artifact: `artifacts/verified-codegen-roadmap.yaml`
(VCR-ISA-001, stays `proposed`; this document is the spike evidence the
2026-06-10 deep-research gate demanded).

## 1. Survey: what exists for Sail→Rocq today

Verified directly against the repositories on 2026-07-08 (not from memory):

| Artifact | State | Evidence |
|---|---|---|
| Sail tool Rocq backend | **Alive.** Sail 0.20.0 ships `--coq` (`--coq-lib-style {bbv\|stdpp}`), plus a newer `--lean` target. Installable in seconds via `nix-shell -p ocamlPackages.sail` (cached). | ran `sail --help` locally |
| Rocq support library | `rems-project/coq-sail` maintained (bbv and stdpp flavours; opam `coq-sail` / `coq-sail-stdpp`). | repo README |
| **sail-arm arm-v9.4-a** | Full AArch32+AArch64 model derived from Arm's 2023-03 ASL by `asl_to_sail`. `src/instrs32.sail` (1.9 MB) contains every T32/A32 instruction incl. all four ADD (register) encodings. `gen_coq` Makefile target exists. | repo listing; quoted sources below |
| arm-v9.4-a **Coq snapshot** | `snapshots/coq/armv9.v` is a **single 42 MB .v file** (+1 MB types), requiring stdpp-**unstable** (not in opam, MPI-SWS GitLab pin) and `coq-sail-stdpp` pinned from git. | `snapshots/coq/README` |
| arm-v8.5-a Coq snapshot (2019) | 11.8 MB `aarch64.v`, "requires ~**40 GB** memory to build", checked against **Coq 8.9.1** + bbv 1.1, generated from a `coq-experimental` branch with manual fixes. AArch64 only. | `arm-v8.5-a/snapshots/coq/README.md` |
| sail-riscv | Coq export documented (`riscv_coq_build`, `generated_definitions/coq/RV64/riscv.v`); the RISC-V side of VCR-ISA-001 remains the easier half, but note upstream builds RV64-first and the concurrency-interface/stdpp churn applies there too. | riscv/sail-riscv docs |

Conclusion of the survey: **the tool is healthy; the generated-ARM-model
artifact is the blocker.** A 42 MB monolithic `.v` pinned to unreleased
library versions cannot join synth's hermetic Rocq 9 / `Stdlib`-prefix Bazel
build, and its historical build cost (40 GB-class) is far outside CI. Nobody
proves against the full generated ARM model directly — even REMS' own Islaris
works from per-instruction Isla traces instead, for exactly this reason.

## 2. What the spike built (the crown)

`coq/Synth/ARM/SailArmBridge.v` — provenance-annotated transcription + bridge:

- **Transcribed from Sail** (rems-project/sail-arm @ `1bf2e5574ba9`,
  2026-06-19, arm-v9.4-a, quoted verbatim in comments):
  - `AddWithCarry` (`v8_base.sail:13337`) → `sail_add_with_carry`
    (result + n/z/c/v exactly as ASL computes them: `result<31>`,
    `IsZero`, `UInt(result) != unsigned_sum`, `SInt(result) != signed_sum`);
  - `execute_aarch32_instrs_ADD_r_Op_A_txt` (`instrs32.sail:457`) and the
    CMP clause (`AddWithCarry(R[n], NOT(shifted), '1')`), at `shift_n = 0`;
  - `NOT` → `sail_not` (same `Z.lnot`+`repr` rendering as our MVN).
- **Bridge theorems (all Qed):**
  - `sail_bridge_add_reg` — `exec_instr (ADD rd rn (Reg rm))` produces
    exactly `R[d] := fst (AddWithCarry (R[n], R[m], '0'))`;
  - `sail_bridge_adds_reg` — ADDS agrees on the register **and all four
    NZCV flags** with the ASL nzcv output;
  - `sail_bridge_cmp_reg` — CMP's flags equal ASL's
    `AddWithCarry(R[n], NOT(R[m]), '1')` nzcv.
  - Per-flag lemmas prove the six hand-written flag definitions
    (`compute_{n,z}_flag`, `compute_{c,v}_flag_{add,sub}`) equal ASL's
    formulations — these are the definitions every CMP-based comparison
    lowering (Compilation.v, VcrSelRules.v's 10 comparison rules) rests on.
    The two formulations are genuinely different (e.g. ASL's V is
    "`SInt(result) != SInt(x)+SInt(y)`", ours is the sign-pattern test), so
    the lemmas are non-vacuous: a modeling bug in either side would fail them.

Documented abstraction gaps (in the file header): `shift_n = 0` (synth emits
plain register forms), `d != 15` (no PC in our executor — the known
VCR-ISA-001 executor gap), `ConditionPassed() = true` (no IT blocks),
`bits(32)` rendered as `I32.int` (Z mod 2^32). The residual trust moves from
"the whole hand-written model is right" to "this 20-line quoted transcription
is faithful" — reviewable token-by-token against the Sail source.

## 3. Measured cost per instruction

Actual spike effort for the ADD family, as data for the migration estimate:

| Piece | Cost |
|---|---|
| Locate + quote Sail source (execute clause, decode, helpers) | ~15 min/instruction family (the model is greppable; helpers like `AddWithCarry`/`Shift_C` amortize across the whole ALU class) |
| Transcription (`sail_add_with_carry`, `sail_not`, slice defs) | ~40 lines Rocq |
| Bridge proofs | ~230 lines Rocq incl. reusable helpers (`sum/diff_mod_cases`, `testbit31_ge`, `unsigned/signed_not`, `destruct_ifs`/`bool_blast` tactics). Two build iterations to green. |
| Reusable residue for the next instructions | the helpers + tactics: SUB/SUBS/RSB/CMN are the same `AddWithCarry` shape (near-zero new machinery); AND/ORR/EOR/MVN/MOV/shifts are flag-free or simpler |

Extrapolation for the integer core ArmSemantics.v actually models (~25
distinct straight-line op shapes after the AddWithCarry family is done):
roughly **0.5–1 day of proof work per remaining instruction class**, most far
cheaper than ADD because the flag machinery (the hard 60%) is now proven once.
The genuinely new costs are: register-shift semantics (`Shift_C` with
amount != 0), `MUL/UMULL` (no flags in our model — easy), `CLZ/RBIT` (our
side is axiomatized via `I32.clz`/`I32.rbit`, so the bridge would first need
those axioms replaced by definitions), and loads/stores (our memory model is
`Z -> I32.int` vs Sail's byte-addressed memory + translation — the widest gap,
needs a deliberate abstraction statement, not a mechanical bridge).

## 4. Risks

1. **Transcription fidelity is hand-checked, not machine-checked.** Mitigation
   used here: verbatim Sail quotes with file:line + commit hash next to every
   definition; a reviewer diffs the two syntaxes side by side. Optional
   hardening later: differential-test the transcription against a Sail-built
   C emulator or unicorn on random operands (fits the existing VCR-ORACLE
   harness pattern).
2. **The PC-gap is NOT closed by this path alone.** The trap-guard admits
   (i32 div/rem) need a PC-indexed executor in *our* model; the Sail model has
   one natively, but bridging control flow means first giving `exec_program` a
   PC (a prerequisite refactor tracked in the VCR-ISA-001 yaml). The bridge
   pattern extends once that lands (Sail's `_PC` projection ↔ our index).
3. **Sail model version drift.** Pinned by commit hash in the provenance
   comments; bumping is a re-diff, not a re-proof, unless Arm's ASL for the
   instruction changed (which is itself signal).
4. **Generated-import remains attractive for RISC-V.** sail-riscv's Coq
   export is institutionally maintained; if upstream lands a current
   Rocq-9-compatible export, the import path can be re-evaluated for the
   RV32 side independently — the ARM conclusion does not transfer 1:1.

## 5. Recommendation

- **GO** on VCR-ISA-001 via **per-instruction transcribe-and-bridge**,
  prioritized: (1) the remaining AddWithCarry family (SUB/SUBS/CMN/RSB —
  cheap now), (2) the flag-free ALU/shift class, (3) the PC-executor refactor
  (unblocks div/rem admits, the item's original motivation), (4) memory ops
  last (needs the memory-model abstraction statement).
- **NO-GO** on importing `gen_coq` output of sail-arm into the build (42 MB
  monolith, unreleased dep pins, 40 GB-class build memory, Rocq-version lag).
- The spike satisfies the deep-research gate of 2026-06-10 ("bounded
  feasibility spike must precede any release commitment"): substrate
  freshness is now VERIFIED for the tool (Sail 0.20 via nixpkgs, `--coq`
  alive) and REFUTED for the generated-ARM-artifact path, with the working
  alternative landed in-tree.

## Artifacts

- `coq/Synth/ARM/SailArmBridge.v` — 23 Qed / 0 Admitted, in
  `//coq:verify_proofs` (green).
- `coq/BUILD.bazel` `:sail_arm_bridge`, `coq/_CoqProject` entry.
- This report.
