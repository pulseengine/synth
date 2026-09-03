# The embedder ABI for `--relocatable` on ARM Cortex-M (#1131)

This document states the complete register and layout contract between a synth
`--relocatable` (ET_REL, host-linked) ARM object and the embedder/harness that
links and runs it. Every fact below is **derived from the code that emits it**,
cited as `file:line` (line numbers as of the commit that landed this document;
the symbol names beside them survive drift). The load-bearing facts are
additionally pinned in `claims.yaml` (`SYNTH-EMBEDDER-ABI-RELOCATABLE-1131`),
so a change to the emitter that invalidates a sentence here turns the
`claim-check` CI job red instead of silently orphaning this page.

Scope: the `--relocatable` Cortex-M (Thumb-2) and Cortex-R5 (A32) path only.
`--relocatable` **forces the direct instruction selector**
(`select_with_stack`) for every function — the optimized path is never used on
host-linked objects, because it materializes an *absolute* linear-memory base
instead of using a register (`crates/synth-backend/src/arm_backend.rs:887-892`,
routing at `:991`; `CompileConfig::relocatable` doc,
`crates/synth-core/src/backend.rs:124-133`). Everything below describes what
that selector and the ARM encoders actually emit. `--native-pointer-abi`
changes the geometry (linmem base 0, statics via `__synth_wasm_data`) and is
out of scope here.

## The register contract

| Register | Meaning | Who sets the register | Who chooses the value | Category |
|---|---|---|---|---|
| **R11** (`fp`) | Linear-memory (memory 0) base address | Embedder, before any export runs | Embedder | (b) chosen |
| **R10** (`sl`) | Linear-memory (memory 0) size **in bytes** | Embedder, before any export runs | Embedder (constrained, see below) | (b) chosen |
| **R9** (`sb`) | Globals-table base address | Embedder, before any export runs | Embedder | (b) chosen |
| **R12** (`ip`) | Encoder scratch — clobbered freely by emitted code | synth | synth | (a) fixed |
| **SP** | AAPCS stack | Embedder (entry SP per AAPCS) | Embedder | (b) chosen |
| R0-R8, LR | AAPCS argument/result/scratch + callee-saved per AAPCS | — | — | (a) fixed (AAPCS) |

The *assignment* of R9/R10/R11 to these roles is **(a) FIXED by synth** — the
embedder cannot pick different registers. The *values* they hold are
**(b) CHOSEN by the embedder**; synth adapts because every access is
register-relative (that is the whole point of the relocatable path).

### Where each fact comes from

- **R9/R10/R11 are reserved — never allocated, never written.** The register
  allocator's universe is R0-R8 only
  (`ALLOCATABLE_REGS`,
  `crates/synth-synthesis/src/instruction_selector.rs:107-125`; the
  `index_to_reg` contract at `:127-147` states `result != R9/R10/R11`).
  Emitted function code *reads* them and never writes them; the prologue
  saves only `{R4-R8, LR}`
  (`crates/synth-synthesis/src/instruction_selector/select_with_stack.rs:174-185`).
  Encoder expansions may not borrow them as scratch either — that was the
  #1021 defect class, and `scripts/repro/expansion_canary_gate_1021.py`
  (CI-wired) executes every rule-emitted expansion under canaries and pins the
  unguarded-clobber set at EMPTY.
- **R11 is the linear-memory base.** Every memory-0 load/store is emitted
  R11-relative: `[R11, #imm]` when the effective offset folds
  (`select_with_stack.rs:2575`, `:2690`), `[R11, Rindex]` otherwise
  (`generate_load_with_bounds_check` /
  `generate_store_with_bounds_check`,
  `instruction_selector.rs:7108-7215` — `MemAddr::reg_imm(Reg::R11, ...)`).
  Wasm address `a` lives at machine address `R11 + a`. There is no other
  base: the object carries **no data relocations** for memory-0 accesses.
- **R10 is the memory-0 size in bytes.** Read by exactly three emission
  classes:
  1. `memory.size` — `LSR rd, R10, #16` (Thumb-2:
     `crates/synth-backend/src/arm_encoder.rs:3810-3831`; A32: `:1772-1778`),
     i.e. bytes → 64 KiB pages;
  2. the bulk-memory bounds guards (`memory.copy`/`memory.fill`,
     `select_with_stack.rs:7282-7295` — "addresses are R11-relative; R10 =
     size in bytes");
  3. every per-access guard under `--safety-bounds software|mask`
     (`software_bounds_guard`, `instruction_selector.rs:7040`;
     `mask_effective_address`, `:6931` — mask mode derives `size-1` from R10
     per access, #651).
  `memory.grow` **never writes R10**: it is emitted as a constant `-1`
  (`MVN rd, #0`, `arm_encoder.rs:3834-3846` Thumb-2, `:1780-1785` A32) —
  memory cannot grow, so R10 is constant for the life of the process.
- **R9 is the globals-table base.** `global.get`/`global.set` are emitted as
  `LDR/STR [R9, #slot_offset]`
  (`select_with_stack.rs:5637-5666` get, `:5722-5822` set; i64 globals are a
  register PAIR at `[R9, off]` / `[R9, off+4]`, `:5533`).
- **R12 is clobbered.** It is the encoder's sanctioned scratch
  (`instruction_selector.rs:109-114`): indexed accesses lower to
  `ADD ip, addr, #off; LDR/STR rd, [R11, ip]`, and constant/VFP helpers use
  it too. The embedder must treat it as dead across any call into the object
  (ordinary AAPCS caller-saved discipline already implies this).

## Timing and preservation

**All three of R9, R10, R11 must hold their contract values before the first
export is entered, and the embedder may set them once.** Reasons, both
checkable:

1. Emitted code never writes any of them (allocator universe above; verified
   by the expansion canary gate, and empirically by disassembling emitted
   objects — the audit in `scripts/embedder_abi_audit_1131.py` decodes
   every function and asserts zero writes to R9/R10/R11).
2. Anything the object calls *out* to must preserve them because they are
   AAPCS callee-saved registers (v6+ of the AAPCS makes R9 platform-reserved,
   which is exactly how synth uses it): stock `arm-none-eabi` libgcc AEABI
   helpers (`__aeabi_f2lz` etc.) comply, and any function the embedder links
   in must comply too. An embedder callback that clobbers R9/R10/R11 without
   restoring them breaks the contract — that is the one way "set once" can
   fail, and it is the caller's bug, not a per-call re-establishment
   obligation.

Per-call re-establishment is therefore unnecessary but harmless.

## Region requirements

- **Linear memory (at R11):** the embedder must reserve at least the module's
  declared initial memory, `initial_pages x 65536` bytes, and R10 must state
  the reserved size in bytes. R10 should be a whole multiple of 65536 — the
  `memory.size` lowering truncates (`LSR #16`), so a non-multiple
  under-reports and, worse, the software/mask guards would permit accesses
  into the fractional tail that `memory.size`-based module logic believes
  does not exist. With the default `--safety-bounds none`, nothing checks
  accesses against R10 at all (the CLAUDE.md compliance envelope; pinned by
  `SYNTH-SAFETY-BOUNDS-DEFAULT-ENVELOPE`) — an OOB access reads/writes
  whatever sits at `R11 + addr`.
- **Globals table (at R9):** size is the sum of the module's global slot
  widths — 4 bytes for i32/f32, 8 for i64/f64, 16 for v128, laid out densely
  in declaration order (`global_slot_width` / `global_slot_offset`,
  `instruction_selector.rs:6752-6777`, #643). Slot offsets are compile-time
  constants; an i64 slot is two word accesses at `off`/`off+4`.
- **Alignment:** 4-byte-align both R9 and R11. The globals lowering emits
  word `LDR/STR` at `R9 + 4k` and its stated requirement is word alignment
  (`instruction_selector.rs:6770`: "word alignment is all the paired
  `LDR`/`STR` lowering requires"). For R11, a 4-aligned base keeps every
  naturally-aligned wasm access naturally aligned on the bus; synth never
  checks the base, so a misaligned base "works" only on cores configured to
  tolerate unaligned word access (UNALIGN_TRP clear) — do not rely on that.
- **Disjointness is the embedder's job.** The linmem region, the globals
  table, and the stack must not overlap. synth validates this **only on the
  self-contained image path** (`validate_linmem_globals_disjoint`,
  `crates/synth-core/src/static_data_addr.rs:465`, called from the Cortex-M
  image builder); on `--relocatable` nothing checks your layout.
- **Stack:** plain AAPCS — the embedder owns placement and size;
  `--stack-layout` is refused with `--relocatable` precisely because "the
  linker/harness owns the layout" (`resolve_stack_layout`,
  `crates/synth-cli/src/main.rs:1554-1576`). Functions need their frames
  (locals + spill area + outgoing args) on SP; there is no shadow-stack or
  split-stack machinery on this path.

## Initialization obligations (the two `--embedder-*` promises)

Emitted code assumes, before any export runs:

- **Active data segments applied**: each segment's bytes at `R11 + offset`
  (declared by `--embedder-data-init`; without the flag a data-carrying
  module refuses, `crates/synth-cli/src/main.rs:344-358`).
- **Globals seeded**: each global's evaluated initializer at
  `R9 + slot_offset` (declared by `--embedder-global-init`; without the flag
  a module with nonzero/non-const initializers refuses, `main.rs:361-376`).
  All-zero initializers need no seeding beyond a zeroed table.

Both flags are byte-invisible in the object — they convert a refusal into an
acknowledged contract; nothing in the artifact can verify the embedder kept
the promise. The observed failure mode for a broken promise is zeros (or
whatever the region holds), not a trap.

## `call_indirect`, extra memories, symbols

- **`call_indirect` (modules that use it):** the host-linked path dispatches
  through the #650 R11 multi-table layout: the embedder links ALL funcref
  tables as one contiguous region of raw 4-byte code pointers **at
  `R11 + 0`** (table N at `R11 + sum(size(0..N)) * 4`), uninitialized slots
  as ZERO words, and — for heterogeneous tables — copies the object's
  `.synth.table_type_ids` section verbatim to `R11 + type_ids_byte_offset`.
  The full normative statement lives on
  [`CallIndirectGuards`](../crates/synth-core/src/wasm_decoder.rs)
  (`crates/synth-core/src/wasm_decoder.rs:164-230`). Note the consequence:
  the pointer region occupies the LOW BYTES of linear memory, so wasm
  addresses `[0, tables*4)` alias it — a module that both stores to low
  linear-memory addresses and uses `call_indirect` will corrupt its own
  dispatch table, and synth does not detect that on this path. (The
  self-contained path DECLINES this very collision, #717; the host-linked
  path inherits it as the embedder's layout responsibility.)
- **Extra linear memories (k > 0):** addressed via their own
  `__synth_wasm_data_<k>` region symbol, which the linker/embedder places —
  R10/R11 are memory-0-only (`main.rs:3617-3627`, VCR-MEM-002 #406).
- **Symbols:** every function is exported twice at the same address
  (`func_N` and, for exports, the wasm export name); imported functions
  become direct `func_N` BLs rewritten to the wasm field name, resolved by
  the linker (`arm_backend.rs:517-520`, #197). Internal calls also carry
  `R_ARM_THM_CALL` relocations — an object whose every relocation is
  `R_ARM_THM_CALL` is the expected shape. Read the symbol table by section
  TYPE (`SHT_SYMTAB`), not name: the ARM builder emits its symtab with an
  empty section name.

## What is INCIDENTAL — observed in some outputs, guaranteed by nothing

Category (c). Do not build a harness on any of these:

- **The concrete values `R11 = 0x2000_0000`, `R10 = 0x1_0000`,
  `R9 = 0x2001_0100`** seen in the SELF-CONTAINED reset handler. They are
  that image's layout choice (`build_multi_func_cortex_m_elf`,
  `crates/synth-cli/src/main.rs:6680-6733`), not the relocatable contract.
- **Globals adjacent to the end of linear memory** (`R9 = R11 + linmem +
  0x100`). Self-contained placement policy. On `--relocatable`, R9 and R11
  are read independently; no emitted instruction derives one from the other.
  Put the table anywhere disjoint.
- **Reading the contract off the self-contained reset handler at all.** It
  happens to agree with the relocatable contract for R9/R10/R11 today, but
  that image also contains the optimized selector's functions, whose
  linear-memory base is an absolute constant
  (`OPTIMIZED_LINMEM_BASE = 0x2000_0100`,
  `crates/synth-core/src/backend.rs:83`) — `0x100` ABOVE that handler's R11,
  a documented pre-existing quirk (`main.rs:6721-6727`). The handler is not
  a statement of any single path's ABI. This document is the contract; the
  disassembly was a corroboration.
- **R10 being ignorable.** A module with no `memory.size`, no bulk-memory
  ops, and default `--safety-bounds none` never reads R10 — an unset R10
  "works" for exactly as long as the module keeps that shape. Set it
  regardless; which emissions read it is an implementation detail.

## Compliance note

With the default `--safety-bounds none` there is no OOB trap on this path —
see the "Compliance envelope" section of `CLAUDE.md`. `--safety-bounds
software|mask` make the guards above real and make R10 load-bearing on every
access.
