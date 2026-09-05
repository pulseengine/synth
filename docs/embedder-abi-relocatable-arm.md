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
  R10/R11 are memory-0-only (`main.rs:3617-3627`, VCR-MEM-002 #406). A
  multi-memory object additionally carries the #1145 region table; the full
  contract — including the MPU obligation it exists for — is the
  "Multi-memory region table" section below.
- **Symbols:** every function is exported twice at the same address
  (`func_N` and, for exports, the wasm export name); imported functions
  become direct `func_N` BLs rewritten to the wasm field name, resolved by
  the linker (`arm_backend.rs:517-520`, #197). Internal calls also carry
  `R_ARM_THM_CALL` relocations — an object whose every relocation is
  `R_ARM_THM_CALL` is the expected shape. Read the symbol table by section
  TYPE (`SHT_SYMTAB`), not name: the ARM builder emits its symtab with an
  empty section name.

### The `@`-in-export-names hazard — UNSOLVED, work around it

Component-model export names keep the WIT name verbatim, including `:` `@`
`#` — and in GNU ARM assembly `@` begins a comment, so a C-side `__asm__`
rename label on such a name truncates SILENTLY mid-symbol; the assembler's
"garbage following instruction" does not point at the cause. **Do not use
the `@`-bearing name as an asm label.**

Two things that look like remedies and are not (both measured, #1132):

- **The `func_N` alias does NOT solve this across translation units.** It
  exists at the same address but is emitted `STB_LOCAL` — `nm --extern-only`
  lists only the `@`-bearing name, so an external `bl func_N` cannot resolve
  to it. That binding is DELIBERATE, not an oversight: `func_N` is named by
  per-object wasm function INDEX, and emitting it GLOBAL made co-linking two
  independently-dissolved synth objects fail with `multiple definition of
  'func_N'` — a real consumer-filed collision (#656). Re-globalizing the
  alias would trade this papercut for that one.
- **`-ffixed-*`-style flag discipline doesn't apply here either** — there is
  no flag; the truncation happens inside the assembler.

The load-bearing workaround is the consumer's own:
`objcopy --redefine-sym 'pulseengine:ns/iface@0.7.0#tick=your_c_name'` —
and ASSERT the rename landed (`nm | grep " T your_c_name$"`) rather than
trusting it; a silent no-op surfaces three steps later as an unresolved
reference.

## The multi-memory region table (#1145, RQ-62-MEMISOLATE)

A `--relocatable` object compiled from a module with **more than one** linear
memory carries a per-memory region table — the link-time input from which the
embedder programs one MPU (or PMP) region per memory. Emission:
`build_relocatable_elf`, `crates/synth-cli/src/main.rs` (the
`RQ-62-MEMISOLATE` block after the `__synth_wasm_data_<k>` symbols).
Single-memory objects carry **none** of these symbols (byte-identical to
pre-#1145 output; pinned by `region_table_absent_on_single_memory_1145`).

### What the table is (category (a) — FIXED by synth)

| Symbol | Encoding | Meaning |
|---|---|---|
| `__synth_mem_count` | `SHN_ABS`, `st_value` = N | Total memory count, memory 0 included. |
| `__synth_mem_size_0` | `SHN_ABS`, `st_value` = bytes | Memory 0's declared initial size (`initial_pages x 65536`). |
| `__synth_mem_size_k` (k ≥ 1) | `SHN_ABS`, `st_value` = bytes | Memory k's declared initial size. |
| `__synth_mem_base_k` (k ≥ 1) | offset 0 of `.synth.wasm_mem_k`, `st_size` = region bytes | Its **linked address** is memory k's region base, wherever your linker script places the section. |

`SHN_ABS` symbols are link-invariant values, not placed addresses — read one
from C as `(uint32_t)(uintptr_t)&__synth_mem_size_1`.

The sizes are **exact for the life of the process**: `memory.grow` on this
backend always returns `-1` (every memory is fixed), and memory k's
`memory.size` is lowered as the same constant — a region programmed from this
table can never need to move or grow.

**There is deliberately NO `__synth_mem_base_0`.** Memory 0's base is the R11
*value* the embedder itself chooses at runtime (the register contract above);
a link-time symbol for it would be a second copy of that truth which nothing
forces to agree with the register. Derive region 0 from the same address you
load into R11 — one source, no drift.

### What the embedder must arrange (category (b) — CHOSEN, constrained)

1. **Placement is yours, MPU legality is yours.** synth emits
   `.synth.wasm_mem_k` with `sh_addralign = 4` — it does NOT pre-align the
   section for your MPU, because it cannot know which MPU you have:
   - **PMSAv7 (Cortex-M3/M4/M7):** a region's size must be a power of two
     (≥ 32 B) and its base aligned to that size. A 1-page memory (64 KiB) is
     a power of two — place the section 64 KiB-aligned. A non-power-of-two
     size (e.g. 3 pages = 192 KiB) needs the next power of two (256 KiB
     region, base 256 KiB-aligned) with 8-slice SRD subregion disables — or a
     split across regions. Your linker script owns this; synth only
     guarantees the size symbol is exact.
   - **PMSAv8 (Cortex-M23/M33/M55/M85):** base and limit on a 32-byte
     granule; any 32 B-aligned placement of any of these sizes is legal.
2. **Region 0 covers what R10 states.** If you reserve more than
   `__synth_mem_size_0` for memory 0 (R10 larger, allowed), your MPU region
   must cover the RESERVED extent — the guards and `memory.size` believe R10.
3. **Disjointness, again yours.** `[R11, R11 + R10)` and every
   `[&__synth_mem_base_k, +__synth_mem_size_k)` must be pairwise disjoint
   (and disjoint from the globals table and stack). Nothing on this path
   checks your layout.
4. **Initialization.** A memory k with active data segments ships
   `.synth.wasm_mem_k` as PROGBITS (segment bytes at their offsets, rest
   zero) — your normal `.data` LMA→VMA startup copy must cover it before any
   export runs. A pure zero-init memory ships NOBITS — zero it like `.bss`.
   Memory 0's segments remain the `--embedder-data-init` promise.
5. **Programming the MPU is yours, and it is a memory-safety control.** synth
   emits NO MPU programming on this path; until the #1145 two-tenant fault
   criterion has executed on an MPU-bearing venue, `--safety-bounds mpu` on a
   multi-memory module REFUSES rather than bless the arrangement — the
   symbols above are the input to YOUR startup, not a claim by synth that
   isolation exists.

### The compliance fact this table does not fix

**Memory k > 0 has no bounds-check story on any profile** (#1145, the finding
that outranks the MPU headline): `--safety-bounds software|mask` loud-skip
every memory-k access — the software guard compares against R10 and mask mode
derives `size-1` from R10, both **memory 0's size** by the register contract;
memory k has no size register, so a guard would check the wrong memory's
bound — and the module then fails via #952 rather than shipping a partial
object. A module touching memory k either compiles with NO inline bounds
checking at all or does not compile. Embedder-programmed MPU regions from
this table are currently the ONLY enforcement available for it. Pinned
executable: `scripts/repro/mem_isolation_red_1145.py` (the decline needles +
the landed cross-tenant write).

### Conformance properties `verify-embedder` COULD check (named, not built)

Stated so the obligation does not go ungated by omission (the #1131
lucky-conformance class). On the **final linked image**, statically checkable
from the symbol table alone:

- every `__synth_mem_base_k`'s linked address is size-aligned for a PMSAv7
  region covering `__synth_mem_size_k` (or 32 B-aligned under a declared
  PMSAv8 target), and
- the `[base_k, base_k + size_k)` regions are pairwise disjoint.

NOT statically checkable, same class as the R11-value question the
register-contract check already names as unseeable: whether the boot code's
`MPU_RBAR/RASR` writes actually program regions matching this table, and
whether region 0 matches the R11/R10 values boot establishes. Those are
execution properties — the two-tenant fault criterion on Renode-M4/silicon is
their gate, not a disassembly scan.

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

- **A WORKING RESULT DOES NOT VERIFY THE METHOD THAT PRODUCED IT.** Requested
  by jess after conforming to this contract correctly *by luck, twice*
  (#1131): they read R11 out of the self-contained reset handler — a 1-in-2
  guess between two linear-memory bases in that binary, which they won — and
  their harness then matched a SIL reference bit-exact, which felt like
  confirmation and was not. A correct output means the inferred contract was
  not *detectably* wrong on that input; it says nothing about the contract.
  Everything in this section is the set of things a passing harness can be
  built on top of and still be wrong about.

## Checking YOUR side: `synth verify-embedder` (#1132)

Everything above states obligations; this section is the mechanical check on
the embedder's half of the register contract. #1131's consumer conformed to
it **correctly by luck**: their C shim happened to compile to a bare
tail-branch, so GCC never allocated R11 between boot establishing the
registers and synth's code reading them — one more local variable and the
linear-memory base silently becomes a scratch register, and the symptom is a
wrong value on a control loop, not a build error.

```
synth verify-embedder <elf> [--allow-writer <symbol>]...
```

REFUSES (exit nonzero, each site named) when any instruction in the given
ELF **writes R9, R10 or R11** — in any form: destination operands,
`pop`/`ldm` register lists, addressing-mode writeback, long-multiply second
destinations, `mrc`/`mrrc`/`vmov`-to-core forms. It disassembles with your
own toolchain's `objdump` (`arm-none-eabi-objdump`, `llvm-objdump`, or
`SYNTH_OBJDUMP=<path>`), and classification is FAIL-CLOSED: an unknown
mnemonic or undecodable bytes near a reserved register refuse rather than
pass. A scan that decodes zero instructions also refuses — conformance about
nothing is not conformance.

Run it over the **final linked image**. Your boot code legitimately writes
the three registers once — name that symbol with `--allow-writer` (an
acknowledgement in the `--embedder-data-init` mold: it changes no behaviour,
it records that a human accepted the obligation for exactly that symbol; a
misspelled name refuses instead of silently waiving nothing). Pair it with
`-ffixed-r9 -ffixed-r10 -ffixed-r11` on your C objects; the check is what
notices when the flag silently stops applying.

The check is deliberately STRICTER than the dynamic contract: a function
that saves, repurposes and restores R11 around a region is AAPCS-legal *if
nothing in that region enters synth code*, but that is not statically
evident, so any write refuses (or gets a deliberate `--allow-writer`).

**What it cannot see** (bounds, stated like every check in this repo):

- Code NOT in the ELF you hand it — a bootloader, ROM routines, a debugger,
  code injected at a later link stage. Check the final image.
- Runtime register-context switches: an RTOS restoring a task context
  rewrites R9-R11 from memory. The `ldm`/`pop` doing it IS flagged, but
  whether the restored VALUES honour the contract is a runtime property.
- Runtime-generated or self-modifying code, and handlers installed at
  runtime whose code lives outside the scanned sections.
- It trusts objdump's mapping-symbol (`$t`/`$d`) code/data separation.
  Toolchain objects carry mapping symbols; on a STRIPPED object a literal
  pool can desynchronise the decode — the failure direction there is a false
  refusal or an undecodable-bytes refusal, not a silent pass.
- Indirect STORES cannot modify a register, so "indirect writes" are not a
  gap for the registers themselves — the indirect hazard is the
  context-restore class above.

It DOES see inline asm and hand-written `.s` — those are emitted code, which
is the point of checking bytes instead of build flags. The check's own
discrimination is CI-pinned: `scripts/repro/verify_embedder_gate_1132.py`
refuses a real 4-shape clobbering object (naming all three registers) and
accepts conforming, acknowledged, and synth-emitted images on every run.

## Compliance note

With the default `--safety-bounds none` there is no OOB trap on this path —
see the "Compliance envelope" section of `CLAUDE.md`. `--safety-bounds
software|mask` make the guards above real and make R10 load-bearing on every
access.
