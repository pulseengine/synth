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
changes the geometry (linmem base 0, statics via `__synth_wasm_data`); its
geometry is otherwise out of scope here, but the rules that decide which
memory-0 values are wasm statics are an embedder contract and are stated in
[`--native-pointer-abi`: memory-0 address provenance](#--native-pointer-abi-memory-0-address-provenance-rq-91-npamodel-v091).

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
  1. `memory.size` — a right shift by **log2 of the memory's DECLARED page
     size** (Thumb-2: `crates/synth-backend/src/arm_encoder.rs:3849-3894`;
     A32: `:1756-1782`), i.e. bytes → declared pages. For the default 64 KiB
     page that is `LSR rd, R10, #16`, byte-identical to every release before
     v0.83. For `(pagesize 1)` (#1441, honoured on `--relocatable` only) the
     byte count IS the page count, so it emits `MOV rd, R10` — a shift of zero
     is NOT an LSR in either encoding (A32 `shift5=0, type=01` means shift BY
     32), and the encoder refuses any shift it cannot encode rather than
     emitting a wrong word;
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
  declared initial memory, `initial_pages x page_bytes` where `page_bytes` is
  the memory's DECLARED page size (65536 unless the module says
  `(pagesize 1)`, #1441), and R10 must state the reserved size in bytes. R10
  should be a whole multiple of that page size — the `memory.size` lowering
  truncates toward it, so a non-multiple
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
  The order is the FULL wasm global index space: imported globals take the
  leading slots (with their own widths), then the defined globals. synth
  binds no imported global's value, so a function that reads or writes one
  is refused (`IMPORTED-GLOBAL`, RQ-91-IMPGLOBAL, #1676); an unreferenced
  import only positions the defined globals after it.
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

  **synth will tell you the size — ask for it with `--emit-stack-depth`**
  (#1341). You still own placement, but you no longer have to guess the
  number:

  ```
  $ synth compile module.wasm --target cortex-m7 --relocatable --all-exports \
      --emit-stack-depth -o module.o
    Stack: wrote module.o.stack.json (4 bounded, 0 declined, deepest 120 B) — synth-stack-v1
  ```

  The `synth-stack-v1` sidecar lands at `<output>.stack.json`, beside the
  object, the same way `--emit-wcet`'s does. Read the entry whose `name`
  matches the export you call:

  ```json
  { "schema": "synth-stack-v1", "module": "module.wasm",
    "exports": [ { "name": "controller#step", "status": "bounded", "bytes": 120 },
                 { "name": "func_0",          "status": "bounded", "bytes": 8 } ] }
  ```

  Two notes on reading it. The array is named `exports` but carries **every**
  compiled function, exported or not — match on `name`, do not assume the
  export is first. And an export name containing `#` or `@` is carried
  through **verbatim**, in the sidecar and in the ELF symbol table alike, so
  `controller#step` is the key you look up (this is *not* affected by the
  `@`-in-export-names hazard described below, which is about linking, not
  about this file).

  **What the number is.** A MAX over the direct call tree, derived by walking
  the **emitted instruction stream** and tracking the running SP delta at every
  instruction boundary (`crates/synth-backend/src/stack_depth.rs`). It counts
  the callee-saved `push`, any `vpush` of the VFP half, the `sub sp` frame, and
  transient `PUSH`/`POP` inside encoder expansions. It is a maximum, not a sum:
  a callee invoked a thousand times in a loop costs its frame **once**, because
  frames are popped between calls.

  **Do not compute this yourself from the object.** Summing every
  `sub sp, #N` — the obvious reading — is wrong in the dangerous direction:
  it misses the callee-saved push entirely, and misses every function whose
  frame size is 0, which emits no `sub sp` at all while still consuming 8 or
  24 bytes. On the shipped fixture `scripts/repro/stack_depth_branch_1341.wat`
  that method yields 96 B against a true **120 B** — a 20 % UNDER-report. (The
  immediate is also printed in hex, so a `#[0-9]+` regex silently reads `#0x20`
  as 0.)

  **An absent number is information, not a gap.** When synth cannot prove a
  bound it says so per export and never emits a lower bound, because a silent
  lower bound would reproduce exactly the corruption this flag exists to
  prevent:

  ```json
  { "name": "top", "status": "declined", "reason": "call_indirect" }
  ```

  The reasons are `recursion` (a cycle in the direct call graph), `call_indirect`
  (the callee set is not statically known), `external-call` (a direct call to an
  import, whose frame is code synth did not emit), `callee-unbounded` (a decline
  propagates up), and `unknown-sp-move` (an SP movement the walker cannot price).
  A `declined` export means **you** must bound that call tree; it does not mean
  the module is unsafe.

  **WHAT YOU MUST STILL ADD ON TOP — synth cannot see it.** This number covers
  the frames synth itself emits. It does **not** include the exception frame
  your core pushes on entry to an interrupt, anything your ISRs then use, or
  nesting between them. The stack-depth pass has no model of interrupts at
  all; it walks the instruction stream and nothing else.

  Splitting MSP/PSP does **not** remove this from your budget, which is the
  part that is easy to get backwards: on Cortex-M the exception **stacking**
  uses whichever stack pointer was active, so if synth's export is running on
  a task stack (PSP) the hardware frame — 8 words, or 26 with FP context
  stacking enabled — lands on **that** stack. Only the handler body then runs
  on MSP. So a task stack must budget synth's number plus at least one
  exception frame, plus a tail-chained or late-arriving one if your priority
  configuration allows it. So:

  > **region size ≥ synth's number + your worst-case interrupt/nesting
  > allowance**, not synth's number.

  Sizing the region to the reported bytes exactly re-creates the original
  #1341 failure — a correct result followed by a corrupted neighbour — with
  the extra hazard that the number now looks authoritative. If your export
  runs on a task stack, size the **task**, and remember that a bound is a
  worst case over the call tree, not an observation like DWT or stack
  colouring.

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
| `__synth_mem_size_0` | `SHN_ABS`, `st_value` = bytes | Memory 0's declared initial size (`initial_pages x` its DECLARED page size — 65536 unless the module says `(pagesize 1)`, #1441). |
| `__synth_mem_size_k` (k ≥ 1) | `SHN_ABS`, `st_value` = bytes | Memory k's declared initial size, on the same rule. |
| `__synth_mem_region_k` (all k) | `SHN_ABS`, `st_value` = bytes | **The MPU-legal extent covering that memory** (#1441): the smallest power of two ≥ 32 that is ≥ `__synth_mem_size_k`. PROGRAM YOUR REGION FROM THIS, not from the size. Two symbols because one number cannot be true about both the declaration and the region: reporting only the rounded extent re-creates #1315's over-grant in miniature, and reporting only the declaration moves an unstated rounding obligation onto you — the class #1145 exists to prevent. Under the default page size the two already differ for any page count that is not itself a power of two, so this is emitted unconditionally rather than only under a custom page size. |
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

1. **Placement is yours, MPU legality is yours.** Since v0.68 synth emits
   `.synth.wasm_mem_k` with `sh_addralign` = its **MPU region size** — the
   smallest power of two covering the memory's declared size, never below the
   PMSAv7 minimum of 32 B (RQ-68-MPUHONEST, #1145) — so a linker honouring
   section alignment places it at a PMSAv7-legal base. (ARMv6-M's 256 B minimum
   region is not applied yet; it lands with ARMv6-M support, #1301.) **Why it
   matters, from gale's two-tenant run:** a misaligned base does not fail as
   "misaligned" — a verified MPU switch that refuses a table whose base is not
   size-aligned reads exactly like *this platform has no MPU*. Before v0.68 the
   fix was placing the section by hand, e.g.
   `--section-start=.synth.wasm_mem_1=0x20030000`; a linker script that places
   sections at explicit addresses still owns legality. **Alignment makes every
   placement *valid*, not every placement *fit*:** on a part without spare RAM
   the linker's orphan ordering can still overflow — gale relinked its 192 KiB
   STM32WB55 image without `--section-start` and lld placed the aligned
   `.synth.wasm_mem_1` ahead of the embedder's memory 0, overflowing RAM by
   64 KiB. On a RAM-constrained part, place `.synth.wasm_mem_k` explicitly
   (linker script or `--section-start`) relative to your own memory 0 and
   stack. **Watch memory 0's section too:** if you place a region-aligned
   memory 0 in `.bss`, its 64 KiB alignment raises the WHOLE `.bss` section's
   alignment and can push other runtime data past the end of RAM — gale moved
   memory 0 to a separate `.uninit` section. What each profile
   requires:
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
   **On silicon, those initial contents are your startup's job, never the
   flasher's:** a PROGBITS `.synth.wasm_mem_k` addressed in RAM is folded by
   lld into an in-file RAM segment, and a debugger's `program … verify` then
   fails (gale's STM32WB55 run; Renode loads such a segment directly and
   cannot show this). Flash only the flash-addressed contents and let your
   startup copy the memory's bytes into RAM.
   Memory 0's segments remain the `--embedder-data-init` promise.
5. **Programming the MPU is yours, and it is a memory-safety control.** synth
   emits NO MPU programming on this path — the symbols above are the input to
   YOUR startup, not a claim by synth that isolation exists. To compile with
   `--safety-bounds mpu` you must pass **`--embedder-mpu`**, which states that
   obligation; without it `mpu` REFUSES on every ARM relocatable object (single
   and multi-memory), and on self-contained images, RV32 and AArch64 it refuses
   outright (RQ-68-MPUHONEST, #1284). The object is byte-identical to
   `--safety-bounds none`; the safety manifest records
   `"mpu_programming": "embedder"`. Status of the arrangement: embedder-programmed; containment demonstrated by gale on Renode and on STM32WB55 silicon (#1145).
6. **Grant regions per EXECUTION CONTEXT, not per tenant.** An MPU region is a
   property of whoever is running, not of a tenant. Enabling every
   `__synth_mem_base_k` region at once hands memory k to whatever executes —
   including tenant A — and an image built that way LOOKS isolated and is not
   (gale's first two-tenant attempt escaped exactly this way). Each context
   switch must grant only the memory of the tenant about to run.

### Facts for your MPU gate: `--emit-memory-facts`, `--memory-domain` (RQ-91-MPUENFORCE, v0.91)

**The decision, and who made it.** #1145 asked for synth-emitted MPU
enforcement. On 2026-11-08 gale, the embedder whose isolation model this is,
chose that the embedder obligation stays the enforcement: gale's verified
`switch_to_partition` and its `gust:mpu/regs` seam stay the ONLY MPU writer,
because synth is build-time and outside the flight TCB. So synth emits **no
MPU register writes, no init routine and no RBAR/RASR words** on any path —
the encoding belongs to the embedder's verified driver. What synth delivers
instead is FACTS, as data, for the embedder's own build-time gate.

**`--emit-memory-facts`** (ARM `--relocatable --all-exports`, multi-memory
only) writes `<output>.memfacts.json` (`synth-memfacts-v1`). The object is
byte-identical with or without the flag; the sidecar carries the object's
`object_sha256`, so a sidecar beside a rebuilt object is detectable. A sidecar,
not a section: a section would change the object's bytes, and a linker merges
or drops same-named non-alloc sections across inputs, losing per-object
attribution; and `--emit-wcet`/`--emit-stack-depth` are sidecars already.

| Field | Meaning | Source |
|---|---|---|
| `functions[].direct_memories` | memories this `func_N` body accesses itself | the memory index of every load/store/`memory.fill`/both sides of `memory.copy` — a static immediate in wasm, so exact |
| `functions[].direct_calls` | the body's direct callees (`func_N`, or `module.field` for an import): with `direct_memories`, the call graph, so you can place a context switch at any edge | |
| `functions[].direct_multi_memory`, `direct_domains`, `direct_spans_domains` | the DIRECT reading. **Role: the key for the supervisor-only assertion.** `direct_spans_domains` = this body itself touches memories of more than one domain, so it is an adapter and must be supervisor code, wherever its callers run | |
| `functions[].sits_in_domains` | the domains the function runs in: its own body's, or, for a body that touches no memory, the union of its callers' (it runs in their context); `[]` for such a body nothing calls | |
| `functions[].direct_call_indirect` | this body itself contains a `call_indirect` | |
| `functions[].memories` | the grant a context running this function needs IF no context switch happens below it: the body plus everything it can call | closure over the direct call graph |
| `functions[].via_call_indirect` | `memories` was widened to every memory because a `call_indirect` is reachable | stated, never folded in silently |
| `functions[].imports_called` | host functions reachable by direct call; their accesses are YOURS and are not in `memories` | |
| `functions[].multi_memory`, `domains`, `spans_domains` | the TRANSITIVE reading. **Role: the key for the reachability / boundary census.** A tenant entry that calls a supervisor adapter is `true` here — a TRUE finding: that tenant entry can reach supervisor memory, through the crossing listed in `cross_domain_edges` — and `false` in `direct_spans_domains` | |
| `cross_domain_edges[]` | one entry per CALL SITE whose callee's call tree reaches a domain the caller does not sit in: `kind`, `caller` (+ `caller_export`), `callee`, `site` (`function_index`, `op_index`, `wasm_offset`), `caller_domains` (its `sits_in_domains`), `callee_domains` (its transitive `domains`). `kind: import` — every call to a host function, always listed (it leaves the module; its accesses are yours, so `callee_domains` is empty). `kind: call-indirect` — callee unknown, treated as reaching EVERY domain, as the memory sets treat it. Cutting exactly these edges leaves every function's reach inside its `sits_in_domains`: allowlist them as the sanctioned crossings. Empty without `--memory-domain` | the decoded call ops and the sets above |
| `field_roles` | the role of each reading above, carried in every sidecar | |
| `memories[].size_bytes` | declared size, exact for the process's life | read back: `__synth_mem_size_k` |
| `memories[].pmsav7_region_bytes` | smallest PMSAv7 region covering it (power of two, >= 32 B) | read back: `__synth_mem_region_k` |
| `memories[].base` | `symbol` (`__synth_mem_base_k` in `.synth.wasm_mem_k`, k >= 1), `register` (`r11`, memory 0), or `native` (memory 0 under `--native-pointer-abi`: native addresses, statics in `__synth_wasm_data` when present) | read back from the symbol table |
| `memories[].section_align`, `section_bytes` | `sh_addralign` / `sh_size` of `.synth.wasm_mem_k` | read back from the section header |
| `memories[].pmsav7_subregions_enabled` | when a section is padded to a subregion granule and does not fill its region, how many of its 8 subregions it covers; `null` otherwise (always `null` until a layout pads a section) | derived from `section_bytes` and the region |
| `memories[].pmsav8_granule_bytes` | 32: PMSAv8 (M33/M55) base and limit granule; any size is legal there, so nothing here assumes a power of two | |
| `not_covered` | what the facts do not cover, carried in every sidecar | |

Every bound is read back from the written object, never recomputed. The sets
come from the module and are cross-checked against the object before the
sidecar is written: the functions described are exactly the `func_N` bodies
the object defines, and a relocation in a function's own code against memory
k's base or size symbol (k >= 1) must find k in its `direct_memories` — a
disagreement refuses the compile. Memory 0 is not checkable that way (it is
R11-relative, and under `--native-pointer-abi` a relocation against its statics
can FORM a pointer a callee dereferences), so it rests on the execution oracle. Executed by `scripts/repro/memory_facts_1145_differential.py`: every
legitimate (wasmtime-non-trapping) access of every #1145, #1619 and #1622
multi-memory fixture, attributed by PC to its `func_N`, must be in that body's
`direct_memories` and in the called export's `memories`; the sets equal the
hand-written tables those oracles carry; a sidecar with one observed memory
removed reds. That is emulation (unicorn, which models no MPU) of the
SUFFICIENCY of the sets, not a containment result — containment is your MPU,
and its evidence is your Renode/silicon matched pair.

**`--memory-domain NAME=K[,K...]`** (repeatable, needs `--emit-memory-facts`)
names which memories each execution domain owns. A meld `--domain` maps to one
memory today; nothing assumes it. Every memory must belong to exactly one
domain — a map that leaves a memory out, or gives one to two domains, refuses.

**What none of this protects** (the compliance envelope, unchanged): an
out-of-bounds address of memory k can land in any memory, so a set is a
statement about legitimate accesses, not about where a bug can write; an
access between `size_bytes` and the region's end does not fault; an MPU fault
is not a wasm trap, and under `none`/`mpu` an out-of-bounds bulk op writes the
in-region bytes before it faults — only `--safety-bounds software` traps
before writing; privileged code can always reach the PPB, including the MPU
registers, so a contained tenant must run unprivileged; the globals table, the
stack and `.text` are shared by every context and are not in the sets.

### Bounds checking memory k: `software` only (#1619, v0.90)

Until v0.90 **memory k > 0 had no bounds-check story on any profile** (#1145,
the finding that outranked the MPU headline): `--safety-bounds software|mask`
loud-skipped every memory-k access, because both guards read R10 — **memory
0's size** by the register contract — and memory k has no size register.

`--safety-bounds software` now guards memory k against **this table's own
`__synth_mem_size_k`**: every lowered memory-k op (the i32/i64 load/store
families, `memory.fill`, `memory.copy` in either direction) loads it through
an `R_ARM_ABS32` literal and runs memory 0's guard against it, trapping with
an inline `UDF`. A bulk op checks every side's whole range before its loop
writes a byte (`dst+len`, and `src+len` for a copy: overflow or `> size`
traps, `== size` is in bounds), so an out-of-bounds fill or copy writes
nothing, as WebAssembly requires. The memory-0 side of a cross-memory copy is
checked against R10, as memory 0's own bulk ops are. What this asks of you:
nothing new — the guard reads the number you already program region k from,
so map memory k at (at least) `__synth_mem_size_k` bytes, as before.

Still refused, loudly (the function is skipped and the module fails via
#952):
- `--safety-bounds mask` on any memory-k access: mask wraps an address with
  `AND size-1`, which needs a power-of-two size, and `__synth_mem_size_k`
  need not be one (`(pagesize 1)`).
- under `--native-pointer-abi`, `software` or `mask` on a module that touches
  memory 0 at all (v0.91, #1661): memory 0's pointers are native there, and
  R10 bounds no native pointer. This one is a MODULE-level refusal
  (`npa-software-bounds`), not a skipped function; a module that touches only
  memory k is accepted.

The default `none` emits no memory-k guard (byte-identical to before), and
`mpu` + `--embedder-mpu` is byte-identical to `none`: an out-of-bounds fill or
forward copy writes the in-region bytes its loop reaches before the first
out-of-region byte faults. Only `software` gives a bulk op wasm's no-write
trap. Pinned executable: `scripts/repro/memk_bulk_oob_1619_differential.py`
(in-bounds, end-exact, straddling, fully out-of-bounds and wrapping fill,
copy and load/store on memories of three different sizes, vs wasmtime, with
the bytes after each memory's end watched) and
`scripts/repro/mem_isolation_red_1145.py` (the landed cross-tenant write
under `none`; both tenants contained under `software`).

### With `--native-pointer-abi` (RQ-89-MEMLAYER6, v0.89)

`--native-pointer-abi` is accepted on a multi-memory module since v0.89, and
it is layered per memory rather than applied to all of them:

- **Memory 0 is native**, exactly as on a single-memory object: R11 is 0, its
  statics live in the `__synth_wasm_data` reservation (`.bss`, plus the
  retargeted `__synth_wasm_seg_K` init segments in `.data` on the mixed
  split), its stack-pointer global is rebased on read, and a memory-0 pointer
  crossing the host boundary is a NATIVE address.
- **Memory k > 0 is a wasm offset**, exactly as without the flag: every
  access is `__synth_wasm_data_<k> + addr`, its `.synth.wasm_mem_k` section,
  `__synth_mem_base_k` and `__synth_mem_size_k` are unchanged, and a
  memory-k pointer crossing the host boundary is a wasm OFFSET.

The compiler enforces the split with a module-level value-provenance pass
(`crates/synth-core/src/npa_multi_memory.rs`, run by the CLI before
selection): a constant inside memory 0's static window that may be used as a
memory-k address stays raw, memory 0's stack pointer is chosen only among
globals that never reach memory k, and a value that may be used as an
address in BOTH memory 0 and memory k — a constant, the stack pointer, an
export parameter or an import result — is REFUSED, naming it. The pass is
field-insensitive per memory (one node stands for everything stored in a
memory), so a module that moves memory-0 contents into a memory-k address
can be refused although no single value is actually shared; that refusal is
imprecision, and is named as such in the oracle. Executed against wasmtime,
with an access-region isolation hook, by
`scripts/repro/npa_multi_memory_1145_differential.py`.

Bulk memory across memories (v0.89, same lane): `memory.copy dst_mem src_mem`
(0->k, k->0, k->k, j->k) and `memory.fill` on memory k are lowered on ARM
`--relocatable`, with and without `--native-pointer-abi`. Each side resolves
against its own memory (memory 0 at R11, memory k at `__synth_wasm_data_<k>`),
and the byte loop picks its direction on the absolute pointers, so a
same-memory copy is memmove-correct. Inline bounds checking of these ops:
since v0.90 (#1619) `--safety-bounds software` guards them against
`__synth_mem_size_k` (see "Bounds checking memory k" above); `mask` still
refuses every memory-k op. Under `--native-pointer-abi` the provenance pass charges each side
to its memory and lets the copied bytes flow between the two memories'
contents. Because it is field-insensitive, a module that stores pointers in
BOTH memories and copies across them can be refused although no value is
really shared. Executed by
`scripts/repro/multi_memory_bulk_1145_differential.py`.

#### `--embedder-copies-carry-no-pointers` — the Canonical-ABI assertion (opt-in)

The pass treats each memory's contents as one value, so a cross-memory
`memory.copy` joins the two memories' contents. A module that stores pointers
in BOTH memories (every Rust tenant and supervisor) and copies across them is
therefore refused by default, although no value is shared. The refusal message
names this flag.

- **What it asserts:** a cross-memory `memory.copy` never carries a value that
  is later used as an address in the DESTINATION memory. This is the Canonical
  ABI's own discipline: an adapter copies payload bytes and re-derives every
  pointer by allocating in the callee's memory, so a copied word is data there.
- **What synth does with it:** the provenance pass stops joining the two
  memories' contents at a cross-memory copy. Nothing else changes. A value that
  reaches an address in both memories by any OTHER route (a local, a call, a
  global, a store and load in one memory, a compare) is still tracked, and it
  is still refused. A same-memory copy is still tracked.
- **Who guarantees it:** whoever produced the copies. For a `meld --memory multi`
  fusion that is meld's adapter generator. For hand-written or other tooling,
  it is the integrator passing the flag. synth cannot check it.
- **If it is false:** a memory-0 pointer copied into memory k (or the reverse)
  keeps its source memory's representation. Memory 0's is native
  (`__synth_wasm_data + C`) and memory k's is a wasm offset. Dereferencing it in
  the destination memory SILENTLY reads or writes the wrong address, out of
  region or into another tenant. There is no trap: this is the failure the
  default refusal exists to prevent. `scripts/repro/npa_multi_memory_1145_differential.py`
  executes exactly that violation under the flag and requires it to diverge
  from wasmtime.
- The flag is refused without `--native-pointer-abi`, where it would mean
  nothing.

Region 0 under this flag is not the R11 value (R11 is 0): it is the linked
`__synth_wasm_data` reservation plus the `.data` section that holds the
retargeted init segments and `__synth_globals`. `__synth_mem_size_0` still
reports memory 0's DECLARED bytes, which is what an embedder sizes a region
from; the `.bss` reservation itself can be smaller (it covers the used
extent).

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

## `--native-pointer-abi`: memory-0 address provenance (RQ-91-NPAMODEL, v0.91)

Under `--native-pointer-abi` R11 is 0 and every memory-0 address is a NATIVE
pointer. A wasm static at offset `C` is reached as `__synth_wasm_data + C`
(retargeted to `__synth_wasm_seg_K` on the split layout). Which values are
wasm statics is decided ONCE per module by the provenance pass
(`synth_core::npa_multi_memory::Provenance::memory0_plan`), and the emitted
instruction stream is checked against the same rule by the ARM backend
(`npa_stream_validate`: a compile-time-constant address inside memory 0's
static range that carries no relocation is a compiler defect, refused as
`npa-addr-validate`). These are the rules; each is a promise one side makes.

**What synth decides (category (a)).**
- With a stack-pointer global, a constant in `[sp_init, memory-0 size)` is a
  pointer and is relocated wherever it appears; a run-time value added to it
  is an index.
- A constant address computed only from constants — through locals, `select`,
  `i32.add` / `i32.sub` — is a static and is relocated at its definition (the
  larger term of an add, the minuend of a sub). This includes statics BELOW
  the stack-pointer init (a toolchain that places data under the stack) and
  the i64 / f32 / v128 / bulk arms.
- Refused for the whole module (non-zero exit, no object, NOT waived by
  `--allow-skipped-exports`), each with its own diagnostic name:
  - `npa-data-pointer (#1672)` — a data-segment WORD holding a wasm address in
    the static range may be loaded and then dereferenced as the pointer.
    Initialised data ships verbatim, so the word is a wasm offset, not a
    native address. The diagnostic names the dereferencing function, the
    load site and the word's segment offset. A word only loaded (returned,
    compared) is not refused, and a loaded value used as an INDEX added to a
    static (`HEAP + OFF`) is not refused.
  - `npa-dynamic-static-offset (#1568)` — with a memory-0 data segment and no
    stack-pointer global (or below the stack-pointer init), a constant or
    memarg offset in the static region beside a run-time value.
  - `npa-static-observed (#1568)` — a static constant below the
    stack-pointer window that is also consumed as a scalar (a comparison, a
    branch condition, arithmetic other than add/sub, or a value handed to the
    host).
  - `npa-static-unrelocatable (#1568)` — a constant static address no
    constant of which can carry the relocation, a local's implicit zero
    dereferenced, or a static constant that reaches an address only through
    memory or a global.
  - `npa-region-straddle (#1604)` — on the split layout, a constant access
    whose bytes span two regions, a relocated constant naming another region
    than the bytes accessed, or a bulk op with a constant destination and a
    run-time length.
  - `npa-double-relocation (#1580)` — a self-relocated memarg offset added to
    an address that already carries a relocated static.
  - `npa-software-bounds (#1661)` — `--safety-bounds software|mask` with any
    memory-0 access.

**What you promise (category (b)) — R1-R3′.**
- **R1 (pointer arithmetic stays in its object).** A static pointer plus a
  RUN-TIME delta stays inside the object the pointer names: within the
  CLOSED range `[base, base + size]`, one-past-the-end included (slice
  iterators compute `end = base + len`). synth checks the bytes only where the
  delta is a constant; across the split layout an access past the object can
  land in packing padding or another segment. `wrapping_add` and arithmetic
  through integer casts fall outside this guarantee.
  **KNOWN GAP in the one-past-the-end half (measured, v0.91, not fixed):** on
  the split layout (every data segment at or above the stack-pointer init) a
  CONSTANT that names one past a data segment's end is relocated by the
  region that contains that address — the zero reservation, or whichever
  segment starts there — not by the segment it ends. A pointer walked from the
  segment's start is then never equal to it: `p = 0x2000; while p != 0x2008`
  over an 8-byte segment at 0x2000 (stack pointer 0x1000, next segment at
  0x3000) sums 0x1043 where wasmtime returns 0x3, identically on v0.90.0 and
  v0.91. It cannot be resolved by rule: such a constant is equally the start
  of whatever follows (a `.bss` object placed right after `.data`). Until it
  is decided (RQ-91-NPAMODEL, residual), an end pointer that is a constant
  equal to a data segment's end is safe only when the contiguous one-image
  layout applies (a segment below the stack-pointer init) or the following
  segment is declared next and the segment's length is a multiple of 4.
- **R2 (no data, no stack pointer: run-time values are native).** In a module
  with no memory-0 data segment and no stack-pointer global, there is no
  static region: a run-time value that reaches an address is a native pointer,
  and a constant added to it is an offset (the `MMIO_BASE + reg` shape of a
  peripheral driver). The ambiguity refusal above applies only to modules
  that HAVE a memory-0 data segment.
- **R3′ (host pointers into the statics were handed out first).** A pointer
  the host passes into the module's statics is one the module itself produced
  earlier — a realloc result (`cabi_realloc` returning `HEAP + OFF`), an
  exported address, a buffer handed out and received back. It is therefore
  already native. The provenance pass assumes a host pointer may point into
  every region whose address left the module through an export result or an
  import argument, and no other.

Pinned executable: `scripts/repro/npa_model_differential.py` (one row per
shape: executed against wasmtime, or refused with its named diagnostic; red on
eab66646), plus the five earlier native-pointer oracles.

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
memory-0 access; on a multi-memory object `software` also guards memory k
against `__synth_mem_size_k`, and `mask` refuses memory k (#1619).
