# The embedder ABI for `-b aarch64 --relocatable` — arm64-Linux host libraries (RQ-64-ARM64LINUX)

This document states the register and layout contract between a synth
`-b aarch64 --relocatable` object (a SysV ELF64 `ET_REL` for `EM_AARCH64`)
and the host program that links and runs it, and it names exactly what is
PROVEN about that path and by which oracle. It is the AArch64 counterpart of
[`embedder-abi-relocatable-arm.md`](embedder-abi-relocatable-arm.md) and
follows the same rule: every fact is **derived from the code that emits it**,
cited as `file:line` (line numbers as of the commit that landed this document;
the symbol names beside them survive drift), and the load-bearing facts are
pinned in `claims.yaml` (`SYNTH-EMBEDDER-ABI-RELOCATABLE-AARCH64-RQ64`), so
an emitter change that invalidates a sentence here turns `claim-check` red.

## The claim, and the instrument behind it

**A `synth compile -b aarch64 --target cortex-a53 --relocatable` object links
into a normal arm64-Linux static executable/library with a stock host linker,
and the linked code executes with results matching wasmtime.** Until v0.64
this was true by accident — the object had the right container and `nm`
showed global symbols, and nothing more was ever checked. The evidence is now
`scripts/repro/arm64_linux_host_link_rq64_differential.py` (CI-wired; fixture
`arm64_linux_host_link_rq64.wat`), which on every run:

1. compiles the fixture exactly as above;
2. GENERATES a freestanding C harness from its own case table (one source
   for the C call sequence and the wasmtime call sequence), compiled with
   `clang -target aarch64-unknown-linux-gnu -ffreestanding -nostdlib
   -ffixed-x28`, plus an assembly `_start` that sets `x28` once — the
   harness's only kernel surface is `write(2)` and `exit_group(2)`;
3. links `_start` + harness + object with **`ld.lld -m aarch64linux
   -static`** and checks the image with pyelftools: `ET_EXEC`, `EM_AARCH64`,
   `ELFOSABI_SYSV`, zero undefined symbols, zero `.rela` sections left,
   every synth symbol present;
4. EXECUTES the image and compares every printed value against a wasmtime
   instance that ran the same sequence with the same host import — under
   unicorn with the Linux ELF loader's semantics reproduced (PT_LOAD at
   vaddr, bss zeroed, fresh stack, `e_entry`), **natively** on the
   `ubuntu-24.04-arm` CI runner (`REQUIRE_NATIVE=1`), and under
   **qemu-user** on the x86-64 CI runner (`REQUIRE_QEMU=1`) — an independent
   ELF loader and syscall layer, not the oracle's own 30 lines;
5. carries its own red-first controls: an `EM_ARM` object handed to
   `-m aarch64linux`, the aarch64 object handed to `-m elf_x86_64`, and a
   harness without the import's definition must each be REFUSED by the
   linker with the message naming the cause; and a bit flipped in `add`'s
   first instruction in the LINKED image must produce a reported mismatch.

What crosses the boundary in that fixture, each a separate way the claim can
be false: host→synth calls in w/x/d registers; synth→host through an
IMPORT (`host_add`, a `SHN_UNDEF` symbol the linker binds to C); synth→synth
`bl` to a non-exported local; linear memory through `x28`, checked from BOTH
sides (synth stores, C reads the byte at `base + addr`; C writes, synth
loads); globals in synth's own `.data`, persisting across calls;
`call_indirect` through the synth-emitted funcref table; a value below an
import call's arguments (RQ-63-A64STACK); `memory.size`.

### What the oracle does NOT verify

Stated so the claim cannot outrun its instrument:

- **Traps.** Every case is non-trapping on purpose: a WASM trap is `brk #0`
  (`crates/synth-backend-aarch64/src/encoder.rs:424`; the OOB guard at
  `selector.rs:1425` and its statically-unreachable-offset form at `:1412`,
  ÷0 at `:1196`, `INT_MIN/-1` at `:1235`, the float→int domain guard at
  `:1042` — 36 `enc::brk(0)` sites in all), which on Linux is **SIGTRAP**
  and kills an unprepared process. Trap PLACEMENT is gated by the sibling unicorn oracles
  (`aarch64_bounds_865_differential.py`,
  `aarch64_call_indirect_851_differential.py`, `aarch64_divrem_851_…`); what
  the embedder does with SIGTRAP is the embedder's contract.
- **Dynamic linking.** No shared object, PLT, GOT, TLS or dynamic
  relocation is emitted or exercised; the claim is a STATIC library and
  `-static` is what ran. Every relocation synth emits is PC-relative
  (`R_AARCH64_CALL26`/`JUMP26`/`ADR_PREL_PG_HI21`/`ADD_ABS_LO12_NC`,
  `elf.rs:15-23`), so a `-pie` link is plausible — and NOT claimed.
- **libc.** The harness is freestanding. A libc-linked embedder adds nothing
  synth's object depends on, but it is not what executed.
- **Anything about the ISA the sibling oracles already cover** — op
  semantics, rounding, trap tables. This oracle is about the CONTAINER and
  the ABI boundary, deliberately.

## The register contract

| Register | Meaning | Who sets it | Who chooses the value | Category |
|---|---|---|---|---|
| **x28** | Linear-memory (memory 0) base address | Embedder, before any export runs | Embedder | (b) chosen |
| x0–x7 / v0–v7 | AAPCS64 argument and result registers | — | — | (a) fixed (AAPCS64) |
| x9–x15 | synth's value-stack temps — clobbered freely | synth | synth | (a) fixed |
| v16–v23 | synth's FP value-stack temps — clobbered freely | synth | synth | (a) fixed |
| x16, x17 (IP0/IP1) | `call_indirect` dispatch scratch — clobbered | synth | synth | (a) fixed |
| x18 | Platform register — **never touched** by emitted code | — | — | (a) fixed |
| x19–x27, v8–v15 | Callee-saved — **never touched** by emitted code | — | — | (a) fixed (AAPCS64) |
| x29, x30 | Frame pointer / link register — saved by every non-leaf prologue | synth | — | (a) fixed (AAPCS64) |
| SP | AAPCS64 stack, 16-byte aligned at every call | Embedder (entry SP) | Embedder | (b) chosen |

There is **no size register and no globals register** on this backend. That
is the single biggest difference from the ARM contract (R9/R10/R11), and it
is why this object needs one precondition where the Cortex-M one needs three.

### Where each fact comes from

- **`x28` is the linear-memory base, read-only to emitted code.**
  `const LINMEM_BASE: Reg = 28;`
  (`crates/synth-backend-aarch64/src/selector.rs:181`), with the contract
  spelled out at `:165-180`: "A memory-using function expects
  `x28 = __linear_memory_base` on entry … the lowering only READS it (never
  clobbers)". Every memory access forms `x28 + uxtw(w_addr) + memarg.offset`
  (`:1371`, `:1444`, `:2255-2260`). The FRONTIER note at `:174-180` is the
  precondition itself: "this backend does NOT yet EMIT anything that
  establishes `x28` — there is no aarch64 startup / linker script".
- **The temp universe is x9–x15 and v16–v23.** `const TEMPS: [Reg; 7] = [9,
  10, 11, 12, 13, 14, 15];` (`selector.rs:151`), `const FTEMPS: [FReg; 8] =
  [16, …, 23];` (`:155`). Nothing outside those, the argument registers, IP0/
  IP1 and the frame registers is ever a destination — which is what makes
  x19–x27 and v8–v15 "never touched" rather than "saved and restored".
- **IP0/IP1 are clobbered by `call_indirect`.** The dispatcher materializes
  the funcref-table slot address in `x16` and reads the class id into `x17`
  (`selector.rs:2646-2656`, emitted at `:2768-2771`). AAPCS64 already makes
  them caller-owned scratch.
- **x18 is never written.** The selector's register-choice rationale names
  it among the registers deliberately excluded (`selector.rs:169`). A Linux
  embedder that reserves x18 (`-ffixed-x18`) is unaffected; one that does
  not is equally unaffected.
- **Non-leaf prologue saves FP/LR.** `stp x29, x30, [sp, #-16]!`
  (`selector.rs:364`, `:563`); frames are rounded to 16 bytes (the
  RQ-57-A64PARAM home-slot model, `:80-96`), and RQ-63-A64STACK's spill area
  around a call is 16-byte aligned and released before the result move —
  callee-saved x19–x28 and SP are asserted intact after every run by
  `aarch64_call_valstack_rq63_differential.py`.

## Memory: no size register, a baked limit, no growth

- **The bounds limit is an IMMEDIATE, not a register.** Under the CLI default
  `--safety-bounds software`, the selector receives
  `MemBounds::Software { limit_bytes: config.linear_memory_bytes }`
  (`crates/synth-backend-aarch64/src/backend.rs:77-79`; the enum at
  `selector.rs:193-204`) — the module's DECLARED initial memory in bytes —
  and every access proves `uxtw(addr) + offset + size <= limit` before the
  dereference or executes `brk #0` (`:1399-1425`). `--safety-bounds none`
  emits no check (`MemBounds::Unchecked`); `mask`/`mpu` hard-error rather
  than silently degrade (`backend.rs:80-90`, #865).
- **Consequence for the embedder:** the region at `x28` must be **at least
  `initial_pages × 65536` bytes** — the guard believes the declared size,
  and there is no register through which a larger or smaller reservation
  could be communicated. Reserving MORE is harmless (the tail is simply
  unreachable to the module); reserving LESS turns an in-bounds-by-the-guard
  access into a host memory fault or a silent read of whatever follows.
- **`memory.size` is the declared minimum; `memory.grow` is −1.** Both are
  constants (`selector.rs:2515-2560`, the #539 rule): memory is a FIXED host
  buffer on this backend, so the size never changes for the life of the
  process and the embedder never needs to re-establish anything.
- **Alignment.** The fixture's harness page-aligns its buffer; synth requires
  nothing beyond what the bus does — AArch64 Linux tolerates unaligned
  normal-memory accesses, so even that is not load-bearing. 16-byte
  alignment is a reasonable habit, not a contract.

## Timing and preservation

**`x28` must hold the base before the first export is entered, and the
embedder may set it once.** Two checkable reasons:

1. Emitted code never writes it (the destination universe above).
2. Anything the object calls OUT to — the imports it was compiled against —
   must preserve it, because x28 is AAPCS64 callee-saved. Any C compiler
   honours that by construction; the oracle's `host_add` is ordinary `-O2`
   C. The one way "set once" fails is an embedder callback that clobbers
   x28 without restoring it, and that is the callback's bug.

Two ways to keep it set, both measured:

- **Reserve it.** Compile every host object with `-ffixed-x28` and
  establish the register in startup before entering C (the oracle's `_start`
  does `adrp x28, linmem; add x28, x28, :lo12:linmem`). This is the shape
  the oracle executes.
- **Trampoline.** If the host's compile flags are not yours, call every
  export through an assembly shim that saves x28, loads the base, `blr`s,
  and restores x28. Per-call re-establishment is unnecessary but harmless.

Do NOT set x28 from inline asm inside an ordinary C function: without
`-ffixed-x28` the compiler may have x28 live across that point, and the
symptom is a wrong value on some other path, not a build error — the #1131
"conformed correctly by luck" shape on this backend.

## What is NOT a precondition (synth emits it)

- **Globals** live in synth's own `.data`, at the `STT_OBJECT` symbol
  `__synth_globals` (`crates/synth-backend-aarch64/src/substrate.rs:56-64`
  layout — one 8-byte slot per global; the symbol planned in `elf.rs`
  `plan_object`, LOCAL since RQ-65-FUNCN — see "Symbols" below),
  **with their decoded constant initializers already in the bytes**. A normal
  static link places the section and the loader maps it; there is no globals
  register and nothing for the embedder to seed. Code reaches the region by
  `adrp` + `add :lo12:` against that symbol (`substrate.rs:1-24`), which the
  linker resolves — `ld.lld` even relaxes the pair to `nop` + `adr` when the
  region is within range, which is standard and harmless.
- **The funcref table** (`__synth_func_table`, `substrate.rs:36-49`) is
  emitted in `.text`, one `[u32 class id][b func_N]` record per slot, with
  the `R_AARCH64_JUMP26` trampolines the linker resolves. No table register,
  no element-segment work for the embedder.
- **Active data segments are REFUSED**, loudly, at compile time
  (`backend.rs:259-275`, and the non-const-offset twin at `:277-285`): this
  backend ships no data section for linear memory and no startup to copy one,
  so a data-carrying module does not compile rather than run with zeros where
  segment bytes belong. There is therefore no `--embedder-data-init`
  promise on this path — the flag exists for the ARM relocatable contract.

## Symbols: what the link sees, and what it does not

- **Exports:** an exported function is a GLOBAL `STT_FUNC` symbol under its
  wasm export name (`backend.rs:334-340`); the binding is the plan's
  (`elf.rs` `PlannedSymbol::binding`, rendered as `st_info = (bind << 4) |
  type` in `build_relocatable_object_full`). Read the symbol table by
  section type (`SHT_SYMTAB`), not name.
- **Imports:** a called import becomes a GLOBAL `STT_FUNC` at `SHN_UNDEF`
  under its wasm FIELD name (`elf.rs` `plan_object`, `backend.rs:405-410`,
  the #1017 wasm2c/Wasker pattern), with an `R_AARCH64_CALL26` at each call
  site. Define it in C with the matching AAPCS64 signature and the linker
  binds it; omit it and `ld.lld` refuses with `undefined symbol: host_add`
  (the oracle pins that refusal).
- **Everything synth invents for its own addressing is LOCAL** (RQ-65-FUNCN,
  #1180): the `func_N` call label every function carries (N = full function
  index, imports first), the globals region `__synth_globals`, and the
  funcref table `__synth_func_table` are `STB_LOCAL`, listed first in
  `.symtab` with `sh_info` at the first non-local symbol (the ELF rule #656
  established for ARM, now applied through the one shared
  `synth_core::backend::locals_first`). They are still IN the symbol table —
  `nm` shows `t func_1`, `d __synth_globals`, a debugger sees them — but
  they take no part in cross-object resolution: this object's own
  `CALL26`/`JUMP26`/`ADR_PREL_PG_HI21`/`ADD_ABS_LO12_NC` relocations bind to
  them by symbol index, and nothing outside the object needs their names.
  **Consequence, measured and EXECUTED by the oracle:
  two synth aarch64 objects link into one program unaided** — the fixture
  plus a second module (`scripts/repro/colink_second_rq65.wat`) that also defines its own
  `func_1`, `__synth_globals` and `__synth_func_table`, linked by `ld.lld`
  with no objcopy step, every value from BOTH objects matching wasmtime. The
  `llvm-objcopy --localize-symbol` workaround the v0.64 edition of this
  document recorded is no longer needed; the oracle now proves the opposite
  direction too (re-globalizing `func_N` in both objects brings
  `duplicate symbol: func_1` back). The Mach-O container makes the same
  decision by construction — the binding is a field of the shared
  `ObjectPlan`, not a per-writer choice — so `nm` on a `--object-format
  macho` object shows `t _func_1`, `d ___synth_globals`, `T _add`.
- **Deliberate divergence from ARM, so it is not "fixed" later:** ARM keeps
  `__synth_globals` GLOBAL because its embedder contract loads R9 with that
  address (`docs/embedder-abi-relocatable-arm.md`). This backend has no
  globals register — code reaches the region by `adrp`+`add :lo12:` — so
  the name is object-private here.
- **The `@`-in-export-names hazard** from the ARM document applies unchanged
  to a C `__asm__` label here; the `objcopy --redefine-sym` workaround is
  the same.

## The container: what makes this "Linux", and what does not

- **Target.** `--target cortex-a53` is the only `-b aarch64` target
  (`crates/synth-cli/src/main.rs:1201`, `:1253`;
  `supported_targets` at `backend.rs:222-223`); its `TargetSpec` triple is
  `aarch64-none-elf` (`crates/synth-core/src/target.rs:455-463`). There is
  no `aarch64-unknown-linux-gnu` triple and none is needed: the object
  carries **nothing OS-specific** — `EI_OSABI` 0 (SysV), no notes, no
  `.ARM.attributes`-style metadata, no PLT/GOT/TLS, no dynamic relocations.
  Its "Linux-ness" is precisely the SysV ELF64 container plus AAPCS64, which
  is what `ld.lld -m aarch64linux` consumes. The same object would link for
  any ELF64/AArch64/SysV target; only arm64-Linux is CLAIMED, because that is
  what the oracle executes.
- **Emulation.** `ld.lld` also accepts the object with no `-m` at all (it
  infers `aarch64linux` from `e_machine`); the oracle passes `-m` explicitly
  so the wrong-target refusals (`is incompatible with aarch64linux`,
  `is incompatible with elf_x86_64`) are the linker's own words.
- **The CLI's post-compile hint.** Before v0.64 every relocatable compile,
  aarch64 included, printed `Link with: arm-none-eabi-ld … kiln_bridge.o`.
  The aarch64 line now names the toolchain that was actually exercised.

### Linking recipe (the one the oracle executes)

```
synth compile m.wat -b aarch64 --target cortex-a53 --relocatable --all-exports -o m.o
clang -target aarch64-unknown-linux-gnu -ffreestanding -nostdlib -ffixed-x28 -c host.c
clang -target aarch64-unknown-linux-gnu -c start.s
ld.lld -m aarch64linux -static -e _start -o prog start.o host.o m.o
#   (or: clang -target aarch64-unknown-linux-gnu -fuse-ld=lld -nostdlib -static …)
```

On an arm64-Linux host `./prog` simply runs. On any host, `qemu-aarch64 prog`
runs it; the oracle additionally runs it under unicorn with the loader
semantics reproduced.

## What is INCIDENTAL — observed in the oracle, guaranteed by nothing

Category (c). Do not build a harness on any of these:

- The harness's buffer placement (`.bss`, page-aligned, 64 KiB) and the
  addresses `ld.lld` chose (`0x200000`-based). Any disjoint, large-enough,
  readable-writable region works.
- `_start` establishing x28 via `adrp/add` to a symbol. A `mov` from a
  `malloc` result is equally fine — the register is what synth reads.
- `-static`. Chosen because it is the shape claimed; see "Dynamic linking"
  above for what is not claimed.
- `ld.lld` specifically. GNU `ld` for aarch64-linux consumes the same
  relocation set; it was not what ran, so it is not what is claimed.
- **A working result does not verify the method that produced it.** Copied
  verbatim from the ARM document because it is the lesson of #1131: a
  harness that happens to leave x28 correct — because the C compiler
  happened not to allocate it — passes every case above and is still wrong.

## Compliance note

With `--safety-bounds software` (the aarch64 default) every access traps
out-of-bounds at `brk #0`; with `--safety-bounds none` there is no OOB trap —
see the "Compliance envelope" section of `CLAUDE.md`. Multi-memory is not
lowered on this backend (declines loudly).
