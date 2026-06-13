# synth#329 — multi-value-call-result × select underflow

`synth compile --cortex-m --all-exports` silently skips a function when a
**multi-value `call` result** feeds a **`select`**: the abstract value-stack
under-counts the call's 2 results to 1, so `select` (which pops 3) reports a
spurious underflow on a module `wasm-tools validate` accepts. Surfaced as the
`func_39` skip in the falcon flight core (`func_30` LocalSet is one consumer over).

| fixture | wasm-tools | synth today | after fix |
|---|---|---|---|
| `repro_call_select.wat` | VALID | **SKIPS** (underflow at select) | compiles; `f(1)=10`, `f(0)=20` (wasmtime golden) |
| `control_block_select.wat` | VALID | compiles | compiles |
| `control_single_call_select.wat` | VALID | compiles | compiles |
| `control_call_drop.wat` | VALID | compiles | compiles |

The `drop`-vs-`select` split is the discriminator: a multi-result call alone is
counted correctly (drop sees both), and single-result calls into select work — it
is specifically the **multi-result-call × select** operand-pop interaction.

Regression lock: the repro must compile **and `f` evaluate to the wasmtime
golden** (`f(1)=10`, `f(0)=20`) after the fix; the three controls must stay
compiling. Independently reproduced on synth v0.11.40 (gale wasm-cross-LTO side;
jess `repro/synth-underflow/` keeps a loop-record copy, this is the canonical
source fixture).

## The fix is two-sided (do not land a caller-only patch)

Root cause confirmed by source + disassembly on v0.11.40:

1. **Caller** (`instruction_selector.rs`, the `Call` arm): after a `BL` it pushes
   exactly **one** operand-stack entry per call, regardless of the callee's
   result count — so `call $two` leaves 1 value where wasm has 2, and `select`
   (pops 3) underflows in `pop_operand` ("stack underflow: malformed WASM or
   compiler bug").
2. **Callee** (`$two`): multi-value return is unimplemented — `$two` compiles to
   `movs r4,#10; movs r5,#20; bx lr`, leaving its results in **r4/r5**, not the
   AAPCS return registers **r0/r1**.

Because of (2), a caller-only fix that just pushes both results would **compile
but miscompile** — the caller would read r0/r1 while the callee wrote r4/r5,
turning today's *safe skip* into silent wrong-code. The two sides must land
together and be gated on a differential **run** (the golden above), not on "it
compiles". Tracked as a multi-value-return ABI item, not a one-line patch.
