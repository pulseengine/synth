# synth#329 — multi-value-call-result × select underflow

`synth compile --cortex-m --all-exports` silently skips a function when a
**multi-value `call` result** feeds a **`select`**: the abstract value-stack
under-counts the call's 2 results to 1, so `select` (which pops 3) reports a
spurious underflow on a module `wasm-tools validate` accepts. Surfaced as the
`func_39` skip in the falcon flight core (`func_30` LocalSet is one consumer over).

| fixture | wasm-tools | synth today | after fix |
|---|---|---|---|
| `repro_call_select.wat` | VALID | **SKIPS** (underflow at select) | compiles, `f` returns hi-word |
| `control_block_select.wat` | VALID | compiles | compiles |
| `control_single_call_select.wat` | VALID | compiles | compiles |
| `control_call_drop.wat` | VALID | compiles | compiles |

The `drop`-vs-`select` split is the discriminator: a multi-result call alone is
counted correctly (drop sees both), and single-result calls into select work — it
is specifically the **multi-result-call × select** operand-pop interaction.

Regression lock: the repro must compile (and `f` evaluate correctly) after the
fix; the three controls must stay compiling. Independently reproduced on
synth v0.11.40 (gale wasm-cross-LTO side; jess `repro/synth-underflow/` keeps a
loop-record copy, this is the canonical source fixture).
