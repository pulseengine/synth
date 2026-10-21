# RQ-88-MEMLAYER5 (#1145) — why the `--native-pointer-abi` multi-memory refusal stays

Evidence, not a CI gate. Measured 2026-10-20 with version-matched builds (`synth 0.87.0`).

- `two_mem_npa.wat` — synthetic stand-in for the reporter's shape (the real module is
  unpublished): memory 0 = 1 page, memory 1 = 2 pages, stack pointer at 0x1000, data in
  both memories. At HEAD, `--relocatable --native-pointer-abi` refuses it (rc=1).
- `one_mem_npa.wat` — single-memory control; compiles (rc=0) at HEAD.
- `two_sp_npa.wat` — two stack pointers (domain 0 at 0x1000, domain 1 at 0x8000), the
  shape `meld --domain` produces.
- `npa_mm_diff.py WAT OBJ` — runs the object under unicorn (R11 = 0, each section at
  its own base) and compares every export against wasmtime with multi-memory on.

With BOTH refusals patched out in a scratch build, `two_mem_npa.wat` compiles silently
(rc=0, 6/6 functions) and the differential exits 1: `read1_static()` returns `0x0`
where wasmtime returns `0xaaaaaaaa`, because a memory-0 constant rewritten to
`__synth_wasm_data + v` is then added to `__synth_wasm_data_1`. The paired controls in
the same run (`read1_ctrl`, `read0_static`, `read1_dyn`) pass; `write1_read1` passes
only because the store and the load land in the same wrong place.

So the refusal is what stands between this shape and a silent cross-memory miscompile.
Adding a memory index to `static_data_addend` would NOT fix it: the rewrite happens on
the VALUE (`I32Const`, stack-pointer global reads), before any access knows its memory.
A correct lift needs module-level provenance on rewritten values (including through
calls, stores, returns and `global.set`) and a stack-pointer pick that knows which
memory each global belongs to.
