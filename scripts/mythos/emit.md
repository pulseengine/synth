You are emitting a new loss-scenario entry to append to
`safety/stpa/loss-scenarios.yaml`. Consult the existing file for
shape.

Input:
- Confirmed bug report (below)
- Chosen `UCA-N` from the validator
---
{{confirmed_report}}
UCA: {{uca_id}}
---

Rules:
1. Grouping invariant: loss-scenarios group under UCAs.
2. New id follows the existing scheme (read the file).
3. Required fields match existing entries. Do not invent fields.
4. In the `scenario` prose, reference the Kani / Rocq harness and
   the QEMU differential test by path. Cite the WebAssembly spec
   section AND the ARM Architecture Reference Manual section that
   the bug violates (e.g., "AAPCS32 §6.2.1 argument passing" or
   "Core Spec §4.4 instructions → control").
5. Optional `related-cve:` for wasmtime compiler precedents.
6. If this is proof-code drift (the Rocq proof is correct but the
   Rust code has diverged from the proof's spec), set
   `type: proof-drift` if the schema allows, else note it in the
   scenario prose. Drift needs different remediation than a
   backend bug.
7. Add `status: draft`. Humans promote to `approved`. Synth
   ships firmware — no draft → deployed path without human review.

Emit ONLY the YAML block, nothing else.
