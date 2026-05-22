# SBOM — CycloneDX Software Bill of Materials

synth can emit a **CycloneDX 1.5 JSON SBOM** alongside every ELF it compiles.
The SBOM documents the compilation transaction: what compiled the binary, what
went in, and what came out. It is synth's contribution to the PulseEngine
supply-chain story — see [rivet #107](#rivet-107-linkage) below.

This is a **build SBOM**, not a transitive dependency scan. synth is a
compiler, not a linker, so the SBOM records what synth actually knows.

## Emitting an SBOM

`synth compile` accepts a `--sbom` flag:

```bash
# Write <output>.cdx.json next to the ELF
synth compile vehicle-control.wat -o vehicle-control.elf --sbom

# Write to an explicit path
synth compile vehicle-control.wat -o vehicle-control.elf \
  --sbom sbom/vehicle-control-v1.0.0.cdx.json
```

`--sbom` is a flag on `compile` rather than a standalone subcommand because
synth already has every input in hand at compile time — the WASM bytes, the
decoded imports, the target triple, the backend, and the freshly written ELF.
A separate `synth sbom <in> <out>` subcommand would have to re-derive all of
that, and could not see the WASM bytes that were actually compiled (after WAT
decoding and any Loom pass).

The conventional file name is `<stem>.cdx.json` (the standard CycloneDX-JSON
suffix). A bare `--sbom` writes the SBOM next to the ELF using that
convention; `--sbom PATH` writes to `PATH` verbatim.

`--sbom` requires a WASM/WAT input file. Built-in demo compilations
(`--demo add`) have no input module, so `--sbom` is skipped with a warning.

## What the SBOM contains

A CycloneDX 1.5 document with these top-level fields:

| Field          | Content                                                       |
|----------------|---------------------------------------------------------------|
| `bomFormat`    | `"CycloneDX"`                                                 |
| `specVersion`  | `"1.5"`                                                       |
| `serialNumber` | `urn:uuid:...`, derived deterministically from the ELF digest |
| `version`      | `1`                                                           |
| `metadata`     | `timestamp` + `tools` (the synth compiler entry)              |
| `components`   | the input WASM, the output ELF, one per WASM import           |
| `dependencies` | a graph linking the output ELF to its inputs                  |

### Components

1. **The synth compiler** — recorded under `metadata.tools` as
   `{ vendor: "PulseEngine", name: "synth", version: <CARGO_PKG_VERSION> }`.
   This is *what built it*.

2. **The input WASM module** — a `library` component with the file name, a
   SHA-256 hash, and the byte size. The hash is of the WASM bytes synth
   actually compiled (after any WAT→WASM decode and Loom optimisation pass),
   so it reflects the true compilation input.

3. **The output ELF binary** — an `application` component with the file name,
   SHA-256 hash, byte size, the target triple (e.g. `thumbv7em-none-eabi`,
   `riscv32imac-unknown-none-elf`), and the backend used (`arm`, `riscv`,
   ...). These appear as `synth:`-namespaced `properties`.

4. **The WASM module's imports** — each imported function / memory / table /
   global becomes a `library` component (`synth:artifact: wasm-import`). This
   is the closest synth can get to "what is linked into the binary" without a
   full linker view.

### The dependency graph

The `dependencies` array links the output ELF (`bom-ref` `elf:<name>`) to the
input WASM (`wasm:<name>`) and to every import (`import:<module>/<name>`). The
WASM module in turn depends on its imports. Every `bom-ref` appears as a graph
node, so the graph is complete and traversable.

### Determinism

For a fixed set of inputs the document is byte-stable **except for
`metadata.timestamp`**, which is wall-clock by design — a CycloneDX SBOM
records when the build happened. The `serialNumber` is derived from the output
ELF's SHA-256, so it is reproducible for a given binary.

## rivet #107 linkage

The sibling PulseEngine repo `rivet` (issue #107, *Supply chain integration:
Sigil attestations + SBOM/AIBOM + Rivet traceability bridge*) defines an
`sbom-record` artifact type that ingests a CycloneDX SBOM:

```yaml
- id: SBOM-vehicle-control-v1
  type: sbom-record
  format: cyclonedx
  sbom-ref: "sbom/vehicle-control-v1.0.0.cdx.json"
  component-count: 142
```

The file synth writes with `--sbom` is exactly what that record points at.
The consumption path is:

```bash
synth compile vehicle-control.wat -o vehicle-control.elf \
  --sbom sbom/vehicle-control-v1.0.0.cdx.json
rivet import --format cyclonedx sbom/vehicle-control-v1.0.0.cdx.json
```

`rivet import --format cyclonedx` turns the SBOM into one `sbom-record` in the
rivet traceability chain, sitting alongside synth's `safety-manifest.json`
(see `crates/synth-core/src/safety_manifest.rs`) and the SLSA build provenance
+ cosign signatures from the release pipeline.

Three 2026 EU regulatory deadlines — the AI Act, the Cyber Resilience Act, and
IEC 62304 Ed.2 — require machine-readable SBOMs. CycloneDX is the format rivet
#107 standardised on for this chain.

## Out of scope

- **Full transitive dependency scanning** of the WASM module — synth is not a
  linker and does not resolve imports to concrete provider artifacts.
- **AIBOM / ML-BOM** — tracked separately as rivet #104.
- **SPDX format** — synth emits CycloneDX only.

## Follow-ups

- **Release-pipeline auto-emit.** The release workflow
  (`.github/workflows/release.yml`) does not yet pass `--sbom` when it
  exercises synth. Wiring the SBOM into a release artifact would let every
  published firmware ship its CycloneDX SBOM. Noted as a follow-up; not done
  here.
- **SPDX export.** If a downstream consumer needs SPDX rather than CycloneDX,
  an `--sbom-format spdx` option could be added. Out of scope for now.
- **Component versions for imports.** Imports are currently recorded with
  `version: "unknown"` — synth cannot know the provider's version. If the
  Component Model / WIT world supplies version metadata, it could be threaded
  through here.
