#!/usr/bin/env python3
"""parity_benchmark/run.py — reproducible wasm→synth-AOT vs native-C parity
benchmark (issue #735; refs #494 beat-LLVM, #390 size attribution, #242).

The industry claim "WebAssembly is ~40% slower than native" describes
runtime/interpreter deployments (wasm3, sandboxes, JIT warm-up). synth is an
AOT compiler: the output is bare-metal Thumb-2 machine code with no runtime,
so the only question is compilation quality — which is measurable. This
harness measures it, both directions, and regenerates the honest artifact
`artifacts/parity-benchmark.md` (--report).

Kernels (all in-tree; see artifacts/parity-benchmark.md for provenance):
  gust_poll    scripts/repro/gust_kernel.wasm      (gale mini-RTOS scheduler)
  gust_mix_q8  scripts/repro/gust_kernel.wasm      (Q8 mix wrapper)
  clamp        scripts/repro/fact_spec_clamp_494.wat  (gust_mix clamp shape)
               + native twin  scripts/repro/parity_benchmark/gust_mix_clamp.c
  flat_flight  scripts/repro/flat_flight/flat_flight.loom.wasm
               + native twin  scripts/repro/flat_flight/flat_flight.c
  falcon_axis  scripts/repro/parity_benchmark/falcon_axis.wat  (f32, VFP)
               + native twin  scripts/repro/parity_benchmark/falcon_axis.c

Every number is tagged with its provenance:
  MEASURED — produced by THIS run from the tools on THIS machine;
  CITED    — quoted from a named source (issue #390 / #494 gale measurements),
             never re-measured here;
  OPEN     — not yet measurable in-tree (cycles need gale's DWT silicon rows
             on i.MX RT1062 / STM32H743-class boards).

Requirements (stdlib-only Python; external binaries):
  * synth        — $SYNTH or target/debug/synth. The `clamp_spec` row needs a
                   verify-feature binary (`cargo build -p synth-cli --features
                   verify`): the fact-spec pass carries the ordeal solver.
  * wat2wasm     — or `wasm-tools parse` fallback ($WAT2WASM to override).
  * arm-none-eabi-gcc / arm-none-eabi-objdump — native rows + symbol sizes.
                   If gcc is absent, native rows degrade to CITED-or-absent
                   and the report says so loudly ($GCC/$OBJDUMP to override).

Usage:
    SYNTH=$CARGO_TARGET_DIR/debug/synth python3 scripts/repro/parity_benchmark/run.py
    ... run.py --only clamp_spec     # falsify one row
    ... run.py --report              # rewrite artifacts/parity-benchmark.md

Exits nonzero if any MEASURED row cannot be produced (missing function,
missing ADMIT evidence, tool failure). The synth-side byte numbers are ALSO
pinned by `crates/synth-cli/tests/parity_benchmark_735.rs` so the committed
report cannot drift from measurement without reddening CI.
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
REPORT = REPO / "artifacts" / "parity-benchmark.md"

GUST_KERNEL = REPO / "scripts/repro/gust_kernel.wasm"
CLAMP_WAT = REPO / "scripts/repro/fact_spec_clamp_494.wat"
FLAT_FLIGHT_WASM = REPO / "scripts/repro/flat_flight/flat_flight.loom.wasm"
FLAT_FLIGHT_C = REPO / "scripts/repro/flat_flight/flat_flight.c"
FLAT_FLIGHT_INC = REPO / "scripts/repro/flat_flight"
FALCON_WAT = HERE / "falcon_axis.wat"
FALCON_C = HERE / "falcon_axis.c"
CLAMP_C = HERE / "gust_mix_clamp.c"

# CITED numbers — quoted, never re-measured here. Sources are load-bearing.
CITED = {
    # issue #390 (gale, synth v0.11.50 / loom v1.1.14): native rustc/LLVM
    # thumbv7m baseline for the gust hot path. Same citation as
    # artifacts/size_attribution_390.md.
    "gust_poll_llvm": 208,
    "gust_mix_llvm": 12,
    # issue #494 (gale gust_floor_bench): LLVM floor for the clamp shape.
    "clamp_llvm_floor": 12,
}

CYCLES_OPEN = "OPEN — gale silicon (DWT)"


def env_tool(var: str, default: str) -> str:
    return os.environ.get(var, default)


def synth_bin() -> str:
    return os.environ.get("SYNTH") or str(REPO / "target" / "debug" / "synth")


def run(cmd, **kw):
    r = subprocess.run(cmd, capture_output=True, text=True, **kw)
    if r.returncode != 0:
        sys.exit(f"FAILED ({r.returncode}): {' '.join(map(str, cmd))}\n{r.stderr}")
    return r


def tool_version(cmd) -> str:
    try:
        r = subprocess.run(cmd, capture_output=True, text=True)
        return r.stdout.splitlines()[0].strip() if r.stdout else "unknown"
    except OSError:
        return "NOT INSTALLED"


# ---- wat -> wasm ----------------------------------------------------------


def wat2wasm(wat: Path, out: Path) -> None:
    tool = os.environ.get("WAT2WASM")
    if tool:
        run([tool, str(wat), "-o", str(out)])
        return
    if shutil.which("wat2wasm"):
        run(["wat2wasm", str(wat), "-o", str(out)])
    elif shutil.which("wasm-tools"):
        run(["wasm-tools", "parse", str(wat), "-o", str(out)])
    else:
        sys.exit("need wat2wasm (wabt) or wasm-tools on PATH ($WAT2WASM to override)")


# ---- schema-v1 wsc.facts encoding (docs/design/wsc-facts-encoding.md) ------
# Mirrors scripts/repro/fact_spec_clamp_494_differential.py and the Rust
# encoder in crates/synth-cli/tests/fact_spec_clamp_494.rs.


def leb_u32(v: int) -> bytes:
    out = bytearray()
    while True:
        b = v & 0x7F
        v >>= 7
        if v:
            b |= 0x80
        out.append(b)
        if not v:
            return bytes(out)


def leb_s64(v: int) -> bytes:
    out = bytearray()
    while True:
        b = v & 0x7F
        v >>= 7
        done = (v == 0 and not b & 0x40) or (v == -1 and b & 0x40)
        if not done:
            b |= 0x80
        out.append(b)
        if done:
            return bytes(out)


def with_range_fact(wasm: bytes, lo: int, hi: int) -> bytes:
    """Append one value-range fact [lo, hi] on (func 0, value_id 0)."""
    body = leb_s64(lo) + leb_s64(hi)
    payload = (
        b"\x01"  # version
        + leb_u32(1)  # count
        + b"\x01"  # kind: value-range
        + leb_u32(0)  # func_index
        + leb_u32(0)  # value_id
        + leb_u32(len(body))
        + body
    )
    name = b"wsc.facts"
    content = leb_u32(len(name)) + name + payload
    return wasm + b"\x00" + leb_u32(len(content)) + content


# ---- size measurement ------------------------------------------------------


def objdump_bin() -> str:
    return env_tool("OBJDUMP", "arm-none-eabi-objdump")


def func_sizes(elf: Path) -> dict:
    """{name: size} for .text functions, derived from sorted symbol-address
    deltas (next symbol / section end) — the same symtab method as
    scripts/repro/size_attribution_390.py and the Rust size oracles
    (st_size is not relied upon for synth-produced ELFs)."""
    r = run([objdump_bin(), "-t", str(elf)])
    syms = []
    for line in r.stdout.splitlines():
        m = re.match(r"([0-9a-f]+)\s.*\sF\s+\.text\s+[0-9a-f]+\s+(\S+)", line)
        if m:
            syms.append((int(m.group(1), 16), m.group(2)))
    rh = run([objdump_bin(), "-h", str(elf)])
    end = None
    for line in rh.stdout.splitlines():
        m = re.match(r"\s*\d+\s+\.text\s+([0-9a-f]+)\s+([0-9a-f]+)", line)
        if m:
            end = int(m.group(2), 16) + int(m.group(1), 16)
    syms.sort()
    out = {}
    for i, (addr, name) in enumerate(syms):
        nxt = syms[i + 1][0] if i + 1 < len(syms) else end
        out[name] = nxt - addr
    return out


def synth_compile(wasm: Path, out: Path, target: str, fact_spec: bool = False) -> str:
    env = dict(os.environ)
    env.pop("SYNTH_FACT_SPEC", None)
    if fact_spec:
        env["SYNTH_FACT_SPEC"] = "1"
    cmd = [
        synth_bin(), "compile", str(wasm),
        "-o", str(out), "-b", "arm", "--target", target, "--all-exports",
    ]
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        sys.exit(f"synth compile failed for {wasm.name}:\n{r.stderr}")
    return r.stderr


def gcc_bin():
    tool = env_tool("GCC", "arm-none-eabi-gcc")
    return tool if shutil.which(tool) else None


def gcc_fn_size(cfile: Path, out: Path, name: str, extra_flags=()) -> int:
    """Compile one C file at -Os for cortex-m4 and return the named function's
    st_size from the object symtab (reliable for GNU-as output)."""
    flags = ["-Os", "-mcpu=cortex-m4", "-mthumb", "-Wno-attributes"]
    flags += list(extra_flags)
    run([gcc_bin(), *flags, "-c", str(cfile), "-o", str(out)])
    r = run([objdump_bin(), "-t", str(out)])
    for line in r.stdout.splitlines():
        m = re.match(r"[0-9a-f]+\s.*\sF\s+\.text\s+([0-9a-f]+)\s+(\S+)", line)
        if m and m.group(2) == name:
            return int(m.group(1), 16)
    sys.exit(f"function {name} not found in {out}")


HARD_FLOAT = ("-mfloat-abi=hard", "-mfpu=fpv4-sp-d16")


# ---- rows -------------------------------------------------------------------


def measure(tmp: Path, only=None) -> dict:
    """Measure everything (or one --only group); return {key: value|None}."""
    want = lambda k: only is None or only == k  # noqa: E731
    m = {}

    if want("gust_poll") or want("gust_mix_q8"):
        elf = tmp / "gust.o"
        synth_compile(GUST_KERNEL, elf, "cortex-m4")
        sizes = func_sizes(elf)
        m["gust_poll_synth"] = sizes["gust_poll"]
        m["gust_mix_q8_synth"] = sizes["gust_mix"]

    if want("clamp") or want("clamp_spec"):
        base = tmp / "clamp_base.wasm"
        wat2wasm(CLAMP_WAT, base)
        if want("clamp"):
            elf = tmp / "clamp_base.o"
            synth_compile(base, elf, "cortex-m4")
            m["clamp_synth_default"] = func_sizes(elf)["gust_mix"]
            if gcc_bin():
                m["clamp_gcc"] = gcc_fn_size(CLAMP_C, tmp / "clamp_gcc.o", "gust_mix")
        if want("clamp_spec"):
            facts = tmp / "clamp_facts.wasm"
            facts.write_bytes(with_range_fact(base.read_bytes(), 524, 1524))
            elf = tmp / "clamp_spec.o"
            stderr = synth_compile(facts, elf, "cortex-m4", fact_spec=True)
            admits = stderr.count("fact-spec: ADMIT")
            if admits != 2:
                sys.exit(
                    f"clamp_spec: expected 2 certificate ADMITs, got {admits}.\n"
                    "The fact-spec pass needs the ordeal solver — build synth "
                    "with `cargo build -p synth-cli --features verify` and "
                    "point $SYNTH at it.\n--- synth stderr ---\n" + stderr
                )
            m["clamp_spec_synth"] = func_sizes(elf)["gust_mix"]
            m["clamp_spec_admits"] = admits

    if want("flat_flight"):
        elf = tmp / "ff_synth.o"
        synth_compile(FLAT_FLIGHT_WASM, elf, "cortex-m4")
        m["flat_flight_synth"] = func_sizes(elf)["flat_flight"]
        if gcc_bin():
            m["flat_flight_gcc"] = gcc_fn_size(
                FLAT_FLIGHT_C, tmp / "ff_gcc.o", "flat_flight",
                extra_flags=(f"-I{FLAT_FLIGHT_INC}",),
            )

    if want("falcon_axis"):
        wasm = tmp / "falcon_axis.wasm"
        wat2wasm(FALCON_WAT, wasm)
        elf = tmp / "falcon_synth.o"
        synth_compile(wasm, elf, "cortex-m4f")  # VFP needs the hard-FPU target
        m["falcon_synth"] = func_sizes(elf)["falcon_axis"]
        if gcc_bin():
            m["falcon_gcc"] = gcc_fn_size(
                FALCON_C, tmp / "falcon_gcc.o", "falcon_axis",
                extra_flags=HARD_FLOAT,
            )
            m["falcon_gcc_nocontract"] = gcc_fn_size(
                FALCON_C, tmp / "falcon_gcc_nc.o", "falcon_axis",
                extra_flags=HARD_FLOAT + ("-ffp-contract=off",),
            )
    return m


def ratio(a, b):
    return f"{a / b:.2f}x" if (a is not None and b) else "—"


def table_lines(m: dict) -> list:
    """[(kernel, path, bytes, provenance, vs_ref, cycles)] for every row we
    have a value for. `vs ref` = this row's bytes / the kernel's native
    reference bytes (the reference row itself shows `ref`)."""
    L = []
    gcc_missing = gcc_bin() is None

    def native(kernel, key_meas, cited_key=None, cited_src=""):
        """Emit the native reference row; return its byte value (or None)."""
        if key_meas and m.get(key_meas) is not None:
            L.append((kernel, "native C — arm-none-eabi-gcc -Os", m[key_meas],
                      "MEASURED", "ref", CYCLES_OPEN))
            return m[key_meas]
        if cited_key:
            L.append((kernel, "native rustc/LLVM thumbv7m", CITED[cited_key],
                      f"CITED {cited_src}", "ref", CYCLES_OPEN))
            return CITED[cited_key]
        if gcc_missing:
            L.append((kernel, "native C — arm-none-eabi-gcc -Os", None,
                      "UNMEASURED (gcc not installed)", "—", CYCLES_OPEN))
        return None

    if "gust_poll_synth" in m:
        ref = CITED["gust_poll_llvm"]
        L.append(("gust_poll", "synth AOT (default)", m["gust_poll_synth"],
                  "MEASURED", ratio(m["gust_poll_synth"], ref), CYCLES_OPEN))
        native("gust_poll", None, "gust_poll_llvm", "#390")
    if "gust_mix_q8_synth" in m:
        ref = CITED["gust_mix_llvm"]
        L.append(("gust_mix (Q8 wrapper)", "synth AOT (default)",
                  m["gust_mix_q8_synth"], "MEASURED",
                  ratio(m["gust_mix_q8_synth"], ref), CYCLES_OPEN))
        native("gust_mix (Q8 wrapper)", None, "gust_mix_llvm", "#390")
    if "clamp_synth_default" in m or "clamp_spec_synth" in m:
        ref = m.get("clamp_gcc")
        if "clamp_synth_default" in m:
            L.append(("gust_mix clamp", "synth AOT (default, no facts)",
                      m["clamp_synth_default"], "MEASURED",
                      ratio(m["clamp_synth_default"], ref), CYCLES_OPEN))
        if "clamp_spec_synth" in m:
            L.append(("gust_mix clamp",
                      "synth AOT + SYNTH_FACT_SPEC=1 (proven ch∈[524,1524])",
                      m["clamp_spec_synth"], "MEASURED (2 ordeal ADMITs)",
                      ratio(m["clamp_spec_synth"], ref), CYCLES_OPEN))
        ref = native("gust_mix clamp", "clamp_gcc")
        L.append(("gust_mix clamp", "native LLVM floor (gale gust_floor_bench)",
                  CITED["clamp_llvm_floor"], "CITED #494",
                  ratio(CITED["clamp_llvm_floor"], ref), CYCLES_OPEN))
    if "flat_flight_synth" in m:
        ref = m.get("flat_flight_gcc")
        L.append(("flat_flight", "synth AOT (default)", m["flat_flight_synth"],
                  "MEASURED", ratio(m["flat_flight_synth"], ref), CYCLES_OPEN))
        native("flat_flight", "flat_flight_gcc")
    if "falcon_synth" in m:
        ref = m.get("falcon_gcc")
        L.append(("falcon_axis (f32)", "synth AOT (cortex-m4f, VFP)",
                  m["falcon_synth"], "MEASURED",
                  ratio(m["falcon_synth"], ref), CYCLES_OPEN))
        native("falcon_axis (f32)", "falcon_gcc")
    return L


def print_table(m: dict) -> None:
    print(f"{'kernel':<22} {'path':<52} {'.text B':>8}  {'provenance':<28} "
          f"{'vs ref':<8} cycles")
    for k, p, b, prov, r, c in table_lines(m):
        print(f"{k:<22} {p:<52} {b if b is not None else '—':>8}  "
              f"{prov:<28} {r:<8} {c}")
    if "falcon_gcc_nocontract" in m:
        print(f"\n  (falcon_axis gcc -ffp-contract=off: "
              f"{m['falcon_gcc_nocontract']} B — same size; vmla instead of "
              f"vfma, still a contraction wasm semantics forbid)")


# ---- report -----------------------------------------------------------------


def toolchain_block() -> str:
    gcc = gcc_bin()
    return "\n".join([
        f"- **synth**: `{tool_version([synth_bin(), '--version'])}` "
        "(debug build, `--features verify` — the fact-spec row needs the "
        "ordeal solver)",
        f"- **arm-none-eabi-gcc**: `{tool_version([gcc, '--version']) if gcc else 'NOT INSTALLED — native C rows unmeasured'}`",
        f"- **arm-none-eabi-objdump**: `{tool_version([objdump_bin(), '--version'])}`",
        f"- **wat2wasm**: `{tool_version(['wat2wasm', '--version']) if shutil.which('wat2wasm') else 'absent (wasm-tools fallback)'}`",
    ])


def report(m: dict) -> str:
    rows = table_lines(m)
    tbl = ["| kernel | path | .text B | provenance | vs native ref | cycles |",
           "|---|---|---|---|---|---|"]
    for k, p, b, prov, r, c in rows:
        tbl.append(f"| {k} | {p} | {b if b is not None else '—'} | {prov} | {r} | {c} |")
    nc = m.get("falcon_gcc_nocontract")
    clamp_gcc = m.get("clamp_gcc")
    ff_gcc = m.get("flat_flight_gcc")
    falcon_gcc = m.get("falcon_gcc")
    return f"""<!-- GENERATED by scripts/repro/parity_benchmark/run.py --report — do not hand-edit -->
# wasm→synth-AOT vs native-C parity benchmark (#735)

**The claim under test.** "WebAssembly is ~40% slower than native" describes
*runtime/interpreter* deployments (wasm3, interpreted sandboxes, JIT warm-up).
synth's model is different: **AOT wasm→bare-metal Thumb-2 with no runtime** —
the output is native machine code for i.MX RT1062 / STM32H743-class parts, and
the only remaining question is compilation quality. That is measurable, so we
measure it — both directions, wins and open gaps.

Regenerate everything on this page:

    SYNTH=$CARGO_TARGET_DIR/debug/synth python3 scripts/repro/parity_benchmark/run.py --report

## Honest headline

- **On the certified-elision clamp shape, AOT-wasm is SMALLER than measured
  native today**: gust_mix clamp **{m.get('clamp_spec_synth', '—')} B** (synth
  `SYNTH_FACT_SPEC=1`, both clamp branches elided under the loom-proven
  premise ch∈[524,1524], each elision ordeal-certified UNSAT) vs
  **{clamp_gcc if clamp_gcc is not None else '—'} B** measured
  `arm-none-eabi-gcc -Os`, and within 2 B of the **12 B LLVM floor** (CITED
  #494). C has no channel to carry the range premise — the native compiler
  must keep both compares; synth carries the proof (#494).
- **General register allocation is still the gap**: gust_poll is
  **{m.get('gust_poll_synth', '—')} B vs 208 B** (CITED #390) = 3.56×, with
  `spill_reload` alone ~31% of the function
  (`artifacts/size_attribution_390.md` — the productive-work residual, 194 B,
  is already comparable to LLVM's entire output; the gap is overhead buckets).
- **Everything is bit-exact**: semantics are differentially gated vs wasmtime
  across the CI suite (incl. the full f32 set) — the size/cycle race is run
  under a correctness gate, not instead of one.
- **Cycles are OPEN**: every cycles cell is gale's DWT silicon row
  (i.MX RT1062 / STM32H743-class). No cycle number appears here until it is
  measured on hardware; the #494 kill-criterion (<1.0× then ≤0.70×) stays open
  with them.

## Pinned toolchain (versions that produced the MEASURED numbers)

{toolchain_block()}

## Method

- **synth side**: `synth compile <kernel> -b arm --target cortex-m4
  --all-exports` (default shipped path, no `--relocatable`; `cortex-m4f` for
  the VFP kernel). Per-function `.text` bytes = sorted symbol-address deltas
  from the ELF symtab (same method as `size_attribution_390.py` and the Rust
  size oracles; `st_size` not relied upon).
- **native side**: the C twin of each kernel at `arm-none-eabi-gcc -Os
  -mcpu=cortex-m4 -mthumb` (+ `-mfloat-abi=hard -mfpu=fpv4-sp-d16` for f32);
  function size from the object symtab.
- **provenance**: MEASURED = produced by this run; CITED = quoted from the
  named issue (gale's rustc/LLVM numbers — no in-tree LLVM baseline);
  OPEN = needs silicon.
- **fairness notes, both directions**: (1) GCC contracts `a*b+c` to
  `vfma`/`vmla` on falcon_axis{f" ({falcon_gcc} B with contraction, {nc} B with -ffp-contract=off — same size, vmla still chains)" if nc is not None else ""} —
  a transformation wasm semantics forbid (no fma op), so synth must keep the
  intermediate rounding to stay bit-exact vs wasmtime: the native baseline
  plays with rules wasm-AOT cannot use. (2) Conversely the fact-spec row uses
  a premise C cannot express — that asymmetry (proof-carrying specialization)
  is synth's structural advantage, and it is gated: wrong premise ⇒ Sat ⇒
  loud DECLINE, byte-identical output (`fact_spec_clamp_494.rs`).
- **cycles**: qemu icount is only wired for the RV32 flat_flight harness
  (`scripts/repro/flat_flight/harness/`, a proxy at best); Cortex-M cycle rows
  wait for gale's DWT measurements rather than shipping a proxy as a headline.

## The table

{chr(10).join(tbl)}

Synth-side byte numbers are pinned by
`crates/synth-cli/tests/parity_benchmark_735.rs` (default rows) and its
verify-feature test (fact-spec row) — prose and measurement cannot drift
apart without reddening CI.

## Falsification — one command per row group

Each command re-measures the row from source on your machine and prints the
table line (nonzero exit on any failure):

    # gust_poll (740 B) and gust_mix Q8 wrapper (32 B)
    SYNTH=$CARGO_TARGET_DIR/debug/synth python3 scripts/repro/parity_benchmark/run.py --only gust_poll
    SYNTH=$CARGO_TARGET_DIR/debug/synth python3 scripts/repro/parity_benchmark/run.py --only gust_mix_q8

    # gust_mix clamp: synth default + gcc twin + LLVM floor citation
    SYNTH=$CARGO_TARGET_DIR/debug/synth python3 scripts/repro/parity_benchmark/run.py --only clamp

    # gust_mix clamp under the proven premise (needs a verify-feature synth;
    # fails loudly unless BOTH elisions are certificate-ADMITted)
    SYNTH=$CARGO_TARGET_DIR/debug/synth python3 scripts/repro/parity_benchmark/run.py --only clamp_spec

    # flat_flight: synth vs the in-tree C source it was compiled from
    SYNTH=$CARGO_TARGET_DIR/debug/synth python3 scripts/repro/parity_benchmark/run.py --only flat_flight

    # falcon_axis f32: synth (cortex-m4f) vs gcc hard-float twin
    SYNTH=$CARGO_TARGET_DIR/debug/synth python3 scripts/repro/parity_benchmark/run.py --only falcon_axis

    # the CI pin (byte numbers cannot drift from this document)
    cargo test -p synth-cli --test parity_benchmark_735
    cargo test -p synth-cli --features verify --test parity_benchmark_735

The CITED rows are falsified at their source: #390 / #494 carry gale's build
recipes for the rustc/LLVM baselines.

## Trend per release (the direction of the gap)

The gap is CLOSING release-over-release, lever by lever, each evidence-gated:

| datum | then | now (this page) | source |
|---|---|---|---|
| gust_poll .text | 816 B (v0.11.50, CITED #390) | {m.get('gust_poll_synth', '—')} B MEASURED | levers v0.12–v0.41 |
| gust_mix (Q8) .text | 44 B (v0.11.50, CITED #390) | {m.get('gust_mix_q8_synth', '—')} B MEASURED | uxth-fold, const-CSE, shift-mask-elide |
| gust_mix clamp (proven premise) | no lever | {m.get('clamp_spec_synth', '—')} B MEASURED vs 12 B LLVM floor | #494 fact-spec (v0.31+) |
| flat_flight frame traffic | 17 spills (#209, CITED) | Belady optimum, frame traffic 0 (since v0.24.0) | VCR-RA-001 |

Open, tracked, and honestly not yet won: general regalloc overhead
(gust_poll 3.56×, spill_reload ~31%, #390/#242 Track A), flat_flight at
{ratio(m.get('flat_flight_synth'), ff_gcc)} vs gcc, falcon f32 at
{ratio(m.get('falcon_synth'), falcon_gcc)} vs gcc (constant materialization
via `movw/movt+vmov` instead of a literal pool, unused callee-save push), and
every cycles cell.

Refs: #735 (this benchmark), #494 (beat-LLVM / fact-spec), #390 (size
attribution), #209 (perf epic), #242 (North Star).
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--only", choices=[
        "gust_poll", "gust_mix_q8", "clamp", "clamp_spec",
        "flat_flight", "falcon_axis",
    ], help="re-measure a single row group (falsification mode)")
    ap.add_argument("--report", action="store_true",
                    help=f"rewrite {REPORT.relative_to(REPO)}")
    args = ap.parse_args()

    if not Path(synth_bin()).exists():
        sys.exit(f"synth binary not found: {synth_bin()} (set $SYNTH)")
    if gcc_bin() is None:
        print("WARNING: arm-none-eabi-gcc not installed — native C rows will "
              "be UNMEASURED (CITED LLVM numbers shown where they exist)",
              file=sys.stderr)

    with tempfile.TemporaryDirectory(prefix="parity_735_") as td:
        m = measure(Path(td), only=args.only)
    print_table(m)
    if args.report:
        if args.only:
            sys.exit("--report needs the full measurement (drop --only)")
        REPORT.write_text(report(m))
        print(f"\nwrote {REPORT}")


if __name__ == "__main__":
    main()
