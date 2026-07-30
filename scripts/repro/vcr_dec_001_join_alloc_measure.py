#!/usr/bin/env python3
"""VCR-DEC-001 increment 2 — MEASURE the join-aware graph-colouring allocator
against the shipping greedy/segment allocator (epic #242, the North Star).

This is the lane's DELIVERABLE, not a gate: a widened allocator with no
comparative numbers says nothing about whether to flip it. For every function
in the ARM repro corpus it reports, per function and in total:

  * `.text` bytes with `SYNTH_GRAPH_ALLOC` OFF (the shipping greedy allocator +
    the verified segment re-allocation) vs ON (whole-function colouring across
    joins), read from the ELF SYMTAB — never from `synth disasm` text, which is
    host-toolchain dependent;
  * the SOUND static worst-case cycle bound from `--emit-wcet`
    (`synth-wcet-v1`), which is synth's own documented Cortex-M3/M4 per-op
    model — so "cycles" here is a bound comparison on identical modelling
    assumptions, not a hardware measurement. Functions whose bound DECLINES on
    either side are excluded from the cycle total and counted separately.

Both `--relocatable` (label-form branches — increment 2's scope) and the
default self-contained path (pre-resolved NUMERIC branches — out of scope, so
the allocator declines and the numbers must be flat) are measured, because the
flat half is itself evidence: it bounds how much of the corpus the increment
can reach today.

Usage:  python3 vcr_dec_001_join_alloc_measure.py <synth-binary> [--json OUT]
Exit 0 always unless a compile fails — this MEASURES, it does not judge.
"""
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

REPRO = Path(__file__).resolve().parent

# Flags cleared so an ambient env var cannot skew a measurement.
CLEAR = [
    "SYNTH_NO_CMP_SELECT_FUSE", "SYNTH_NO_LOCAL_PROMOTE", "SYNTH_NO_IMM_SHIFT_FOLD",
    "SYNTH_NO_STACK_FWD", "SYNTH_SPILL_REALLOC", "SYNTH_CONST_CSE", "SYNTH_BASE_CSE",
    "SYNTH_DEAD_FRAME_ELIM", "SYNTH_UXTH_FOLD", "SYNTH_GRAPH_ALLOC",
    "SYNTH_SHIFT_MASK_ELIDE", "SYNTH_RANGE_REALLOC", "SYNTH_FACT_SPEC",
]


def corpus():
    """Every ARM-compilable repro fixture, sorted for a deterministic report."""
    return sorted(
        [p for p in REPRO.glob("*.wat")] + [p for p in REPRO.glob("*.wasm")],
        key=lambda p: p.name,
    )


def compile_one(synth, src, outdir, relocatable, graph_alloc):
    env = {k: v for k, v in os.environ.items()}
    for k in CLEAR:
        env.pop(k, None)
    if graph_alloc:
        env["SYNTH_GRAPH_ALLOC"] = "1"
        env["SYNTH_GRAPH_ALLOC_STATS"] = "1"
    elf = Path(outdir) / (src.stem + ".elf")
    cmd = [synth, "compile", str(src), "-o", str(elf),
           "-b", "arm", "--target", "cortex-m4", "--all-exports", "--emit-wcet"]
    if relocatable:
        cmd.append("--relocatable")
    r = subprocess.run(cmd, capture_output=True, env=env)
    return r, elf


def func_sizes(elf):
    """{name: size} for every STT_FUNC in the SYMTAB (never `synth disasm`
    text, which is host-toolchain dependent — the #850 lesson). synth's
    relocatable object leaves the symtab section NAME empty, so the section is
    found by TYPE. Each function carries both a `func_N` symbol and its export
    alias at the same address; the aliases are collapsed onto the export name so
    a function is not counted twice."""
    from elftools.elf.elffile import ELFFile
    from elftools.elf.sections import SymbolTableSection
    by_addr = {}
    with open(elf, "rb") as fh:
        ef = ELFFile(fh)
        for sec in ef.iter_sections():
            if not isinstance(sec, SymbolTableSection):
                continue
            for sym in sec.iter_symbols():
                if sym["st_info"]["type"] != "STT_FUNC" or not sym["st_size"]:
                    continue
                key = (sym["st_value"], sym["st_size"])
                prev = by_addr.get(key)
                # Prefer the human-readable export alias over `func_N`.
                if prev is None or (prev.startswith("func_") and
                                    not sym.name.startswith("func_")):
                    by_addr[key] = sym.name
    return {name: key[1] for key, name in by_addr.items()}


def wcet_bounds(elf):
    """{name: cycles} from the synth-wcet-v1 sidecar; declines are omitted (a
    DECLINE is a refusal to bound, not a zero)."""
    side = Path(str(elf) + ".wcet.json")
    if not side.exists():
        return {}, set()
    try:
        doc = json.loads(side.read_text())
    except json.JSONDecodeError:
        return {}, set()
    bounds, declined = {}, set()
    for fn in doc.get("functions", []):
        name = fn.get("name") or fn.get("function") or ""
        cyc = fn.get("cycles")
        if fn.get("status") != "bounded" or cyc is None:
            declined.add(name)
        else:
            bounds[name] = cyc
    return bounds, declined


def measure(synth, relocatable):
    rows, errors = [], []
    applied_total = 0
    declines = {}
    with tempfile.TemporaryDirectory() as td_off, tempfile.TemporaryDirectory() as td_on:
        for src in corpus():
            r_off, elf_off = compile_one(synth, src, td_off, relocatable, False)
            r_on, elf_on = compile_one(synth, src, td_on, relocatable, True)
            if r_off.returncode != 0 or r_on.returncode != 0:
                # Not every fixture targets ARM/cortex-m4; a fixture that does
                # not compile on BOTH sides is simply out of the population.
                if r_off.returncode != r_on.returncode:
                    errors.append(f"{src.name}: asymmetric compile "
                                  f"(off={r_off.returncode} on={r_on.returncode})")
                continue
            stderr_on = r_on.stderr.decode(errors="replace")
            applied_total += stderr_on.count("whole-function colouring APPLIED")
            for line in stderr_on.splitlines():
                if "join colouring DECLINED:" in line:
                    reason = line.rsplit(":", 1)[1].strip()
                    declines[reason] = declines.get(reason, 0) + 1
            s_off, s_on = func_sizes(elf_off), func_sizes(elf_on)
            w_off, d_off = wcet_bounds(elf_off)
            w_on, d_on = wcet_bounds(elf_on)
            for name in sorted(set(s_off) & set(s_on)):
                cyc_off = w_off.get(name)
                cyc_on = w_on.get(name)
                rows.append({
                    "fixture": src.name,
                    "func": name,
                    "bytes_off": s_off[name],
                    "bytes_on": s_on[name],
                    "cycles_off": cyc_off,
                    "cycles_on": cyc_on,
                })
    return rows, applied_total, declines, errors


def report(tag, rows, applied, declines, errors):
    changed = [r for r in rows if r["bytes_off"] != r["bytes_on"]]
    b_off = sum(r["bytes_off"] for r in rows)
    b_on = sum(r["bytes_on"] for r in rows)
    cyc = [r for r in rows if r["cycles_off"] is not None and r["cycles_on"] is not None]
    c_off = sum(r["cycles_off"] for r in cyc)
    c_on = sum(r["cycles_on"] for r in cyc)
    grew = [r for r in rows if r["bytes_on"] > r["bytes_off"]]
    shrank = [r for r in rows if r["bytes_on"] < r["bytes_off"]]
    cyc_grew = [r for r in cyc if r["cycles_on"] > r["cycles_off"]]
    cyc_shrank = [r for r in cyc if r["cycles_on"] < r["cycles_off"]]

    print(f"\n===== {tag} =====")
    print(f"functions measured        : {len(rows)}")
    print(f"graph-alloc APPLIED (fn)  : {applied}")
    print(f"bytes  off={b_off}  on={b_on}  delta={b_on - b_off:+d} "
          f"({100.0 * (b_on - b_off) / b_off:+.2f}%)" if b_off else "bytes: n/a")
    if cyc:
        print(f"wcet   off={c_off}  on={c_on}  delta={c_on - c_off:+d} "
              f"({100.0 * (c_on - c_off) / c_off:+.2f}%)  "
              f"[{len(cyc)}/{len(rows)} functions have a bound on both sides]")
    else:
        print("wcet   : no function has a sound bound on both sides")
    print(f"bytes  : {len(shrank)} shrank, {len(grew)} grew, "
          f"{len(rows) - len(changed)} unchanged")
    print(f"cycles : {len(cyc_shrank)} shrank, {len(cyc_grew)} grew")
    if declines:
        print("decline reasons (flag-on):")
        for k, v in sorted(declines.items(), key=lambda kv: -kv[1]):
            print(f"    {k:<26} {v}")
    if changed:
        print("per-function changes:")
        for r in sorted(changed, key=lambda r: r["bytes_on"] - r["bytes_off"]):
            dc = ""
            if r["cycles_off"] is not None and r["cycles_on"] is not None:
                dc = f"  cyc {r['cycles_off']}->{r['cycles_on']} " \
                     f"({r['cycles_on'] - r['cycles_off']:+d})"
            print(f"    {r['fixture']:<34} {r['func']:<24} "
                  f"{r['bytes_off']:>4} -> {r['bytes_on']:>4} "
                  f"({r['bytes_on'] - r['bytes_off']:+d}){dc}")
    for e in errors:
        print(f"  ERROR {e}")
    return {"functions": len(rows), "applied": applied,
            "bytes_off": b_off, "bytes_on": b_on,
            "cycles_off": c_off, "cycles_on": c_on,
            "cycle_functions": len(cyc),
            "shrank": len(shrank), "grew": len(grew),
            "cyc_shrank": len(cyc_shrank), "cyc_grew": len(cyc_grew),
            "declines": declines, "rows": rows}


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    synth = sys.argv[1]
    out_json = None
    if "--json" in sys.argv:
        out_json = sys.argv[sys.argv.index("--json") + 1]

    summary = {}
    for tag, reloc in (("relocatable / label-form branches (increment-2 scope)", True),
                       ("self-contained / pre-resolved numeric branches (out of scope)", False)):
        rows, applied, declines, errors = measure(synth, reloc)
        summary["relocatable" if reloc else "self_contained"] = report(
            tag, rows, applied, declines, errors)
    if out_json:
        Path(out_json).write_text(json.dumps(summary, indent=2))
        print(f"\nwrote {out_json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
