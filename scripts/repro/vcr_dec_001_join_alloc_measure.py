#!/usr/bin/env python3
# ci-status: manual (measurement) — the #242 join-allocator COMPARISON deliverable (bytes and --emit-wcet bounds, graph-alloc ON vs OFF) whose whole point is a number to judge a flip by; it deliberately has no verdict. The allocator's correctness is gated by the wired VCR-DEC-001 differential jobs.
"""VCR-DEC-001 increments 2+3 — MEASURE the join- and call-aware graph-colouring
allocator against the shipping greedy/segment allocator (epic #242, the North
Star).

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

Both paths are measured, because the DIFFERENCE between them bounds how much of
the corpus each increment reaches:
  * `--relocatable` — label-form branches, fully in scope;
  * the default self-contained path — branches are PRE-RESOLVED to numeric
    offsets, which the allocator still declines (`numeric-branch`), so only its
    call-form and branch-free functions are reachable there. Increment 3 moved
    this half from "mostly flat" to real: calls stay label-form on BOTH paths,
    so modeling them reaches functions the numeric-branch decline had hidden.

The per-run DECLINE HISTOGRAM is the actionable half of the output: each reason
names a construct the allocator refuses, and the largest bucket is the next
increment's target (that is how increment 3 was chosen — `call` + `call-indirect`
were 68 of increment 2's declines).

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
    "SYNTH_DEAD_FRAME_ELIM", "SYNTH_UXTH_FOLD", "SYNTH_GRAPH_ALLOC", "SYNTH_GRAPH_ALLOC_FORCE",
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


def insn_metrics(elf):
    """RQ-59-MEASURE: per-function INSTRUCTION metrics — count, wide (32-bit)
    encodings, and FRAME TRAFFIC (loads/stores whose base is SP — the direct
    path's frame addressing) — because bytes and instruction count can move in OPPOSITE
    directions: the colourer's rewrites can turn a narrow 16-bit op into a wide
    32-bit one (e.g. an SP-relative `ldr` of a high register must be `ldr.w`),
    so a verdict quoting only one of the two would be misleading.

    Optional: requires capstone; returns {} when it is not installed (the
    byte/wcet halves of this report do not depend on it). Same-host, same-pass
    on BOTH sides, so the host-dependence caveat that rules out `synth disasm`
    text differentials does not arise."""
    try:
        import capstone
    except ImportError:
        return {}
    from elftools.elf.elffile import ELFFile
    from elftools.elf.sections import SymbolTableSection
    md = capstone.Cs(capstone.CS_ARCH_ARM,
                     capstone.CS_MODE_THUMB | capstone.CS_MODE_MCLASS)
    md.detail = True
    md.skipdata = True  # literal pools inside a symbol's span must not truncate
    out = {}
    with open(elf, "rb") as fh:
        ef = ELFFile(fh)
        secs = list(ef.iter_sections())
        funcs = {}
        for sec in secs:
            if not isinstance(sec, SymbolTableSection):
                continue
            for sym in sec.iter_symbols():
                if sym["st_info"]["type"] != "STT_FUNC" or not sym["st_size"]:
                    continue
                # st_shndx pins the DEFINING section: in an ET_REL object every
                # section has sh_addr == 0, so a spanning-address search alone
                # would silently disassemble the first section that fits.
                key = (sym["st_value"], sym["st_size"], sym["st_shndx"])
                prev = funcs.get(key)
                if prev is None or (prev.startswith("func_") and
                                    not sym.name.startswith("func_")):
                    funcs[key] = sym.name
        for (vaddr, size, shndx), name in funcs.items():
            addr = vaddr & ~1  # strip the Thumb bit
            if not isinstance(shndx, int):
                continue
            sec = secs[shndx]
            base = sec["sh_addr"]
            if (sec["sh_type"] == "SHT_NOBITS"
                    or not (sec["sh_flags"] & 0x4)  # SHF_EXECINSTR
                    or addr < base or addr + size > base + sec["sh_size"]):
                continue
            body = sec.data()[addr - base: addr - base + size]
            m = {"insns": 0, "wide": 0, "frame_ld": 0, "frame_st": 0,
                 "wide_frame": 0, "pushpop_regs": 0, "sp_sub": 0}
            for ins in md.disasm(body, addr):
                if ins.mnemonic == ".byte":  # skipdata placeholder (literal pool)
                    continue
                m["insns"] += 1
                if ins.size == 4:
                    m["wide"] += 1
                mn = ins.mnemonic
                if mn.startswith(("push", "pop")):
                    m["pushpop_regs"] += len(ins.operands)
                if mn.startswith("sub") and ins.op_str.startswith("sp,"):
                    ops = ins.operands
                    if ops and ops[-1].type == capstone.arm.ARM_OP_IMM:
                        m["sp_sub"] += ops[-1].imm
                is_ld = mn.startswith(("ldr", "ldm", "ldrd"))
                is_st = mn.startswith(("str", "stm", "strd"))
                if is_ld or is_st:
                    for op in ins.operands:
                        if op.type != capstone.arm.ARM_OP_MEM:
                            continue
                        # The direct path's frame is SP-relative
                        # (`ldr rd,[sp,#off]`, select_with_stack). R11/R9/R10
                        # are the linmem/globals/memsize bases and R7 is
                        # allocatable, so ONLY an SP base is frame traffic.
                        base_reg = ins.reg_name(op.mem.base) or ""
                        if base_reg == "sp":
                            m["frame_ld" if is_ld else "frame_st"] += 1
                            if ins.size == 4:
                                m["wide_frame"] += 1
            out[name] = m
    return out


def parse_set(listing):
    """`Op xN, Op xN` → {op: n} (the complete-set diagnostic line format)."""
    out = {}
    for part in listing.split(", "):
        if part:
            name, _, n = part.rpartition(" x")
            out[name] = out.get(name, 0) + int(n)
    return out


def measure(synth, relocatable):
    rows, errors = [], []
    applied_total = 0
    declines = {}
    # RQ-59-REACH: the census must never report FIRST blockers only (the #936
    # `scan_for_decline` trap). The pass emits COMPLETE-set diagnostics; this
    # pairs each set line with the decline that follows it:
    #   unmodeled_sets  — per declined function, EVERY op no effect fn models;
    #   inc1_subs       — why increment 1 refused a `single-block` function;
    #   refused_sets    — per apply-colouring decline, EVERY op `rewrite_op`
    #                     refused, annotated rmw-colour-mismatch/no-rewrite-arm.
    unmodeled_sets, inc1_subs, refused_sets = [], {}, []
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
            pending_unmodeled = pending_refused = pending_sub = None
            for line in stderr_on.splitlines():
                if "unmodeled-op complete blocker set:" in line:
                    pending_unmodeled = parse_set(line.split("set:", 1)[1].strip())
                elif "rewrite-refused complete set:" in line:
                    pending_refused = parse_set(line.split("set:", 1)[1].strip())
                elif "increment-1 declined:" in line:
                    pending_sub = line.split("declined:", 1)[1].strip()
                elif "join colouring DECLINED:" in line:
                    reason = line.rsplit(":", 1)[1].strip()
                    declines[reason] = declines.get(reason, 0) + 1
                    if reason == "unmodeled-op" and pending_unmodeled:
                        unmodeled_sets.append(pending_unmodeled)
                    if reason == "single-block" and pending_sub:
                        inc1_subs[pending_sub] = inc1_subs.get(pending_sub, 0) + 1
                        if pending_sub == "apply-colouring" and pending_refused:
                            refused_sets.append(pending_refused)
                    pending_unmodeled = pending_refused = pending_sub = None
            s_off, s_on = func_sizes(elf_off), func_sizes(elf_on)
            w_off, d_off = wcet_bounds(elf_off)
            w_on, d_on = wcet_bounds(elf_on)
            m_off, m_on = insn_metrics(elf_off), insn_metrics(elf_on)
            for name in sorted(set(s_off) & set(s_on)):
                cyc_off = w_off.get(name)
                cyc_on = w_on.get(name)
                row = {
                    "fixture": src.name,
                    "func": name,
                    "bytes_off": s_off[name],
                    "bytes_on": s_on[name],
                    "cycles_off": cyc_off,
                    "cycles_on": cyc_on,
                }
                if name in m_off and name in m_on:
                    row["insn_off"] = m_off[name]
                    row["insn_on"] = m_on[name]
                rows.append(row)
    census = {"unmodeled_sets": unmodeled_sets, "inc1_subs": inc1_subs,
              "refused_sets": refused_sets}
    return rows, applied_total, declines, errors, census


def census_report(census):
    """The RQ-59-REACH separation: identity-colouring is a SUCCESS (a validated
    identity rewrite), so the report prints reach failures apart from it, and
    every blocker aggregation is over COMPLETE per-function sets."""
    def agg(sets):
        by_fn, by_occ = {}, {}
        for s in sets:
            for op, n in s.items():
                by_fn[op] = by_fn.get(op, 0) + 1
                by_occ[op] = by_occ.get(op, 0) + n
        return by_fn, by_occ

    if census["unmodeled_sets"]:
        by_fn, by_occ = agg(census["unmodeled_sets"])
        print("unmodeled-op COMPLETE blocker sets "
              f"({len(census['unmodeled_sets'])} functions):")
        for op, v in sorted(by_fn.items(), key=lambda kv: -kv[1]):
            print(f"    {op:<26} functions {v:>4}  occurrences {by_occ[op]:>5}")
    if census["inc1_subs"]:
        print("single-block sub-reasons (increment-1 refusals):")
        for k, v in sorted(census["inc1_subs"].items(), key=lambda kv: -kv[1]):
            print(f"    {k:<40} {v}")
    if census["refused_sets"]:
        by_fn, by_occ = agg(census["refused_sets"])
        print("apply-colouring COMPLETE refused sets "
              f"({len(census['refused_sets'])} functions):")
        for op, v in sorted(by_fn.items(), key=lambda kv: -kv[1]):
            print(f"    {op:<40} functions {v:>4}  occurrences {by_occ[op]:>5}")


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
    # RQ-59-MEASURE: instruction-level aggregates (capstone-optional) — count
    # and size can move in OPPOSITE directions (narrow movs traded for wide
    # ldr.w), so the verdict must quote both.
    im = [r for r in rows if "insn_off" in r]
    if im:
        def tot(side, key):
            return sum(r[side][key] for r in im)
        print(f"insns  off={tot('insn_off', 'insns')}  on={tot('insn_on', 'insns')}  "
              f"delta={tot('insn_on', 'insns') - tot('insn_off', 'insns'):+d}   "
              f"[{len(im)}/{len(rows)} functions disassembled]")
        print(f"wide (32-bit) encodings   : off={tot('insn_off', 'wide')}  "
              f"on={tot('insn_on', 'wide')}  "
              f"delta={tot('insn_on', 'wide') - tot('insn_off', 'wide'):+d}")
        ft_off = tot('insn_off', 'frame_ld') + tot('insn_off', 'frame_st')
        ft_on = tot('insn_on', 'frame_ld') + tot('insn_on', 'frame_st')
        print(f"frame traffic ([sp,#..] ld/st): off={ft_off}  on={ft_on}  "
              f"delta={ft_on - ft_off:+d}  "
              f"(wide: {tot('insn_off', 'wide_frame')} -> {tot('insn_on', 'wide_frame')})")
        print(f"push/pop breadth (regs)   : off={tot('insn_off', 'pushpop_regs')}  "
              f"on={tot('insn_on', 'pushpop_regs')}")
        print(f"frame size (SUB sp bytes) : off={tot('insn_off', 'sp_sub')}  "
              f"on={tot('insn_on', 'sp_sub')}")
    if declines:
        # RQ-59-REACH separation: `identity-colouring` is the colourer
        # SUCCEEDING with nothing to improve (a validated identity rewrite
        # handed to the shipping pass), NOT a reach failure — mixing it into
        # the histogram made the top "decline" bucket look like a limit.
        ident = declines.get("identity-colouring", 0)
        fails = {k: v for k, v in declines.items() if k != "identity-colouring"}
        print(f"identity-colouring (SUCCESS, nothing to improve): {ident}")
        print(f"reach failures (flag-on): {sum(fails.values())}")
        for k, v in sorted(fails.items(), key=lambda kv: -kv[1]):
            print(f"    {k:<26} {v}")
    if changed:
        print("per-function changes:")
        for r in sorted(changed, key=lambda r: r["bytes_on"] - r["bytes_off"]):
            dc = ""
            if r["cycles_off"] is not None and r["cycles_on"] is not None:
                dc = f"  cyc {r['cycles_off']}->{r['cycles_on']} " \
                     f"({r['cycles_on'] - r['cycles_off']:+d})"
            di = ""
            if "insn_off" in r:
                io, ion = r["insn_off"], r["insn_on"]
                fo = io["frame_ld"] + io["frame_st"]
                fn_ = ion["frame_ld"] + ion["frame_st"]
                di = f"  insn {io['insns']}->{ion['insns']} " \
                     f"wide {io['wide']}->{ion['wide']} " \
                     f"frame {fo}->{fn_}"
            print(f"    {r['fixture']:<34} {r['func']:<24} "
                  f"{r['bytes_off']:>4} -> {r['bytes_on']:>4} "
                  f"({r['bytes_on'] - r['bytes_off']:+d}){dc}{di}")
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
    for tag, reloc in (("relocatable / label-form branches (fully in scope)", True),
                       ("self-contained / pre-resolved numeric branches "
                        "(branches out of scope; calls in scope)", False)):
        rows, applied, declines, errors, census = measure(synth, reloc)
        summ = report(tag, rows, applied, declines, errors)
        census_report(census)
        summ["census"] = census
        summary["relocatable" if reloc else "self_contained"] = summ
    if out_json:
        Path(out_json).write_text(json.dumps(summary, indent=2))
        print(f"\nwrote {out_json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
