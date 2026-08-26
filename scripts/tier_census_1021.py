#!/usr/bin/env python3
# NOTE on home: this lives in scripts/ (with claim_check.py and
# model_coverage_audit.py — derivation/audit tooling over shipped artifacts),
# not scripts/repro/ (defect oracles). It is RQ-59-TIERCENSUS's measurement
# artifact, report-and-stop by scope. The enforcing gate over its findings is
# VCR-TIER-001 increment 1, LANDED as scripts/repro/expansion_canary_gate_1021.py
# (CI-wired): it executes every rule-emitted expansion under canaries and pins
# the unguarded-clobber set at EMPTY — stronger than "does not grow".
"""RQ-59-TIERCENSUS (#1021) — the proof-tier census, re-derivable.

#1021 shipped a memory-safety miscompile THROUGH a Rocq-proved rule:
`rule_i32_popcnt` is proved, it emits the `ArmOp::Popcnt` PSEUDO-OP, and the
defect lived in that pseudo-op's ENCODER EXPANSION (R11 — the WASM
linear-memory base — borrowed as scratch, in no pushed set, leaking to every
caller). `ArmSemantics` executes POPCNT atomically (writes rd only), so the
clobber was unrepresentable in the model: the proof was real, the model was
faithful to the pseudo-op, the machine still corrupted memory. An atomic model
of a multi-instruction expansion is a SILENT CLAIM that the expansion is
scratch-free. This script measures how many such claims the 80-rule
VCR-SEL-001 surface makes, and how many are unguarded.

Everything here is DERIVED from shipped artifacts, not hand-listed:

  rules → ops     parsed from `crates/synth-synthesis/src/sel_dsl/generated.rs`
                  (the committed lowering functions, pinned 1:1 to `RULES` by
                  `generated_lowering_is_up_to_date` and to the Rocq theorems by
                  `//coq:vcr_sel_rules_coverage`), cross-checked against
                  `coq/vcr_sel_rules.manifest`.
  ops → bytes     the REAL encoders, via `cargo run -p synth-backend --example
                  tier_census_dump_1021` (Thumb-2 + A32, one representative
                  non-aliased instance per emitted variant; the example fails
                  loudly if its instance table drifts from generated.rs).
  bytes → effects capstone decode (static write sets, instruction counts) plus
                  unicorn execution over several operand valuations (net
                  register clobbers after completion, SP discipline, memory
                  traffic) — a grep is a hypothesis, the executed bytes are the
                  measurement.
  guards          SMT-certification coverage parsed from
                  `crates/synth-verify/src/expansion_validator.rs`
                  (`covered_i64_pseudo_selections`, asserted result-tier ONLY —
                  `validate_expansion` compares the contract result registers
                  and nothing else, so a reserved-register clobber is invisible
                  to it BY CONSTRUCTION); execution-differential coverage
                  derived by scanning `scripts/repro/*_differential.py` headers
                  (`ci-status: wired`) for the WASM ops present in their .wat
                  fixtures; frozen-anchor coverage from the fixtures pinned in
                  `crates/synth-cli/tests/frozen_codegen_bytes.rs`.

The residual hand-written parts, stated per the census method note: the
representative operand choice in the dump example (no derivation can pick
operands), the backend-of-a-script heuristic (filename: `a32_` → A32,
`riscv`/`aarch64`/`rv32` → out of scope, else Thumb-2), and the
"state-observing" test (a differential counts as able to observe a wrong
REGISTER EFFECT only if it reads a reserved register back or compares a memory
image AFTER emulation — detected by grep; the two hits on main were verified
by hand and both are INDIRECT: `i64_global_init_649` reads R9 once at startup
and then compares R9-relative global values, `stack_layout_687` compares a RAM
image — each would see a reserved-register clobber only if the fixture happens
to route a dependent access through the clobbered base afterwards. No wired
differential on main reads R9/R10/R11 back after return; PR #1039's
`popcnt_r11_clobber_1021_differential.py` is the first).

Usage:
    python3 scripts/tier_census_1021.py [--json OUT.json] [--dump FILE]
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

from capstone import CS_ARCH_ARM, CS_MODE_ARM, CS_MODE_THUMB, Cs
from unicorn import (
    UC_ARCH_ARM,
    UC_HOOK_MEM_WRITE,
    UC_MODE_ARM,
    UC_MODE_THUMB,
    Uc,
    UcError,
)
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R4,
    UC_ARM_REG_R5,
    UC_ARM_REG_R6,
    UC_ARM_REG_R7,
    UC_ARM_REG_R8,
    UC_ARM_REG_R9,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_R12,
    UC_ARM_REG_SP,
)

ROOT = Path(__file__).resolve().parents[1]
GENERATED = ROOT / "crates/synth-synthesis/src/sel_dsl/generated.rs"
MOD_RS = ROOT / "crates/synth-synthesis/src/sel_dsl/mod.rs"
MANIFEST = ROOT / "coq/vcr_sel_rules.manifest"
EXPANSION_VALIDATOR = ROOT / "crates/synth-verify/src/expansion_validator.rs"
FROZEN_TEST = ROOT / "crates/synth-cli/tests/frozen_codegen_bytes.rs"
REPRO = ROOT / "scripts/repro"

# ARM ABI roles this project reserves (the #1021 mechanism lives here):
# R9 = globals base, R10 = memory size, R11 = linear-memory base.
# R12 is the encoder's sanctioned scratch (never allocatable).
RESERVED = {"r9", "r10", "r11"}
SANCTIONED_SCRATCH = {"r12", "ip"}

GPR = {f"r{i}" for i in range(13)} | {"sp", "lr", "pc", "ip", "fp", "sl", "sb"}
CANON = {"ip": "r12", "fp": "r11", "sl": "r10", "sb": "r9"}

REGS = {
    "r0": UC_ARM_REG_R0,
    "r1": UC_ARM_REG_R1,
    "r2": UC_ARM_REG_R2,
    "r3": UC_ARM_REG_R3,
    "r4": UC_ARM_REG_R4,
    "r5": UC_ARM_REG_R5,
    "r6": UC_ARM_REG_R6,
    "r7": UC_ARM_REG_R7,
    "r8": UC_ARM_REG_R8,
    "r9": UC_ARM_REG_R9,
    "r10": UC_ARM_REG_R10,
    "r11": UC_ARM_REG_R11,
    "r12": UC_ARM_REG_R12,
    "sp": UC_ARM_REG_SP,
    "lr": UC_ARM_REG_LR,
}

CODE_BASE = 0x0001_0000
STACK_BASE = 0x2000_0000
STACK_SIZE = 0x10_0000
SP_INIT = STACK_BASE + STACK_SIZE // 2

# Operand valuations. r4 doubles as the shift-amount register in the dump's
# instances, so the sets cover small / large / zero shift paths and the
# negative-high-limb paths the i64 diamonds branch on. The large amount is
# DELIBERATELY not a fixed point of `& 63` (0x67 = 103 -> 39): the i64
# variable-shift expansions mask the amount register IN PLACE, and a
# fixed-point valuation (7, 39, 0) would make that undeclared write invisible
# to the net-state diff — the first census run missed it exactly that way
# (the capstone static column still flagged it, which is why both views run).
# The write is a REAL, executed miscompile when the amount is a register-homed
# local re-read after the shift: filed as #1048 from this census.
INPUT_SETS = [
    {
        "r0": 0x11111111, "r1": 0x22222222, "r2": 0x33333333, "r3": 0x44444444,
        "r4": 7, "r5": 0x66666666, "r6": 0x77777777, "r7": 0x88888888,
        "r8": 0x12345678,
    },
    {
        "r0": 0xFFFFFFFF, "r1": 0x80000000, "r2": 0x80000001, "r3": 0xFFFFFFFF,
        "r4": 0x67, "r5": 0x0000FFFF, "r6": 0x1, "r7": 0x2, "r8": 0xDEADBEEF,
    },
    {
        "r0": 0, "r1": 0, "r2": 0, "r3": 0, "r4": 0, "r5": 0, "r6": 0,
        "r7": 0, "r8": 0,
    },
]
AMBIENT = {"r9": 0x99999990, "r10": 0xAAAAAAA0, "r11": 0xBBBBBBB0,
           "r12": 0xCCCCCCC0, "lr": 0xEEEEEEE1}


def parse_rules() -> dict[str, dict]:
    """rule name -> {"wasm": WasmOp ident, "variants": [ArmOp idents]}."""
    manifest = [
        ln.strip() for ln in MANIFEST.read_text().splitlines()
        if ln.strip() and not ln.startswith("#")
    ]
    mod_src = MOD_RS.read_text()
    ops = dict(re.findall(r'name:\s*"(rule_\w+)",\s*\n\s*op:\s*WasmOp::(\w+)', mod_src))

    gen_src = GENERATED.read_text()
    chunks = re.split(r"\npub fn (rule_\w+)\(", gen_src)
    rules: dict[str, dict] = {}
    for i in range(1, len(chunks), 2):
        name, body = chunks[i], chunks[i + 1]
        variants = re.findall(r"ArmOp::(\w+)", body)
        rules[name] = {"wasm": ops.get(name), "variants": variants}

    if sorted(rules) != sorted(manifest):
        sys.exit(
            f"FATAL: generated.rs rules ({len(rules)}) != manifest ({len(manifest)}); "
            f"diff: {sorted(set(rules) ^ set(manifest))}"
        )
    missing_op = [r for r in rules if rules[r]["wasm"] is None]
    if missing_op:
        sys.exit(f"FATAL: could not parse WasmOp for {missing_op} from mod.rs")
    return rules


def wasm_ident_to_wat(ident: str) -> str:
    """WasmOp ident -> .wat mnemonic (I32Popcnt -> i32.popcnt, Select -> select)."""
    tokens = re.findall(r"[A-Z][a-z]*\d*", ident)
    if tokens[0] in ("I32", "I64") and len(tokens) > 1:
        return tokens[0].lower() + "." + "_".join(t.lower() for t in tokens[1:])
    return "_".join(t.lower() for t in tokens)


def run_dump(dump_file: str | None) -> list[dict]:
    if dump_file:
        return json.loads(Path(dump_file).read_text())
    out = subprocess.run(
        ["cargo", "run", "-p", "synth-backend", "--example", "tier_census_dump_1021"],
        cwd=ROOT, capture_output=True, text=True, check=False,
    )
    if out.returncode != 0:
        sys.exit(f"FATAL: dump example failed:\n{out.stderr[-2000:]}")
    return json.loads(out.stdout)


def static_writes(code: bytes, thumb: bool) -> tuple[int, set[str], list[str]]:
    """(instruction count, statically-written GPRs, mnemonics)."""
    md = Cs(CS_ARCH_ARM, CS_MODE_THUMB if thumb else CS_MODE_ARM)
    md.detail = True
    count, written, mnems = 0, set(), []
    off = 0
    for insn in md.disasm(bytes(code), CODE_BASE):
        count += 1
        off = insn.address + insn.size - CODE_BASE
        mnems.append(insn.mnemonic)
        _, wr = insn.regs_access()
        for r in wr:
            name = md.reg_name(r)
            if name in GPR:
                written.add(CANON.get(name, name))
    if off != len(code):
        sys.exit(
            f"FATAL: capstone decoded {off} of {len(code)} bytes "
            f"({'thumb' if thumb else 'a32'}) — undecodable expansion byte"
        )
    return count, written, mnems


def execute(code: bytes, thumb: bool, ambient: dict[str, int] | None = None) -> dict:
    """Run the expansion; union of net register clobbers over the input sets.

    `ambient` overrides the seeded values of the non-operand registers
    (r9-r12, lr) — the canary gate (scripts/repro/expansion_canary_gate_1021.py,
    VCR-TIER-001) passes its own distinctive canaries; the census default is
    AMBIENT."""
    net: set[str] = set()
    mem_writes: set[int] = set()
    sp_ok = True
    errors: list[str] = []
    for inputs in INPUT_SETS:
        mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB if thumb else UC_MODE_ARM)
        mu.mem_map(CODE_BASE & ~0xFFF, 0x2000)
        mu.mem_map(STACK_BASE, STACK_SIZE)
        mu.mem_write(CODE_BASE, bytes(code))
        seed = {**inputs, **(AMBIENT if ambient is None else ambient), "sp": SP_INIT}
        for name, val in seed.items():
            mu.reg_write(REGS[name], val)

        def on_write(_mu, _acc, addr, size, _val, _data):
            mem_writes.add(addr)
            return True

        mu.hook_add(UC_HOOK_MEM_WRITE, on_write)
        start = CODE_BASE | 1 if thumb else CODE_BASE
        try:
            mu.emu_start(start, CODE_BASE + len(code), count=10_000)
        except UcError as e:
            errors.append(f"{inputs['r4']}: {e}")
            continue
        pc = mu.reg_read(UC_ARM_REG_PC)
        if pc != CODE_BASE + len(code):
            errors.append(f"stopped at {pc:#x}, expected {CODE_BASE + len(code):#x}")
            continue
        for name, val in seed.items():
            if name == "sp":
                if mu.reg_read(REGS[name]) != val:
                    sp_ok = False
                continue
            if mu.reg_read(REGS[name]) != val:
                net.add(name)
    return {
        "net_clobbers": net,
        "sp_restored": sp_ok,
        "mem_writes": sorted(mem_writes),
        "errors": errors,
    }


def parse_smt_coverage() -> set[str]:
    """ArmOp variants covered by covered_i64_pseudo_selections (Thumb-2, result-tier)."""
    src = EXPANSION_VALIDATOR.read_text()
    m = re.search(
        r"pub fn covered_i64_pseudo_selections.*?\n\}", src, flags=re.S
    )
    if not m:
        sys.exit("FATAL: covered_i64_pseudo_selections not found in expansion_validator.rs")
    return set(re.findall(r"ArmOp::(\w+)", m.group(0)))


def parse_frozen_fixtures() -> list[str]:
    src = FROZEN_TEST.read_text()
    m = re.search(
        r"fn frozen_fixtures_text_is_bit_identical_oracle_001.*?assert_frozen",
        src, flags=re.S,
    )
    return re.findall(r'"([\w./]+\.(?:wasm|wat))"', m.group(0)) if m else []


WAT_OP_RE = re.compile(r"\b(i32\.[a-z_0-9]+|i64\.[a-z_0-9]+|select)\b")


def wired_differential_coverage() -> dict[str, list[dict]]:
    """wat op -> [{script, backend, state_observing}] over wired ARM differentials."""
    cov: dict[str, list[dict]] = defaultdict(list)
    for script in sorted(REPRO.glob("*.py")):
        head = script.read_text(errors="replace")
        if "ci-status: wired" not in head.splitlines()[1] and "ci-status: wired" not in head[:400]:
            continue
        name = script.name
        if any(k in name for k in ("riscv", "rv32", "aarch64")):
            continue
        backend = "a32" if name.startswith("a32_") else "thumb2"
        # A differential can only observe a wrong REGISTER EFFECT if it reads a
        # reserved register back or inspects memory after emulation.
        state_observing = bool(
            re.search(r"reg_read\(\s*UC_ARM_REG_R(9|10|11)\b", head)
            or re.search(r"mem_read\(.+\)\s*(?:!=|==)", head)
            or ("mem_read" in head and "expected_mem" in head)
        )
        ops: set[str] = set()
        if name == "arm_corpus_sweep_973.py":
            # The corpus sweep compiles EVERY scripts/repro/*.wat for ARM and
            # executes the pure all-i32 exports vs wasmtime — attribute the
            # whole corpus's ops (compile tier for all, execute tier for the
            # pure subset; see the script's own purity note).
            for p in REPRO.glob("*.wat"):
                ops |= set(WAT_OP_RE.findall(p.read_text(errors="replace")))
        else:
            for fix in set(re.findall(r"([\w.]+\.wat)\b", head)):
                p = REPRO / fix
                if p.exists():
                    ops |= set(WAT_OP_RE.findall(p.read_text(errors="replace")))
            # in-line (module ...) literals inside the script itself
            if "(module" in head:
                ops |= set(WAT_OP_RE.findall(head))
        for op in ops:
            cov[op].append(
                {"script": name, "backend": backend, "state_observing": state_observing}
            )
    # The wast conformance runner (wast_conformance_928_differential.py, wired)
    # EXECUTES the assert_return values in tests/wast/ under unicorn on the
    # Thumb-2 backend — but DECLINES i64-valued assertions ("i64-pair"), so
    # only i32-valued ops and select count as executed there.
    wast_ops: set[str] = set()
    for p in (ROOT / "tests/wast").glob("*.wast"):
        wast_ops |= set(WAT_OP_RE.findall(p.read_text(errors="replace")))
    for op in wast_ops:
        if op.startswith("i64."):
            continue
        cov[op].append(
            {
                "script": "wast_conformance_928_differential.py",
                "backend": "thumb2",
                "state_observing": False,
            }
        )
    return cov


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", help="also write the machine-readable census here")
    ap.add_argument("--dump", help="reuse an existing dump JSON instead of cargo run")
    args = ap.parse_args()

    rules = parse_rules()
    print(f"rules in manifest & generated.rs: {len(rules)}")

    dump = run_dump(args.dump)
    smt_covered = parse_smt_coverage()
    frozen = parse_frozen_fixtures()
    frozen_ops: set[str] = set()
    for f in frozen:
        wat = REPRO / f.replace(".wasm", ".wat")
        if wat.exists():
            frozen_ops |= set(WAT_OP_RE.findall(wat.read_text(errors="replace")))
    diff_cov = wired_differential_coverage()

    # ---- per-variant expansion analysis ------------------------------------
    variants: dict[str, dict] = {}
    for inst in dump:
        v = inst["variant"]
        rec = variants.setdefault(
            v,
            {
                "shapes": [], "max_insns": {"thumb2": 0, "a32": 0},
                "static_writes": {"thumb2": set(), "a32": set()},
                "net_clobbers": {"thumb2": set(), "a32": set()},
                "push_pop": {"thumb2": False, "a32": False},
                "sp_ok": True, "mem": {"thumb2": set(), "a32": set()},
                "outputs": set(), "declared_temps": set(), "errors": [],
            },
        )
        rec["shapes"].append(inst["shape"])
        rec["outputs"] |= set(inst["outputs"])
        # VCR-TIER-001: the dump's `scratch_contract` is DERIVED from the
        # shipped crate's single declaration site
        # (`synth_backend::arm_encoder::expansion_scratch_contract`); the
        # `declared_temps` fallback reads dumps generated before that existed
        # (they carried a hand column mirroring the pre-#1048 operand temps),
        # and a dump with neither defaults to the STRICTEST contract — {rd}
        # only, the same silent claim the atomic model makes.
        rec["declared_temps"] |= set(
            inst.get("scratch_contract", inst.get("declared_temps", []))
        )
        for isa, key in (("thumb2", "thumb"), ("a32", "a32")):
            hexs = inst[key]
            if not hexs:
                rec["errors"].append(f"{isa}:{inst['shape']}:{inst[key + '_err']}")
                continue
            code = bytes.fromhex(hexs)
            n, wr, mnems = static_writes(code, thumb=isa == "thumb2")
            rec["max_insns"][isa] = max(rec["max_insns"][isa], n)
            rec["static_writes"][isa] |= wr
            if any(m.startswith(("push", "pop", "stm", "ldm")) for m in mnems):
                rec["push_pop"][isa] = True
            ex = execute(code, thumb=isa == "thumb2")
            rec["net_clobbers"][isa] |= ex["net_clobbers"]
            rec["sp_ok"] &= ex["sp_restored"]
            rec["mem"][isa] |= set(ex["mem_writes"])
            rec["errors"].extend(f"{isa}:{inst['shape']}:{e}" for e in ex["errors"])

    # ---- classification ----------------------------------------------------
    print("\n=== per-variant expansion census (Thumb-2 / A32) ===")
    hdr = (
        f"{'variant':14s} {'insT':>4s} {'insA':>4s} {'pseudo':6s} "
        f"{'net-clobbers beyond decl':24s} {'touched(restored/static)':24s} rsvd"
    )
    print(hdr)
    pseudo_variants: set[str] = set()
    findings: dict[str, dict] = {}
    for v, rec in sorted(variants.items()):
        declared = rec["outputs"] | rec["declared_temps"]
        it, ia = rec["max_insns"]["thumb2"], rec["max_insns"]["a32"]
        is_pseudo = max(it, ia) > 1
        if is_pseudo:
            pseudo_variants.add(v)
        net = (rec["net_clobbers"]["thumb2"] | rec["net_clobbers"]["a32"]) - declared
        static = (rec["static_writes"]["thumb2"] | rec["static_writes"]["a32"]) - declared - {"pc"}
        touched_restored = static - net
        rsvd = sorted((net | static) & RESERVED)
        findings[v] = {
            "insns": {"thumb2": it, "a32": ia},
            "pseudo": is_pseudo,
            "net_clobbers": sorted(net),
            "touched_restored": sorted(touched_restored),
            "reserved_touched": rsvd,
            "push_pop": rec["push_pop"],
            "sp_restored": rec["sp_ok"],
            "mem_write_addrs": sorted(rec["mem"]["thumb2"] | rec["mem"]["a32"]),
            "errors": rec["errors"],
        }
        print(
            f"{v:14s} {it:4d} {ia:4d} {'YES' if is_pseudo else '-':6s} "
            f"{','.join(sorted(net)) or '-':24s} "
            f"{','.join(sorted(touched_restored)) or '-':24s} "
            f"{','.join(rsvd) or '-'}"
        )
        if rec["errors"]:
            print(f"    !! {rec['errors']}")

    # ---- guards per pseudo variant ----------------------------------------
    # Map each variant back to the rules (and WASM ops) that emit it.
    variant_rules: dict[str, list[str]] = defaultdict(list)
    for rname, r in rules.items():
        for v in set(r["variants"]):
            variant_rules[v].append(rname)

    print("\n=== guard census for pseudo-op variants ===")
    guard_rows: dict[str, dict] = {}
    for v in sorted(pseudo_variants):
        wat_ops = sorted({wasm_ident_to_wat(rules[r]["wasm"]) for r in variant_rules[v]})
        smt = v in smt_covered
        diffs_t = sorted(
            {d["script"] for op in wat_ops for d in diff_cov.get(op, []) if d["backend"] == "thumb2"}
        )
        diffs_a = sorted(
            {d["script"] for op in wat_ops for d in diff_cov.get(op, []) if d["backend"] == "a32"}
        )
        observing = sorted(
            {d["script"] for op in wat_ops for d in diff_cov.get(op, []) if d["state_observing"]}
        )
        anchor = any(op in frozen_ops for op in wat_ops)
        guard_rows[v] = {
            "rules": sorted(variant_rules[v]),
            "wat_ops": wat_ops,
            "smt_cert_thumb2_result_tier": smt,
            "wired_differentials_thumb2": diffs_t,
            "wired_differentials_a32": diffs_a,
            "state_observing_differentials": observing,
            "frozen_anchor_ops": anchor,
        }
        print(f"{v}: rules={','.join(sorted(variant_rules[v]))}")
        print(f"    smt-cert(thumb2, result-tier): {'YES' if smt else 'no'}")
        print(f"    wired value-tier differentials: thumb2={len(diffs_t)} a32={len(diffs_a)}")
        print(f"    state-observing (register-effect) differentials: {observing or 'NONE'}")
        print(f"    frozen-anchor byte pin over these ops: {'yes' if anchor else 'no'}")

    # ---- the headline sets -------------------------------------------------
    pseudo_rules = sorted(
        r for r, rr in rules.items() if any(v in pseudo_variants for v in rr["variants"])
    )
    # R12 is the encoder's SANCTIONED scratch (never allocatable, clobberable
    # across ops by repo contract) — an r12-only net clobber is within the
    # declared ABI. Everything else beyond the declared outputs/temps is not.
    unsanctioned = {
        v: sorted(set(f["net_clobbers"]) - SANCTIONED_SCRATCH)
        for v, f in findings.items()
        if f["pseudo"] and set(f["net_clobbers"]) - SANCTIONED_SCRATCH
    }
    reserved_subset = {
        v: f["reserved_touched"] for v, f in findings.items() if f["reserved_touched"]
    }
    unguarded_value = [
        v for v in sorted(pseudo_variants)
        if not guard_rows[v]["smt_cert_thumb2_result_tier"]
        and not guard_rows[v]["wired_differentials_thumb2"]
        and not guard_rows[v]["wired_differentials_a32"]
    ]
    # The #1021 gap: an expansion that could scribble on state beyond its
    # declared result, with NO guard capable of noticing a wrong register
    # effect. (The SMT cert asserts result registers only — by construction it
    # cannot see this class; value-tier differentials return the leaf's value
    # and never read the reserved registers back.)
    clobber_capable = sorted(set(unsanctioned) | set(reserved_subset))
    unguarded_clobber = [
        v for v in clobber_capable if not guard_rows[v]["state_observing_differentials"]
    ]

    print("\n=== HEADLINE ===")
    print(f"rules total: {len(rules)}")
    print(f"pseudo-op-emitting rules: {len(pseudo_rules)} "
          f"(proof at pseudo-op tier, expansion below the model)")
    print(f"pseudo-op variants: {len(pseudo_variants)}: {sorted(pseudo_variants)}")
    print(f"value-tier UNGUARDED pseudo variants (no cert, no wired differential): "
          f"{unguarded_value or 'NONE'}")
    print("net clobbers beyond declared outputs/temps + sanctioned R12:")
    for v in sorted(unsanctioned):
        print(f"  {v}: {unsanctioned[v]}  (push_pop={findings[v]['push_pop']})")
    if not unsanctioned:
        print("  NONE")
    print(f"RESERVED-REGISTER (R9/R10/R11) scratch subset — the #1021 mechanism: "
          f"{reserved_subset or 'NONE'}")
    print(f"clobber-tier UNGUARDED subset (clobber-capable AND no state-observing "
          f"differential): {unguarded_clobber or 'NONE'}")
    print("note: r12-only net clobbers (sanctioned encoder scratch): "
          + (", ".join(sorted(
              v for v, f in findings.items()
              if f["pseudo"] and f["net_clobbers"]
              and not set(f["net_clobbers"]) - SANCTIONED_SCRATCH)) or "none"))

    if args.json:
        Path(args.json).write_text(json.dumps({
            "rules": {r: {"wasm": rr["wasm"], "variants": rr["variants"]} for r, rr in rules.items()},
            "findings": {v: f for v, f in findings.items()},
            "guards": guard_rows,
            "pseudo_rules": pseudo_rules,
            "unguarded_value_tier": unguarded_value,
            "unsanctioned_net_clobbers": unsanctioned,
            "reserved_register_subset": reserved_subset,
            "unguarded_clobber_tier": unguarded_clobber,
        }, indent=1, default=sorted))
        print(f"\nwrote {args.json}")


if __name__ == "__main__":
    main()
