#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 6
"""RQ-62-MEMISOLATE (#1145) — the RED leg of gale's two-tenant kill-criterion,
plus the region-table structural pins and the decline-matrix envelope pins.

THE CRITERION (gale's, adopted verbatim on #1145):

    "a two-tenant image where tenant A writes outside its region and the
     write lands in tenant B's memory instead of faulting"

This oracle executes the RED half — the write LANDS — which needs no MPU
model: it compiles gale's two-tenant fixture (memory 0 = tenant A at the R11
base, memory 1 = tenant B via `__synth_wasm_data_1`), places the two regions
ADJACENT (the physically plausible layout the MPU exists to police), and runs
tenant A's guardless `write_a` one byte-offset past its own page. Under
unicorn (which models no ARMv7-M MPU) the store completes without any fault
and tenant B observes the byte — exactly the outcome the criterion names as
the failure. wasmtime first confirms the SPEC verdict on the same call: an
out-of-bounds store must TRAP, so the landed write is a real isolation hole,
not an in-bounds access.

The GREEN half — the same write FAULTS once the embedder programs one MPU
region per memory from the #1145 region table — is NOT executable here:
unicorn does not model the ARMv7-M MPU. It runs on an MPU-modeling venue:
gale's Renode Cortex-M4 platform (Renode's own `tests/unit-tests/mpu.robot`
passes Zephyr's mem_protect suite on stm32f4) or the STM32G474RE bench. Until
that executes, `--safety-bounds mpu` on a multi-memory module KEEPS REFUSING
(pinned below), so this oracle landing green does not let synth claim
isolation — it proves the hole the region table exists to close, and pins the
table's shape.

Also pinned here, so the compliance envelope cannot drift silently:
  * region table structure — `__synth_mem_{count,size_0,size_1}` SHN_ABS with
    exact values, `__synth_mem_base_1` at the base of `.synth.wasm_mem_1`
    with st_size = region extent, and NO `__synth_mem_base_0` (memory 0's
    base is the embedder's R11 value; a symbol would be a second source of
    truth).
  * `--safety-bounds software|mask` still LOUD-decline the memory-1 access
    (root cause: memory 1 has no size register — R10 is memory 0's) and the
    module fails via #952 rather than shipping a partial object.
  * `--safety-bounds mpu` still refuses, naming the region table and the
    two-tenant criterion rather than the closed "#406 phase 2".

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/mem_isolation_red_1145.py

RED-FIRST evidence: on main @ 12a01a32 (pre-#1145) the structural half FAILS
— the object carries no `__synth_mem_*` symbol — while the execution half
already lands the cross-tenant write (the hole predates the table).
"""

import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("mem_isolation_two_tenant_1145.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
ABS32 = 2
PAGE = 0x10000
SHN_ABS = "SHN_ABS"

TEXT_BASE = 0x10000
# ADJACENT tenant regions — deliberately, unlike the far-apart placement in
# multi_memory_406_differential.py. Adjacency is the layout the MPU exists to
# police: tenant A's one-past-the-end store lands on tenant B's first page
# instead of unmapped space, so the criterion's "lands in tenant B's memory"
# is observed as a VALUE, never as an accidental unicorn unmapped-fault.
MEM0_BASE = 0x200000  # tenant A: memory 0, the R11 base (1 page)
MEM1_BASE = MEM0_BASE + PAGE  # tenant B: memory 1, __synth_wasm_data_1 (1 page)
STACK_BASE = 0x600000
MEM1_SECTION = ".synth.wasm_mem_1"

# Tenant A's out-of-region store: one wasm page past its own memory, byte 3.
OOB_ADDR = PAGE + 3
POISON = 0xAA


def fail(msg):
    print(f"FAIL: {msg}")
    sys.exit(1)


def compile_variant(obj, extra):
    return subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", str(obj), "--target", "cortex-m3",
         "--all-exports", "--relocatable", "--embedder-data-init", *extra],
        capture_output=True,
        text=True,
    )


def main():
    tmp = Path(tempfile.mkdtemp(prefix="memiso1145_"))

    # ── Envelope pins: the decline matrix, exact and loud ────────────────────
    for mode, needles in (
        ("software", ["read_b", "memory-0-only", "#952"]),
        ("mask", ["read_b", "memory-0-only", "#952"]),
        ("mpu", ["#1145", "__synth_mem_base_N", "two-tenant"]),
    ):
        p = compile_variant(tmp / f"declined_{mode}.o", ["--safety-bounds", mode])
        if p.returncode == 0:
            fail(
                f"--safety-bounds {mode} now ACCEPTS the two-tenant module. If "
                f"that is deliberate, the #1145 fault criterion must have "
                f"executed on an MPU-bearing venue first (RQ-62-REACH) and this "
                f"pin updated with it."
            )
        blob = (p.stderr or "") + (p.stdout or "")
        for needle in needles:
            if needle not in blob:
                fail(f"--safety-bounds {mode} refusal no longer names {needle!r}")
    print("declines pinned: software/mask skip memory-1 loudly (#952), mpu refuses naming #1145")

    # ── The shipped object ───────────────────────────────────────────────────
    obj = tmp / "two_tenant.o"
    p = compile_variant(obj, [])
    if p.returncode != 0:
        print(p.stderr.strip())
        fail("plain --relocatable compile of the two-tenant module declined")

    e = ELFFile(open(obj, "rb"))
    secname_by_idx = {i: s.name for i, s in enumerate(e.iter_sections())}
    text = bytearray(e.get_section_by_name(".text").data())
    mem1 = e.get_section_by_name(MEM1_SECTION)
    if mem1 is None or mem1["sh_type"] != "SHT_PROGBITS" or mem1["sh_size"] != PAGE:
        fail(f"{MEM1_SECTION} missing or not a 1-page PROGBITS region")
    mem1_image = bytes(mem1.data())
    if mem1_image[0:7] != b"tenantB":
        fail("tenant B's init segment not placed at offset 0")

    symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
    syms = {s.name: (s["st_shndx"], s["st_value"], s["st_size"])
            for s in symtab.iter_symbols()}

    # ── Region-table structural pins (#1145 option 3) ────────────────────────
    for name, want in (
        ("__synth_mem_count", 2),
        ("__synth_mem_size_0", PAGE),
        ("__synth_mem_size_1", PAGE),
    ):
        if name not in syms:
            fail(f"{name} not emitted — the #1145 region table is absent")
        shndx, value, _ = syms[name]
        if shndx != SHN_ABS:
            fail(f"{name} must be SHN_ABS (link-invariant value), got {shndx}")
        if value != want:
            fail(f"{name} = {value:#x}, want {want:#x}")
    if "__synth_mem_base_1" not in syms:
        fail("__synth_mem_base_1 not emitted — the embedder has no region base")
    shndx, value, size = syms["__synth_mem_base_1"]
    if not isinstance(shndx, int) or secname_by_idx[shndx] != MEM1_SECTION:
        fail(f"__synth_mem_base_1 must live in {MEM1_SECTION}, got {shndx}")
    if value != 0 or size != PAGE:
        fail(f"__synth_mem_base_1 value/size = {value:#x}/{size:#x}, want 0/{PAGE:#x}")
    if "__synth_mem_base_0" in syms:
        fail("__synth_mem_base_0 emitted — memory 0's base is the embedder's "
             "R11 value; a link-time symbol is a second source of truth")
    print("region table pinned: count=2, size_0/size_1 SHN_ABS exact, base_1 in "
          f"{MEM1_SECTION}, no base_0")

    # ── Spec ground truth: the OOB store TRAPS in wasmtime ───────────────────
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, WAT.read_text())
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    trapped = False
    try:
        inst.exports(store)["write_a"](store, OOB_ADDR, POISON)
    except wasmtime.Trap:
        trapped = True
    if not trapped:
        fail(f"wasmtime did not trap write_a({OOB_ADDR:#x}) — fixture addresses "
             f"are wrong; the RED leg would prove nothing")
    print(f"wasmtime: write_a({OOB_ADDR:#x}) TRAPS — the spec verdict on this store")

    # ── Patch relocs, map the adjacent two-tenant layout ─────────────────────
    sec_bases = {MEM1_SECTION: MEM1_BASE, ".text": TEXT_BASE}
    rel = e.get_section_by_name(".rel.text")
    n_mem1_relocs = 0
    for r in rel.iter_relocations() if rel is not None else []:
        if r["r_info_type"] != ABS32:
            continue
        sym = symtab.get_symbol(r["r_info_sym"])
        shndx, val, _ = syms[sym.name]
        secname = secname_by_idx[shndx]
        if secname not in sec_bases:
            fail(f"unexpected ABS32 reloc into section {secname}")
        if secname == MEM1_SECTION:
            n_mem1_relocs += 1
        (add,) = struct.unpack_from("<I", text, r["r_offset"])
        struct.pack_into("<I", text, r["r_offset"],
                         (sec_bases[secname] + val + add) & 0xFFFFFFFF)
    if n_mem1_relocs == 0:
        fail("no ABS32 reloc against memory 1 — read_b is not symbol-addressed")

    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(TEXT_BASE, PAGE)
    mu.mem_map(MEM0_BASE, PAGE)  # tenant A
    mu.mem_map(MEM1_BASE, PAGE)  # tenant B — ADJACENT
    mu.mem_map(STACK_BASE, PAGE)
    mu.mem_write(TEXT_BASE, bytes(text))
    RET = TEXT_BASE + PAGE - 0x10
    mu.mem_write(RET, b"\x00\xbf\x00\xbf")

    def run(fn, args):
        for reg, val in zip((UC_ARM_REG_R0, UC_ARM_REG_R1), args):
            mu.reg_write(reg, val & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_R10, PAGE)  # memory 0's size in bytes
        mu.reg_write(UC_ARM_REG_R11, MEM0_BASE)  # memory 0's base
        mu.reg_write(UC_ARM_REG_SP, STACK_BASE + PAGE - 0x100)
        mu.reg_write(UC_ARM_REG_LR, RET | 1)
        entry = TEXT_BASE + (syms[fn][1] & ~1)
        mu.emu_start(entry | 1, RET, timeout=5_000_000)
        return mu.reg_read(UC_ARM_REG_R0)

    # The embedder contract: seed tenant A (--embedder-data-init) and tenant B
    # (the object's own section image) before any export runs.
    mu.mem_write(MEM0_BASE, b"\x00" * PAGE)
    mu.mem_write(MEM0_BASE, b"tenantA")
    mu.mem_write(MEM1_BASE, mem1_image)

    # Sanity: each tenant reads its own data through its own region.
    for fn, arg, want, what in (
        ("read_a", 0, ord("t"), "tenant A byte 0"),
        ("read_a", 6, ord("A"), "tenant A byte 6"),
        ("read_b", 6, ord("B"), "tenant B byte 6"),
        ("read_b", 3, ord("a"), "tenant B byte 3, pre-write"),
    ):
        got = run(fn, (arg,)) & 0xFF
        if got != want:
            fail(f"sanity {fn}({arg}) = {got:#x}, want {want:#x} ({what})")
    print("sanity: both tenants read their own init data through their own regions")

    # ── THE RED LEG ──────────────────────────────────────────────────────────
    # Tenant A writes one page past its own region. No MPU is modeled, no
    # guard is emitted (--safety-bounds none is the only accepting mode for
    # this module): the store must COMPLETE — a fault here means the harness
    # layout is wrong, not that isolation exists.
    try:
        run("write_a", (OOB_ADDR, POISON))
    except UcError as exc:
        fail(f"write_a({OOB_ADDR:#x}) faulted in a NO-MPU harness ({exc}) — "
             f"the adjacency layout is broken; this leg must observe the LANDED "
             f"write, not a fault")

    raw = mu.mem_read(MEM1_BASE + 3, 1)[0]
    seen = run("read_b", (3,)) & 0xFF
    if raw != POISON or seen != POISON:
        fail(f"cross-tenant write did NOT land (raw={raw:#x}, read_b(3)={seen:#x}) "
             f"— the RED leg no longer demonstrates the hole; if an MPU/guard "
             f"now stops it, move this criterion to the GREEN venue")
    print(f"RED: tenant A's write_a({OOB_ADDR:#x}, {POISON:#x}) LANDED in tenant "
          f"B's memory (read_b(3) = {seen:#x}, was 'a') — no fault. Exactly the "
          f"outcome gale's criterion names.")
    print("GREEN leg (same write must FAULT with MPU regions programmed from the "
          "#1145 table): NOT executable under unicorn — runs on gale's Renode "
          "Cortex-M4 platform or the STM32G474RE bench.")
    print("RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
