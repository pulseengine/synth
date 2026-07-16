#!/usr/bin/env python3
"""#275 — self-contained `--cortex-m` call_indirect EXECUTION differential.

The finale of #275: the falcon shape — a SELF-CONTAINED Cortex-M image whose
exports dispatch through a funcref table — must EXECUTE correctly, including
every WASM Core §4.4.8 trap. RED-FIRST: on the pre-fix main this fails at the
symbol probe (`via1`/`via2` loud-declined, absent from the image — the #717
interim); with the flash-resident funcref table (PC-relative dispatch, never
R11) it is GREEN.

For each (export, index) case both engines run:
  - wasmtime (oracle): matching dispatches return values; wrong-class calls
    trap ("indirect call type mismatch"); null slots trap ("uninitialized
    element"); OOB indices trap ("undefined element").
  - unicorn (the DEFAULT self-contained image, its OWN Reset_Handler startup —
    the harness fabricates NOTHING: no table region, no RAM contents beyond
    what the image's reset path copies): matching calls must equal wasmtime;
    type-mismatch, null AND OOB cases must all stop AT A UDF (the deterministic
    §4.4.8 trap idiom), never a stray fault or a wrong value.

Non-collision proof (the #717 root cause): the `via1(x, 1)` dispatch target
$ld READS LINEAR MEMORY initialized by an active data segment (`x + 42`) —
correct values prove the funcref table lives outside the R11 linmem region and
the dispatched function's linmem addressing survived the dispatch.

Non-vacuity: a build without the type check BLXes the wrong-signature function
and produces a wrong VALUE (via1(x,0) runs $add on one argument) — a mismatch,
not a vacuous pass; a missing null check BLXes address 0 (fault, distinguished
from UDF); a missing bounds guard reads past the table.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python \
      scripts/repro/call_indirect_275_selfcontained_execution_differential.py
Exits nonzero on a compile decline, missing export, value mismatch, or a trap
that does not stop at a UDF.
"""

import os
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("call_indirect_275_selfcontained_execution.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

FLASH, RAM, RAM_SIZE = 0x0000_0000, 0x2000_0000, 0x40000
RET = 0x000F_0000  # inside the flash map, far past any code
X = 10
# Per dispatcher: index -> expected wasmtime outcome category (§4.4.8).
CASES = {
    "via2": {"ok": [0, 2], "type": [1], "null": [3, 4], "oob": [5, 99]},
    "via1": {"ok": [1], "type": [0, 2], "null": [3, 4], "oob": [5, 99]},
}
TRAP_REASON = {
    "type": "indirect call type mismatch",
    "null": "uninitialized element",
    "oob": "undefined element",
}


def compile_synth(out: str) -> None:
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, "--all-exports",
         "-b", "arm", "--target", "cortex-m3"],
        capture_output=True, text=True,
    )
    if r.returncode != 0:
        sys.exit(f"compile failed: {r.stderr}")
    if "skipping function" in r.stderr:
        # The pre-fix #717 interim: call_indirect loud-declined. RED.
        print(r.stderr)
        print("\nORACLE: FAIL — dispatchers were loud-declined (the #717 "
              "interim); self-contained call_indirect did not compile (#275)")
        sys.exit(1)


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            for sy in sec.iter_symbols():
                if sy.name:
                    syms[sy.name] = sy["st_value"]
    return text.data(), text["sh_addr"], syms, f["e_type"]


class ImageRunner:
    """The DEFAULT self-contained image, startup included — one persistent
    unicorn instance on ZEROED RAM (only the image's own reset path populates
    it: R11/linmem init + the #758 ROM->RAM data copy)."""

    def __init__(self, code, base, syms):
        self.code, self.base, self.syms = code, base, syms
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        self.mu.mem_map(FLASH, 0x100000)
        self.mu.mem_map(RAM, RAM_SIZE)
        self.mu.mem_map(0xE000E000, 0x1000)  # SCS page
        self.mu.mem_write(base, code)
        self.sp = int.from_bytes(code[0:4], "little")
        reset = syms.get("Reset_Handler")
        if reset is None:
            sys.exit("Reset_Handler missing from symtab")
        # Execute the real startup UP TO the `LDR r0,[pc,#4]; BLX r0` scaffold.
        stop = code.find(b"\x01\x48\x80\x47", (reset & ~1) - base)
        if stop < 0:
            sys.exit("startup call scaffold (LDR r0/BLX r0) not found")
        self.mu.reg_write(UC_ARM_REG_SP, self.sp)
        self.mu.emu_start(reset | 1, base + stop, count=100000)

    def call(self, fn, a, b):
        faddr = self.syms.get(fn)
        if faddr is None:
            return f"ERR:symbol {fn} missing"
        self.mu.reg_write(UC_ARM_REG_SP, self.sp)
        self.mu.reg_write(UC_ARM_REG_LR, RET | 1)
        self.mu.reg_write(UC_ARM_REG_R0, a & 0xFFFFFFFF)
        self.mu.reg_write(UC_ARM_REG_R1, b & 0xFFFFFFFF)
        try:
            self.mu.emu_start(faddr | 1, RET, count=100000)
        except UcError:
            # Distinguish the deterministic §4.4.8 UDF trap from a stray
            # fault (e.g. a BLX to address 0 from a missing null check).
            pc = self.mu.reg_read(UC_ARM_REG_PC)
            lo = pc - self.base
            if 0 <= lo < len(self.code) - 1 and self.code[lo:lo + 2] == b"\x00\xde":
                return "trap:udf"
            return f"ERR:fault pc={pc:#x}"
        return self.mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


def wasmtime_oracle():
    """Ground truth: (export, idx) -> value or 'trap:udf'. The CASES table is
    itself oracle-checked against the §4.4.8 trap reasons, not hand-trusted."""
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, WAT.read_text())
    results = {}
    for export, groups in CASES.items():
        for why, idxs in groups.items():
            for idx in idxs:
                store = wasmtime.Store(engine)  # fresh instance per call
                fn = wasmtime.Instance(store, module, []).exports(store)[export]
                try:
                    results[(export, idx)] = fn(store, X, idx) & 0xFFFFFFFF
                    assert why == "ok", f"{export}({X},{idx}) must trap ({why})"
                except wasmtime.Trap as t:
                    reason = TRAP_REASON[why]
                    assert reason in t.message, (
                        f"{export}({X},{idx}): expected '{reason}', got {t.message}"
                    )
                    results[(export, idx)] = "trap:udf"
    return results


def main() -> int:
    out = "/tmp/ci275_execution.elf"
    compile_synth(out)
    code, base, syms, etype = load(out)
    print("=== #275 self-contained call_indirect EXECUTION differential ===")
    if etype != "ET_EXEC":
        print(f"  [BUG] output is {etype}, not ET_EXEC — not a self-contained image")
        return 1
    img = ImageRunner(code, base, syms)
    gt = wasmtime_oracle()
    fails = 0
    for (export, idx), want in sorted(gt.items()):
        got = img.call(export, X, idx)
        ok = got == want
        fails += 0 if ok else 1
        print(f"  {export}({X},{idx}): wasmtime={want} synth={got} "
              f"{'OK' if ok else 'MISMATCH'}")
    if fails == 0:
        print("ORACLE: PASS — self-contained call_indirect executes + traps "
              "identically to wasmtime (#275)")
        return 0
    print(f"ORACLE: FAIL — {fails} divergence(s) (#275)")
    return 1


if __name__ == "__main__":
    sys.exit(main())
