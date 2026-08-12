#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 9
"""#953 (SECURITY) — rv32 `(memory 0)` got a 65532-byte bounds guard.

`--safety-bounds software` is the mode whose entire purpose is to make every
out-of-bounds access trap. On v0.56.0, a module declaring `(memory 0)` got a
bound baked at **65532** — byte-for-byte the guard of a 1-page module — so every
address in `0..=65532` passed the check and the access was performed against a
memory with no bytes at all. Reads AND writes:

    lui  t1, 0x10          ; 65536
    addi t1, t1, -0x4      ; 65532   <- bound for a ZERO-byte memory
    bltu t1, t0, ...       ; trap only if 65532 < addr

ROOT CAUSE: `0` used as both a value and a sentinel.
`config.linear_memory_bytes == 0` meant "unset — a hand-built driver with no
module context, fall back to 1 page" AND is exactly what `(memory 0)` produces.
The two were indistinguishable.

This is the same disease as #932 (fixed one release earlier) running the other
way: there `unwrap_or(0)` turned "no floor establishable" into "the floor is 0
bytes" and STRIPPED guards; here `0` meant "unset" and INVENTED one.

# What this oracle asserts, and why it is shaped this way

wasmtime is the reference: it traps on every access to a zero-byte memory. The
compiled function must do the same. A trap is observed as a unicorn `ebreak`
intercept, NOT as "the value came back wrong" — a wrong-value check would pass
vacuously if the function returned 0 for an unrelated reason.

The 65536 vector is the NON-VACUITY control: it was already trapping before the
fix, so if it ever stops trapping the fixture has broken in a way that would
make the other vectors meaningless.
"""

import struct
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_RISCV, UC_HOOK_INTR, UC_MODE_RISCV32, Uc, UcError
from unicorn.riscv_const import UC_RISCV_REG_A0, UC_RISCV_REG_RA, UC_RISCV_REG_S11, UC_RISCV_REG_SP

WAT = "scripts/repro/rv32_zero_memory_953.wat"
ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/z953.o"

CODE, LIN, RET = 0x100000, 0x40000, 0x200000

# (export, address). Every one must TRAP: the memory has zero bytes.
#   0      — the friendliest possible address; accepted pre-fix.
#   65528  — last aligned address inside the INVENTED 65532 bound; accepted.
#   65536  — past the invented bound; already trapped pre-fix (the control).
VECTORS = [
    ("ld", 0),
    ("ld", 65528),
    ("ld", 65536),
    ("st", 0),
    ("st", 65528),
    ("st", 65536),
    ("ld8", 0),
    ("ld8", 65531),
    ("ld8", 65536),
]


def symbols(path):
    with open(path, "rb") as fh:
        f = ELFFile(fh)
        st = f.get_section_by_name(".symtab")
        syms = {
            s.name: s["st_value"]
            for s in st.iter_symbols()
            if s.name and s["st_info"]["type"] == "STT_FUNC"
        }
        return syms, f.get_section_by_name(".text").data()


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, WAT)

    def wasmtime_traps(name, addr):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        try:
            inst.exports(store)[name](store, addr)
            return False
        except Exception:
            return True

    syms, code = symbols(ELF)

    def synth_traps(name, addr):
        """True if the compiled function traps (ebreak) at this address."""
        entry = syms.get(name)
        if entry is None:
            return None  # function skipped — a decline, not a trap
        mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
        for base, size in [(CODE, 0x20000), (LIN, 0x20000), (0x88000, 0x10000), (RET, 0x1000)]:
            mu.mem_map(base, size)
        mu.mem_write(CODE, code)
        mu.reg_write(UC_RISCV_REG_SP, 0x90000)
        mu.reg_write(UC_RISCV_REG_S11, LIN)
        mu.reg_write(UC_RISCV_REG_A0, addr & 0xFFFFFFFF)
        mu.reg_write(UC_RISCV_REG_RA, RET)
        trapped = []
        mu.hook_add(UC_HOOK_INTR, lambda *_: trapped.append(True))
        try:
            mu.emu_start(CODE + entry, RET, count=4000)
        except UcError:
            # A fault reaching unicorn is also a refusal to perform the access.
            return True
        return bool(trapped)

    fails = executed = 0
    for name, addr in VECTORS:
        want = wasmtime_traps(name, addr)
        got = synth_traps(name, addr)
        if got is None:
            print(f"  {name}({addr}): SYMBOL MISSING — function skipped, not trapped")
            fails += 1
            continue
        executed += 1
        ok = got == want
        fails += 0 if ok else 1
        print(
            f"  {name}({addr}): synth_traps={got}  wasmtime_traps={want}  "
            f"{'OK' if ok else '*** ACCESS PERFORMED ON A ZERO-BYTE MEMORY ***'}"
        )

    print(f"\n#953 EMULATIONS={executed}/{len(VECTORS)}")
    if executed != len(VECTORS):
        print(f"FAIL: only {executed} of {len(VECTORS)} vectors reached the emulator")
        sys.exit(1)
    print(
        "RESULT: PASS — every access to a zero-byte memory traps, matching wasmtime"
        if not fails
        else f"FAIL: {fails} vector(s) disagree with wasmtime"
    )
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
