#!/usr/bin/env python3
"""#846 gpio-thin size-regression gate — SIZE drop + execution-UNCHANGED.

gale's `gpio-thin` gust driver regressed +44 B / +9% (490→534 `.text`) on synth
0.49: its pin bit-arithmetic (`pin & 0xf` / `pin & 31` then a register shift)
emits the source mask `and rN,#0x1f` IMMEDIATELY followed by the #682 mod-32
re-mask `and r12,rN,#0x1f`, and that second mask is provably redundant (the
operand is already in-range). The #686 `elide_shift_masks` Pattern B drops it;
v0.50.0 flips that pass DEFAULT-ON (`SYNTH_SHIFT_MASK_ELIDE=0` opts out).

This gate asserts BOTH halves of the fix on gale's REAL loom.wasm (pinned as
`gpio_thin_846.loom.wasm`, decoded from the issue), never a synthetic (#757):

  (a) SIZE: default (flag-on) `.text` < opt-out (flag-off) `.text`, and the
      redundant `and r12,#0x1f` count strictly drops. (Both compiled here.)
  (b) EXECUTION UNCHANGED: for a pin sweep that INCLUDES pin >= 32 (the mod-32
      boundary a wrongly-elided mask would corrupt), the captured
      mmio_write32 (addr,value) call sequence AND every mmio_read32-consuming
      return value are BIT-IDENTICAL between:
        - wasmtime (ground truth, imports trampolined to a fake MMIO), and
        - unicorn running synth's flag-ON ARM (BL to the unresolved
          mmio_write32/read32 imports hooked to the same fake MMIO).
      A size fix that changed behavior would be a miscompile; this is the
      whole point of the issue (effects identical, verified by gale's Renode
      content-gate).

Deps: wasmtime unicorn pyelftools capstone.
Run:
  SYNTH=./target/debug/synth python3 scripts/repro/gpio_thin_846_differential.py
Exits nonzero on any size or execution mismatch.
"""
import os
import struct
import subprocess
import sys
import tempfile

import wasmtime
from capstone import CS_ARCH_ARM, CS_MODE_THUMB, Cs
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_HOOK_CODE, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

SYNTH = os.environ.get("SYNTH", "./target/release/synth")
HERE = os.path.dirname(os.path.abspath(__file__))
WASM = os.path.join(HERE, "gpio_thin_846.loom.wasm")

# Fake MMIO peripheral: a flat dict addr -> u32. mmio_write32 stores,
# mmio_read32 returns whatever was last written (default 0). A deterministic
# non-zero seed exercises the read-modify-write drivers (clear/toggle/config).
BASE_ADDR = 0x40020000
SEED = {BASE_ADDR + 0x10: 0xA5A50F0F}  # ODR-ish register some drivers read

# Pin sweep: crucially includes >= 32 (mod-32 boundary), the wrap the mask
# guards. Also a spread of the `& 0xf` (config) domain and typical GPIO pins.
PINS = [0, 1, 5, 7, 8, 15, 16, 31, 32, 33, 47, 63, 100, 255, 0x7FFFFFFF]


def compile_elf(flag_off, out):
    env = dict(os.environ)
    if flag_off:
        env["SYNTH_SHIFT_MASK_ELIDE"] = "0"
    else:
        env.pop("SYNTH_SHIFT_MASK_ELIDE", None)  # default = ON
    subprocess.run(
        [SYNTH, "compile", WASM, "-o", out,
         "--target", "cortex-m3", "--all-exports", "--relocatable"],
        env=env, check=True, capture_output=True,
    )


def text_size_and_masks(elf):
    """(.text length, count of `and r12,rN,#0x1f` mod-32 masks) from the ELF."""
    with open(elf, "rb") as fh:
        e = ELFFile(fh)
        text = e.get_section_by_name(".text")
        code, base = text.data(), text["sh_addr"]
    md = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    masks = 0
    for ins in md.disasm(bytes(code), base):
        # capstone renders R12 as its alias `ip`; match either spelling.
        rd = ins.op_str.split(",", 1)[0].strip()
        if (ins.mnemonic.startswith("and") and rd in ("r12", "ip")
                and "#0x1f" in ins.op_str):
            masks += 1
    return len(code), masks


def elf_syms_text(path):
    with open(path, "rb") as fh:
        elf = ELFFile(fh)
        symtab = next(
            (s for s in elf.iter_sections() if s["sh_type"] == "SHT_SYMTAB"), None)
        if symtab is None:
            sys.exit(f"no SHT_SYMTAB in {path}")
        syms = {s.name: s["st_value"] & ~1
                for s in symtab.iter_symbols()
                if s.name and s["st_info"]["type"] == "STT_FUNC"}
        text = elf.get_section_by_name(".text")
        return syms, text.data(), text["sh_addr"]


# --- wasmtime ground truth: run one export, capture the mmio trace + return ---
def wasmtime_trace(export, args):
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(WASM, "rb").read())
    store = wasmtime.Store(engine)
    trace = []
    state = dict(SEED)

    def mmio_write32(addr, val):
        trace.append(("w", addr & 0xFFFFFFFF, val & 0xFFFFFFFF))
        state[addr & 0xFFFFFFFF] = val & 0xFFFFFFFF

    def mmio_read32(addr):
        v = state.get(addr & 0xFFFFFFFF, 0)
        trace.append(("r", addr & 0xFFFFFFFF, v))
        return v

    ft_w = wasmtime.FuncType([wasmtime.ValType.i32(), wasmtime.ValType.i32()], [])
    ft_r = wasmtime.FuncType([wasmtime.ValType.i32()], [wasmtime.ValType.i32()])
    imports = [
        wasmtime.Func(store, ft_w, mmio_write32),
        wasmtime.Func(store, ft_r, mmio_read32),
    ]
    inst = wasmtime.Instance(store, module, imports)
    fn = inst.exports(store)[export]
    ret = fn(store, *args)
    ret = (ret & 0xFFFFFFFF) if isinstance(ret, int) else None
    return trace, ret


# --- unicorn: run synth's ARM for one export, same fake MMIO via BL hooks ---
CODE, LIN, STK = 0x100000, 0x40000, 0x90000
RET = 0x9F00 | 1


def unicorn_trace(syms, code, base, export, idx, args, wpc, rpc):
    trace = []
    state = dict(SEED)
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(LIN, 0x20000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_write(CODE, code)

    entry = None
    for cand in (export, f"func_{idx}"):
        if cand in syms:
            entry = syms[cand]
            break
    if entry is None:
        sys.exit(f"SYMBOL MISSING: {export}; symtab has {sorted(syms)}")

    # Args in r0.., linmem base in r11.
    regs = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2]
    for r, v in zip(regs, args):
        mu.reg_write(r, v & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, LIN)
    mu.reg_write(UC_ARM_REG_LR, RET)

    # BL to an import lands on the (unresolved, addend -4) placeholder; its
    # target after relocation would be mmio_write32/read32. We identify the
    # call by the reloc'd symbol via the ELF: the BL site PC is whatever the
    # placeholder points at. Simpler + robust: hook every `bl`/`blx` and
    # decide by which import symbol the reloc names at that offset.
    def do_write(mu):
        addr = mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
        val = mu.reg_read(UC_ARM_REG_R1) & 0xFFFFFFFF
        trace.append(("w", addr, val))
        state[addr] = val

    def do_read(mu):
        addr = mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
        v = state.get(addr, 0)
        trace.append(("r", addr, v))
        mu.reg_write(UC_ARM_REG_R0, v)

    def hook(mu, a, sz, u):
        off = a - CODE
        if off in wpc:
            do_write(mu)
            mu.reg_write(UC_ARM_REG_PC, ((a + sz) | 1))  # return past the BL
        elif off in rpc:
            do_read(mu)
            mu.reg_write(UC_ARM_REG_PC, ((a + sz) | 1))
    mu.hook_add(UC_HOOK_CODE, hook)

    try:
        mu.emu_start((CODE + entry - base) | 1, RET & ~1, count=4000)
        ret = mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
    except UcError as e:
        return trace, f"ERR:{e}"
    return trace, ret


def import_call_sites(elf_path, base):
    """Map each `bl`-to-import call-site .text offset -> 'w'|'r' via relocs.

    synth's relocatable ELF carries R_ARM_THM_CALL relocations naming the
    import symbol (mmio_write32 / mmio_read32) at each BL site. We return the
    sets of .text offsets that call write vs read.
    """
    wpc, rpc = set(), set()
    with open(elf_path, "rb") as fh:
        elf = ELFFile(fh)
        symtab = next((s for s in elf.iter_sections()
                       if s["sh_type"] == "SHT_SYMTAB"), None)
        symnames = [s.name for s in symtab.iter_symbols()]
        for sec in elf.iter_sections():
            if sec["sh_type"] not in ("SHT_REL", "SHT_RELA"):
                continue
            # Only relocations against .text.
            for reloc in sec.iter_relocations():
                symidx = reloc["r_info_sym"]
                name = symnames[symidx] if symidx < len(symnames) else ""
                off = reloc["r_offset"]
                if name == "mmio_write32":
                    wpc.add(off)
                elif name == "mmio_read32":
                    rpc.add(off)
    return wpc, rpc


EXPORTS = [
    ("gpio_clear", 2, lambda pin: (BASE_ADDR, pin)),
    ("gpio_read", 4, lambda pin: (BASE_ADDR, pin)),
    ("gpio_set", 5, lambda pin: (BASE_ADDR, pin)),
    ("gpio_toggle", 6, lambda pin: (BASE_ADDR, pin)),
    ("gpio_configure", 3, lambda pin: (BASE_ADDR, pin, 0x3)),
]


def main():
    tmp = tempfile.mkdtemp()
    elf_on = os.path.join(tmp, "gpio_on.elf")
    elf_off = os.path.join(tmp, "gpio_off.elf")
    compile_elf(flag_off=False, out=elf_on)
    compile_elf(flag_off=True, out=elf_off)

    # (a) SIZE half.
    on_len, on_masks = text_size_and_masks(elf_on)
    off_len, off_masks = text_size_and_masks(elf_off)
    print("=== #846 SIZE ===")
    print(f"  flag-OFF (SYNTH_SHIFT_MASK_ELIDE=0): .text={off_len} B  "
          f"redundant `and r12,#0x1f` masks={off_masks}")
    print(f"  flag-ON  (default v0.50.0)         : .text={on_len} B  "
          f"redundant `and r12,#0x1f` masks={on_masks}")
    print(f"  recovered: {off_len - on_len} B  ({off_masks - on_masks} masks elided)")
    size_ok = on_len < off_len and on_masks < off_masks
    if not size_ok:
        print("  SIZE: FAIL (default did not shrink .text / mask count)")

    # (b) EXECUTION half — on the flag-ON bytes, across the pin sweep incl >=32.
    syms, code, base = elf_syms_text(elf_on)
    wpc, rpc = import_call_sites(elf_on, base)
    print("=== #846 EXECUTION UNCHANGED (flag-ON bytes vs wasmtime) ===")
    exec_ok = True
    checks = 0
    for export, idx, mkargs in EXPORTS:
        for pin in PINS:
            args = mkargs(pin)
            gt_trace, gt_ret = wasmtime_trace(export, args)
            un_trace, un_ret = unicorn_trace(
                syms, code, base, export, idx, args, wpc, rpc)
            ok = (gt_trace == un_trace) and (gt_ret == un_ret
                                             if gt_ret is not None else True)
            checks += 1
            if not ok:
                exec_ok = False
                print(f"  MISMATCH {export}(pin={pin}):")
                print(f"    wasmtime trace={gt_trace} ret={gt_ret}")
                print(f"    unicorn  trace={un_trace} ret={un_ret}")
    if exec_ok:
        print(f"  {checks}/{checks} match — mmio (addr,value) sequences + returns "
              f"bit-identical across pins {PINS} (incl. >=32 mod-32 boundary)")

    print("=== RESULT ===")
    ok = size_ok and exec_ok
    print("gpio-thin #846: PASS" if ok else "gpio-thin #846: FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
