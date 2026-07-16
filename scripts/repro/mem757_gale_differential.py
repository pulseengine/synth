#!/usr/bin/env python3
"""#757 — gale's exact fused os-tl node (the real miscompile, not a reconstruction).

`mem757_gale/loom.wasm` (md5 18da000d9142dfa0885f57578d3af150) is the meld-fused +
loom-inlined `gust:os {time,log}` node. It declares THREE active data segments ALL
at wasm linear-memory offset 0x100000 — legal WASM, where a LATER active segment
OVERWRITES an earlier one. The last (seg_2, 24 B) owns those bytes at runtime and
holds `"gust:os up\\n"` at linmem 0x100008.

The bug (silent miscompile, byte-identical across 0.43.0/0.43.1/0.44.0/0.45.0):
the #354 mixed-split reloc retargeting picked the FIRST segment whose wasm-offset
range contains an access address (`.position()`), so the string source at 0x100008
bound to `__synth_wasm_seg_0 + 8` (seg_0's stale const 0x02) instead of
`__synth_wasm_seg_2 + 8` (the string). gale's runtime: got=[2,0,0,0,1,0,0,32,...]
instead of "gust:os up\\n". Fix: resolve overlapping addresses to the LAST-declared
owning segment (`.rposition()`), matching WASM overwrite semantics.

THE ORACLE (non-vacuous, no execution needed — a reloc that reads the wrong byte
IS the miscompile): reconstruct the runtime linear-memory image (apply loom.wasm's
data segments in declaration order, later-wins), compile with synth, then for EVERY
static-data reloc assert the byte it resolves to in the packed .data equals the
byte that address holds in the runtime image. A single mismatch (the seg_0+8 case)
fails. This is the ground-truth #757 regression gate — synthetic reconstructions
provably do NOT reproduce it (synth PR #772: 7 shapes all green), so the real
module must live in CI.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WASM = os.path.join(HERE, "mem757_gale", "loom.wasm")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

try:
    from elftools.elf.elffile import ELFFile
except ImportError:
    print("FAIL: pyelftools required (pip install pyelftools)")
    sys.exit(1)


def uleb(d, i):
    r = s = 0
    while True:
        b = d[i]
        i += 1
        r |= (b & 0x7F) << s
        if not b & 0x80:
            return r, i
        s += 7


def wasm_data_segments(wasm):
    """Return [(linmem_off, bytes)] for active data segments, in declaration order."""
    p = 8
    segs = []
    while p < len(wasm):
        sid = wasm[p]
        p += 1
        sz, p = uleb(wasm, p)
        end = p + sz
        if sid == 11:  # data section
            n, q = uleb(wasm, p)
            for _ in range(n):
                flags, q = uleb(wasm, q)
                off = 0
                if flags in (0, 2):
                    if flags == 2:
                        _memidx, q = uleb(wasm, q)
                    assert wasm[q] == 0x41  # i32.const
                    q += 1
                    off, q = uleb(wasm, q)
                    assert wasm[q] == 0x0B  # end
                    q += 1
                ln, q = uleb(wasm, q)
                segs.append((off, wasm[q : q + ln]))
                q += ln
            return segs
        p = end
    return segs


def build_runtime_linmem(segs):
    """Apply active segments in order (later overwrites earlier) — the truth."""
    mem = {}
    for off, data in segs:
        for j, b in enumerate(data):
            mem[off + j] = b
    return mem


def main():
    if not os.path.exists(WASM):
        print(f"FAIL: {WASM} missing")
        return 1
    wasm = open(WASM, "rb").read()
    segs = wasm_data_segments(wasm)
    runtime = build_runtime_linmem(segs)
    print(f"loom.wasm: {len(segs)} data segments; "
          f"{sum(1 for a,b in [(s[0],s[0]+len(s[1])) for s in segs] for _ in [0])} "
          f"— overlapping at 0x{segs[0][0]:x}" if segs else "no segments")

    out = "/tmp/mem757_gale_oracle.o"
    r = subprocess.run(
        [SYNTH, "compile", WASM, "--target", "cortex-m3", "--all-exports",
         "--relocatable", "--native-pointer-abi", "--shadow-stack-size", "2048",
         "-o", out],
        capture_output=True, text=True)
    if r.returncode != 0:
        print("FAIL: compile failed\n" + r.stderr[-500:])
        return 1

    elf = ELFFile(open(out, "rb"))
    raw = open(out, "rb").read()
    txt = elf.get_section_by_name(".text")
    tbase = txt["sh_offset"]
    dsec = elf.get_section_by_name(".data")
    ddata = dsec.data() if dsec else b""

    # packed offset of each __synth_wasm_seg_K within .data (declaration order,
    # each 4-aligned) — mirrors main.rs mixed_layout.
    packed = []
    cur = 0
    for _off, d in segs:
        cur = (cur + 3) & ~3
        packed.append(cur)
        cur += len(d)

    mismatches = []
    for sec in elf.iter_sections():
        if sec.header["sh_type"] == "SHT_REL" and ".text" in sec.name:
            symtab = elf.get_section(sec["sh_link"])
            for rel in sec.iter_relocations():
                if rel["r_info_type"] != 2:  # R_ARM_ABS32
                    continue
                sym = symtab.get_symbol(rel["r_info_sym"]).name
                if not sym.startswith("__synth_wasm_seg_"):
                    continue
                k = int(sym.rsplit("_", 1)[1])
                off = rel["r_offset"]
                addend = int.from_bytes(raw[tbase + off:tbase + off + 4], "little")
                # runtime linmem address this reloc reads:
                linmem_addr = segs[k][0] + addend
                # byte the packed .data actually serves:
                packed_byte = ddata[packed[k] + addend] if packed[k] + addend < len(ddata) else None
                truth = runtime.get(linmem_addr)
                if truth is not None and packed_byte is not None and packed_byte != truth:
                    mismatches.append(
                        (sym, addend, linmem_addr, packed_byte, truth))

    if mismatches:
        print("ORACLE: FAIL — static-data reloc reads the wrong (stale-segment) byte:")
        for sym, add, la, got, exp in mismatches[:6]:
            print(f"  {sym}+0x{add:x} -> linmem 0x{la:x}: reads 0x{got:02x}, "
                  f"runtime owns 0x{exp:02x} ('{chr(exp) if 32<=exp<127 else '.'}')")
        print("  This is #757: an overlapping-segment address bound to the wrong "
              "(earlier) segment. gale's got=[2,0,0,0,...] = seg_0+8.")
        return 1

    # positive: confirm the string is readable via its source reloc
    print("ORACLE: PASS — every static-data reloc reads the runtime-correct byte "
          "(overlapping segments resolve to the last-declared owner). #757 fixed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
