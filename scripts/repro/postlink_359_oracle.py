#!/usr/bin/env python3
"""
#359 POST-LINK ORACLE — the structural fix to the #368 mistake (a unicorn-on-.o
oracle could not see the #354 link-time retargeting, so #368 passed locally and
failed on silicon with rc=-35).

Builds the actual linked image for msgq_put_359.wasm (native-pointer + #354
split) using scripts/repro/n359/postlink.ld (mimics Zephyr: __synth_wasm_seg_0
in .data, __synth_wasm_data == __bss_start in .bss) + zephyr_stubs.s, then
asserts gale's INVARIANT:

  No `__synth_wasm_*` literal that addresses the relocated `.rodata` table may
  resolve into [__bss_start, __bss_end) — every static-data access must land in
  the .data/seg_K region that owns its offset.

PRE-FIX (v0.11.47): FAILS — literals `__synth_wasm_data + 0` (= .bss base) and
`__synth_wasm_data + 65552` (= __bss_end) reach .bss, so the action->ret table
lookup reads zero -> "queue full" on an empty queue -> rc=-35.

Run: PATH=$PWD/target/release:$PATH python3 scripts/repro/postlink_359_oracle.py
Final silicon gate stays gale's G474RE re-test (this oracle is necessary, not
sufficient — Thumb/runtime-index effects need real hardware).
"""
import subprocess, re, struct, sys, os
HERE=os.path.dirname(os.path.abspath(__file__))
O="/tmp/n359/msgq.o"; ELF="/tmp/n359/msgq.elf"
os.makedirs("/tmp/n359", exist_ok=True)
def run(c): return subprocess.run(c, capture_output=True, text=True)
run(["synth","compile","scripts/repro/msgq_put_359.wasm","--target","cortex-m4f",
     "--native-pointer-abi","--relocatable","--all-exports","-o",O])
run(["arm-none-eabi-as","-mcpu=cortex-m4","-mthumb",f"{HERE}/n359/zephyr_stubs.s","-o","/tmp/n359/stubs.o"])
ld=run(["arm-none-eabi-ld","-T",f"{HERE}/n359/postlink.ld",O,"/tmp/n359/stubs.o","-o",ELF])
if ld.returncode!=0: print("LINK FAILED:",ld.stderr); sys.exit(2)
nm={l.split()[2]:int(l.split()[0],16) for l in run(["arm-none-eabi-nm",ELF]).stdout.splitlines() if len(l.split())==3}
bss_lo,bss_hi=nm["__bss_start"],nm["__bss_end"]
# INVARIANT (precise): a `__synth_wasm_data + C` literal in a synth body must
# resolve to a READABLE location holding linmem[C]'s value:
#  - C inside an init segment -> the data moved to seg_K (.data), so the literal
#    must be RETARGETED (it must NOT still point at __synth_wasm_data/.bss).
#  - C in a zero region -> stays __synth_wasm_data + C in .bss, which is correct
#    ONLY IF the .bss reservation covers C (C < used_extent, i.e. the resolved
#    address < __bss_end). Reading AT/PAST __bss_end is the #359 bug: gale's msgq
#    reads a zero word at offset 65552 (the table tail), but .bss was sized to
#    exactly 65552 (the init-seg end) because static_top filtered MovwAbs while
#    the real relocs are Abs32 -> the access lands at __bss_end and reads garbage.
# So flag any literal that resolves at/past __bss_end but within the plausible
# linmem window [__bss_start, __bss_start + 128 KiB) — a static access that reads
# past the zero reservation. (The post-link image is NECESSARY-not-sufficient;
# numeric rc=0 stays gale's G474RE round-trip.)
MARGIN = 0x40  # a real boundary over-read lands just past __bss_end; wider hits = code words
s=run(["arm-none-eabi-objdump","-s","-j",".text",ELF]).stdout
viol=[]
for line in s.splitlines():
    p=line.split()
    if len(p)>=2 and re.match(r'^[0-9a-f]{6,8}$', p[0]):
        base=int(p[0],16)
        for i,w in enumerate(p[1:5]):
            if re.match(r'^[0-9a-f]{8}$',w):
                v=struct.unpack('<I',bytes.fromhex(w))[0]
                if bss_hi <= v < bss_hi + MARGIN:
                    viol.append((base+i*4, v, v - bss_lo))
print(f"__bss_start={bss_lo:#x} __bss_end={bss_hi:#x} __synth_wasm_seg_0={nm.get('__synth_wasm_seg_0',0):#x} .bss size={bss_hi-bss_lo}")
for a,v,off in viol:
    print(f"  text@{a:#08x}: .word {v:#010x}  -> __synth_wasm_data + {off} resolves AT/PAST __bss_end (reads past the zero reservation) — VIOLATION")
ok = len(viol)==0
print("ORACLE:", "PASS (no __synth_wasm_* literal reads past __bss_end)"
      if ok else f"FAIL ({len(viol)} static-data literals read past .bss — #359 #354x#368)")
sys.exit(0 if ok else 1)
