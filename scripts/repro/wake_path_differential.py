#!/usr/bin/env python3
"""
#204 WAKE-path differential harness (gale's binary semaphore).

Compares synth's compiled `z_impl_k_sem_give` against the WASM semantics
(wasmtime as the oracle) for both the no-waiter (increment) and waiter (WAKE)
paths — the WAKE path can't be exercised on hardware because the debugger
perturbs the give/take race (gale's heisenbug).

Setup:
    python3 -m venv /tmp/armv
    /tmp/armv/bin/pip install unicorn capstone wasmtime
    # fetch gale's gist to /tmp/merged.wat:
    curl -sL https://api.github.com/gists/d30f965ac96b8ca4cac7d4fea2832a6a \
      | python3 -c "import sys,json;print(json.load(sys.stdin)['files']['merged.both.loom.wat']['content'])" \
      > /tmp/merged.wat
    # compile for gale's target (Thumb-2 — NOT the default --target arm!):
    synth compile /tmp/merged.wat --target cortex-m4 --relocatable -o /tmp/gz_m4.elf

Run:
    /tmp/armv/bin/python3 scripts/repro/wake_path_differential.py

Key gotcha: synth's default `--target arm` emits ARM/A32 and its encoder drops
the register index on indexed loads/stores (#206). gale builds Thumb-2
(cortex-m4); the harness runs UC_MODE_THUMB to match. Disassemble with capstone
THUMB mode, not `synth disasm` (which decodes as ARM).
"""
import struct
from unicorn import *
from unicorn.arm_const import *
from capstone import *
import wasmtime

WAT = "/tmp/merged.wat"
ELF = "/tmp/gz_m4.elf"
THREAD = 0x5000  # fake pended-waiter pointer for the WAKE scenario


def oracle(thread):
    eng = wasmtime.Engine(); store = wasmtime.Store(eng)
    mod = wasmtime.Module.from_file(eng, WAT); calls = []
    i32 = wasmtime.ValType.i32()
    ft0 = wasmtime.FuncType([i32], [i32]); ft1 = wasmtime.FuncType([i32, i32], [])
    ft2 = wasmtime.FuncType([i32], []); ft3 = wasmtime.FuncType([i32, i32], [i32])
    imp = [wasmtime.Func(store, ft0, lambda x: (calls.append("k_spin_lock") or 0x400)),
           wasmtime.Func(store, ft0, lambda x: (calls.append("z_unpend") or thread)),
           wasmtime.Func(store, ft1, lambda t, v: calls.append("arch_ret")),
           wasmtime.Func(store, ft2, lambda t: calls.append("z_ready_thread")),
           wasmtime.Func(store, ft3, lambda k, a: (calls.append("z_reschedule") or 0))]
    inst = wasmtime.Instance(store, mod, imp); mem = inst.exports(store)["memory"]
    mem.write(store, (0).to_bytes(4, "little"), 0x100)
    mem.write(store, (1).to_bytes(4, "little"), 0x104)
    inst.exports(store)["z_impl_k_sem_give"](store, 0x100)
    return calls, int.from_bytes(mem.read(store, 0x100, 0x104), "little")


def synth(thread):
    d = open(ELF, "rb").read()
    so = struct.unpack_from("<I", d, 0x20)[0]; n = struct.unpack_from("<H", d, 0x30)[0]
    sx = struct.unpack_from("<H", d, 0x32)[0]
    secs = [struct.unpack_from("<IIIIIIIIII", d, so + i * 0x28) for i in range(n)]
    shstr = secs[sx][4]

    def nm(x):
        e = d.index(b"\0", shstr + x); return d[shstr + x:e].decode()
    S = {nm(s[0]): s for s in secs}
    code = d[S[".text"][4]:S[".text"][4] + S[".text"][5]]
    rel = S[".rel.text"]
    relofs = sorted(struct.unpack_from("<II", d, rel[4] + i * 8)[0] for i in range(rel[5] // 8))
    NM = dict(zip(relofs, ["k_spin_lock", "z_unpend", "arch_ret", "z_ready_thread", "z_reschedule"]))
    md = Cs(CS_ARCH_ARM, CS_MODE_THUMB); md.skipdata = True
    pushes = [i.address for i in md.disasm(code, 0) if i.mnemonic.startswith("push")]
    zimpl = max(p for p in pushes if p < relofs[0])
    CODE = 0x10000; LIN = 0x40000; SEM = 0x100
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    for b in (CODE, 0x20000, LIN):
        mu.mem_map(b, 0x10000)
    mu.mem_write(CODE, code)
    mu.mem_write(LIN + SEM, (0).to_bytes(4, "little"))
    mu.mem_write(LIN + SEM + 4, (1).to_bytes(4, "little"))
    mu.reg_write(UC_ARM_REG_SP, 0x28000); mu.reg_write(UC_ARM_REG_R11, LIN)
    mu.reg_write(UC_ARM_REG_R0, SEM); mu.reg_write(UC_ARM_REG_LR, 0x15000 | 1)
    calls = []

    def ch(mu, a, s, u):
        o = a - CODE
        if o in NM:
            calls.append(NM[o])
            mu.reg_write(UC_ARM_REG_R0, thread if NM[o] == "z_unpend" else 0)
            mu.reg_write(UC_ARM_REG_PC, (a + 4) | 1)
    mu.hook_add(UC_HOOK_CODE, ch)
    try:
        mu.emu_start((CODE + zimpl) | 1, 0x15000, count=8000)
    except UcError as e:
        calls.append(f"ERR:{e}")
    return calls, int.from_bytes(mu.mem_read(LIN + SEM, 4), "little")


for label, thread in [("NO-WAITER", 0), ("WAITER", THREAD)]:
    oc, ocnt = oracle(thread); sc, scnt = synth(thread)
    print(f"{label}:")
    print(f"  wasm oracle: count={ocnt} calls={oc}")
    print(f"  synth ARM  : count={scnt} calls={sc}")
    print(f"  {'MATCH' if (oc == sc and ocnt == scnt) else 'MISMATCH <<< synth miscompiles this path'}")
