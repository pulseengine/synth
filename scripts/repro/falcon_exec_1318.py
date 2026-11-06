#!/usr/bin/env python3
# ci-status: manual (external-input) — needs the reporter's opt.wasm from the #1318 attachment errors.zip (https://github.com/user-attachments/files/32349478/errors.zip, 24,368 bytes; opt.wasm sha256 7065f112fdaae127291f5f12cacc00619c55363e14a5141059dc2fcc6cfd00df), which is not vendored in this tree and whose every re-fetch needs the maintainer's approval; the defect classes it executes are gated in CI by vfp_high_bank_restore_1318_differential.py, float_local_zero_init_1594_differential.py and vfp_wide_stage_1593_differential.py (all wired).
# ci-checks: emulations >= 2204
"""RQ-90-FALCON7 (#1318) — the reporter's `opt.wasm`, compiled with the
reporter's own command and EXECUTED under unicorn against wasmtime.

WHY THIS FILE EXISTS. v0.89 delivered #1318 (PRs #1585, #1595, #1596, #1600)
and measured the reporter's module running bit-identical to wasmtime — `step`
1000 of 1000 on a garbage and on a zeroed stack, `configure` 42 of 42,
`cabi_realloc` 60 of 60 — with an old-object positive control at 334 of 1000.
That harness (`falcon_exec.py`) lived in a sandbox and was never committed, so
the figure could not be re-derived from the tree (v0.89 cold review, U1). This
is its committed replacement, written fresh: the v0.89 script is gone, so the
VECTORS here are this file's own (seeded, deterministic), not a recovery of
v0.89's. The call COUNTS are the same; which calls trap may differ.

THE INPUT IS NOT IN THE TREE, ON PURPOSE. It is the reporter's module, from the
issue attachment:

    URL      https://github.com/user-attachments/files/32349478/errors.zip
    size     24,368 bytes (contains opt.wasm and fused.wasm)
    errors.zip sha256 0f796616d5d7ec01dce21a32cb78d40240da778e04d64e32ee7e26c6d51184a1
    opt.wasm   sha256 7065f112fdaae127291f5f12cacc00619c55363e14a5141059dc2fcc6cfd00df
    fused.wasm sha256 21e7a893b93ef47138e99639b53f356ddd51da31a4f50c6a4ee7950470a20bef

The harness takes the module PATH as an argument and refuses (rc 2) unless its
sha256 is the one above. Treat the archive as untrusted: unzip it into a new,
empty directory and run nothing from it natively — this script only hands the
bytes to wasmtime (the reference) and executes the compiled ARM object under
unicorn.

WHAT IT DOES
  1. compile `opt.wasm` with the reporter's command line:
       synth compile opt.wasm --target cortex-m7 --relocatable --all-exports
             --embedder-data-init --embedder-global-init
     rc 0 and no skipped function are required (17 of 17).
  2. link: `arm-none-eabi-ld -Ttext=0` against the stock hard-float libgcc
     (`arm-none-eabi-gcc -mthumb -mcpu=cortex-m7 -mfpu=fpv5-sp-d16
     -mfloat-abi=hard -print-libgcc-file-name`, thumb/v7e-m+fp/hard), which
     supplies the `__aeabi_f2lz`/`__aeabi_l2f` the object imports.
  3. run, as the embedder in docs/embedder-abi-relocatable-arm.md: R11 = linear
     memory, R10 = its size in bytes (64 KiB), R9 = the dense globals table, the
     active data segments applied and the globals seeded at reset (the two
     `--embedder-*-init` obligations). The reset image is first checked equal to
     wasmtime's freshly instantiated memory.
  4. for each MACHINE STATE — GARBAGE (random caller-saved R0..R3/R12/S0..S15,
     random callee-saved R4..R8/S16..S31, a random-filled stack) and ZEROED —
     execute, each call against wasmtime on the same inputs:
       configure  42 calls, nine f32 arguments each, every call on a fresh
                  instance (the module refuses a second configure by spinning);
       cabi_realloc_wit_bindgen_0_41_0
                  60 calls on one instance, a bump arena that ends in traps when
                  it is exhausted — a trap must trap on BOTH sides (UDF here);
       step       1000 calls in 20 episodes of 50, each episode on a fresh
                  instance: even episodes UNCONFIGURED, odd ones after one
                  configure with seeded gains (both paths are real — the
                  d4c0b232 control fails every unconfigured call, but only about
                  one configured call in ten). Each call gets a fresh input
                  record of the module's 100-byte layout written at linear
                  address INPUT (the ABI's indirect parameter).
     Before every call the ARM machine's linear memory and globals are set equal
     to wasmtime's (globals read through export entries this script appends to
     the module — appending exports changes no function), so each call is judged
     on its own: one wrong call does not cascade into the next.
     A call MATCHES when: both sides return the same value, or both trap; all
     65536 bytes of linear memory are equal (an aligned word where both sides
     hold a NaN counts equal — wasm leaves NaN payloads nondeterministic — and
     each such word is counted and printed); every global is equal; and the
     AAPCS contract held on the ARM side (SP, R4..R11, S16..S31 restored, nothing
     written into the caller's stack above SP).
  5. exit 0 only if every call matched; rc 1 on any mismatch or when the
     compiler refuses or skips a function; rc 2 on a setup failure (wrong
     digest, missing tool, link failure, a reference that cannot finish).

THE NUMBERS IT RE-DERIVES (RQ-90-FALCON7). MEASURED 2026-11-06 on synth 0.89.2
built from origin/main c20d37b2 (object sha256 3877c047...6f2310), wasmtime-py
48.0.0, unicorn 2.1.4, arm-none-eabi-gcc 13.2.1's thumb/v7e-m+fp/hard libgcc:
in BOTH machine states configure 42 of 42, cabi_realloc 60 of 60 (21 of them
traps on both sides) and step 1000 of 1000; 2204 of 2204 calls, 0 NaN-payload
words tolerated, rc 0. The v0.89 figures were 1000/1000 twice, 42/42 and 60/60
(49 ok + 11 traps) on 0.89.0's object (db26e1d9...); the counts are the same,
the object differs because v0.89.1/v0.89.2 changed the compiler since, and the
trap split differs because the vectors are this file's own.

POSITIVE CONTROLS, same command, same seed, `--synth` pointed at a binary built
from an older commit (rc 1 both):
  d4c0b232 (after #1585, before #1593/#1594/#1600; the commit v0.89 used, where
            it measured 334 of 1000): step 0 of 1000 in both states — 980
            UC_ERR_WRITE_UNMAPPED faults plus 20 wrong-memory calls, each
            state. v0.89's 334 came from vectors this file does not have.
  ce348045 (#1593 fixed, #1594 not): step 991 of 1000 on the GARBAGE machine,
            1000 of 1000 on the zeroed one — the float local read before
            written that #1594 zeroes, visible only with garbage in the frame
            (v0.89 measured 32 of 1000 at the same point with its vectors).
configure and cabi_realloc match at both control commits: the defects were in
step.

Run (local; needs wasmtime, unicorn, pyelftools, arm-none-eabi-ld/gcc). Fetch
ONLY with the maintainer's approval, into a new empty directory, and check the
archive digest before unzipping:
  mkdir /path/to/new-empty-dir && cd /path/to/new-empty-dir
  curl -sSLo errors.zip https://github.com/user-attachments/files/32349478/errors.zip
  shasum -a 256 errors.zip    # 0f796616...184a1, as above
  unzip errors.zip
  cd <synth checkout> && cargo build -p synth-cli --bin synth
  python3 -I scripts/oracle_run.py scripts/repro/falcon_exec_1318.py \\
      /path/to/new-empty-dir/opt.wasm --synth ./target/debug/synth
(oracle_run.py enforces the `ci-checks: emulations >= 2204` floor; the script
also runs on its own: `python3 -I scripts/repro/falcon_exec_1318.py <opt.wasm>
--synth <synth>`.)

WHY CI DOES NOT RUN IT. Every re-fetch of the attachment needs the maintainer's
approval (RQ-89-FALCON6), so a job that fetched it per run would be a standing
unapproved re-fetch, and the module is the reporter's, so it is not vendored.
The defect classes this executes are gated in CI on in-tree fixtures by
vfp_wide_stage_1593_differential.py, float_local_zero_init_1594_differential.py
and vfp_high_bank_restore_1318_differential.py.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.metadata
import os
import random
import shutil
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import unicorn
import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn import arm_const as A

OPT_SHA256 = "7065f112fdaae127291f5f12cacc00619c55363e14a5141059dc2fcc6cfd00df"
ATTACHMENT = "https://github.com/user-attachments/files/32349478/errors.zip"
COMPILE_FLAGS = ["--target", "cortex-m7", "--relocatable", "--all-exports",
                 "--embedder-data-init", "--embedder-global-init"]
LIBGCC_QUERY = ["-mthumb", "-mcpu=cortex-m7", "-mfpu=fpv5-sp-d16",
                "-mfloat-abi=hard", "-print-libgcc-file-name"]

CONFIGURE = "pulseengine:falcon-cascade/controller@0.10.0#configure"
STEP = "pulseengine:falcon-cascade/controller@0.10.0#step"
REALLOC = "cabi_realloc_wit_bindgen_0_41_0"
N_CONFIGURE, N_REALLOC, N_STEP = 42, 60, 1000
STEP_EPISODE = 50

# Machine layout (unicorn). The linked image sits at 0 (-Ttext=0).
LIN, LIN_SIZE = 0x2000_0000, 0x1_0000        # R11, R10 = 64 KiB (1 page)
GLOB = 0x3000_0000                           # R9
STACK, STACK_SIZE = 0x4000_0000, 0x10_0000
SP0 = STACK + STACK_SIZE - 0x1000            # 4 KiB of caller frame above SP
RET = 0x0F00_0000                            # return trap page
INSN_LIMIT = 20_000_000
FUEL = 200_000_000
# The `step` input record (the ABI's indirect parameter) lives here: above
# __heap_base (19616) and the module's bump arena, below the 64 KiB end.
INPUT = 0xC000

R = {n: getattr(A, f"UC_ARM_REG_{n}") for n in
     ["R0", "R1", "R2", "R3", "R4", "R5", "R6", "R7", "R8", "R9", "R10",
      "R11", "R12", "SP", "LR", "PC"]}
S_REGS = [getattr(A, f"UC_ARM_REG_S{i}") for i in range(32)]
CALLEE_CORE = ["R4", "R5", "R6", "R7", "R8", "R9", "R10", "R11"]


def die(msg: str, rc: int = 2):
    print(f"{'FAIL' if rc == 1 else 'SETUP-FAIL'}: {msg}")
    sys.exit(rc)


# ---- wasm module facts ------------------------------------------------------
def _uleb(b, p):
    r = s = 0
    while True:
        x = b[p]
        p += 1
        r |= (x & 0x7F) << s
        s += 7
        if not x & 0x80:
            return r, p


def _sleb(b, p):
    r = s = 0
    while True:
        x = b[p]
        p += 1
        r |= (x & 0x7F) << s
        s += 7
        if not x & 0x80:
            return (r - (1 << s) if x & 0x40 else r), p


def _uleb_enc(v):
    out = bytearray()
    while True:
        x = v & 0x7F
        v >>= 7
        out.append(x | (0x80 if v else 0))
        if not v:
            return bytes(out)


def _i32_const(b, p):
    if b[p] != 0x41:
        die("only i32.const initialisers are modelled")
    v, p = _sleb(b, p + 1)
    if b[p] != 0x0B:
        die("initialiser is not a single i32.const")
    return v & 0xFFFFFFFF, p + 1


def module_facts(wasm: bytes):
    """(sections, globals, data): globals as (valtype, init), data as (off, bytes)."""
    p, secs, glob, data = 8, [], [], []
    while p < len(wasm):
        sid = wasm[p]
        ln, q = _uleb(wasm, p + 1)
        secs.append((sid, p, q, q + ln))
        if sid == 6:
            n, r = _uleb(wasm, q)
            for _ in range(n):
                vt = wasm[r]
                if vt != 0x7F:
                    die(f"global of value type {vt:#x} not modelled (i32 only)")
                v, r = _i32_const(wasm, r + 2)
                glob.append(v)
        elif sid == 11:
            n, r = _uleb(wasm, q)
            for _ in range(n):
                flag, r = _uleb(wasm, r)
                if flag != 0:
                    die("only active memory-0 data segments are modelled")
                off, r = _i32_const(wasm, r)
                ln2, r = _uleb(wasm, r)
                data.append((off, wasm[r:r + ln2]))
                r += ln2
        p = q + ln
    return secs, glob, data


def with_global_exports(wasm: bytes, secs, nglob: int) -> bytes:
    """The same module with `__falcon_g<i>` exports appended for every global,
    so wasmtime's global values can be read and compared. Appending an export
    entry changes no function body, type, import or initialiser."""
    exp = [s for s in secs if s[0] == 7]
    if len(exp) != 1:
        die("expected exactly one export section")
    _, start, q, end = exp[0]
    n, r = _uleb(wasm, q)
    body = bytearray(wasm[r:end])
    for i in range(nglob):
        name = f"__falcon_g{i}".encode()
        body += _uleb_enc(len(name)) + name + b"\x03" + _uleb_enc(i)
    payload = _uleb_enc(n + nglob) + bytes(body)
    return wasm[:start] + b"\x07" + _uleb_enc(len(payload)) + payload + wasm[end:]


# ---- the reference ------------------------------------------------------------
class Ref:
    def __init__(self, wasm: bytes, nglob: int):
        cfg = wasmtime.Config()
        cfg.consume_fuel = True
        self.engine = wasmtime.Engine(cfg)
        self.module = wasmtime.Module(self.engine, wasm)
        self.nglob = nglob
        self.fresh()

    def fresh(self):
        self.store = wasmtime.Store(self.engine)
        self.store.set_fuel(FUEL)
        inst = wasmtime.Instance(self.store, self.module, [])
        self.ex = inst.exports(self.store)
        self.mem = self.ex["memory"]

    def memory(self) -> bytes:
        return bytes(self.mem.read(self.store, 0, LIN_SIZE))

    def write(self, addr: int, blob: bytes):
        self.mem.write(self.store, blob, addr)

    def globals(self):
        return [self.ex[f"__falcon_g{i}"].value(self.store) & 0xFFFFFFFF
                for i in range(self.nglob)]

    def call(self, name, *args):
        """('ok', u32 or None) / ('trap', msg). Fuel exhaustion is a HARNESS
        failure (a vector the reference cannot finish is not a test)."""
        self.store.set_fuel(FUEL)
        try:
            v = self.ex[name](self.store, *args)
        except wasmtime.Trap as e:
            if "fuel" in str(e).lower():
                die(f"wasmtime ran out of fuel on {name}{args!r}")
            return ("trap", str(e).splitlines()[0])
        return ("ok", None if v is None else v & 0xFFFFFFFF)


# ---- the ARM side -------------------------------------------------------------
class Arm:
    def __init__(self, elf_path: str, globals_init, data):
        with open(elf_path, "rb") as fh:
            ef = ELFFile(fh)
            self.syms = {}
            for sec in ef.iter_sections():
                if sec["sh_type"] == "SHT_SYMTAB":
                    for s in sec.iter_symbols():
                        if s.name:
                            self.syms[s.name] = s["st_value"]
            self.segs = [(seg["p_vaddr"], seg.data()) for seg in ef.iter_segments()
                         if seg["p_type"] == "PT_LOAD"]
        top = max(a + len(d) for a, d in self.segs)
        if top >= RET:
            die("linked image overlaps the return-trap page")
        self.code_end = top
        self.globals_init, self.data = globals_init, data
        uc = self.uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        try:
            uc.ctl_set_cpu_model(A.UC_CPU_ARM_MAX)
        except AttributeError:
            pass
        uc.mem_map(0, (top + 0xFFFF) & ~0xFFFF)
        for a, d in self.segs:
            uc.mem_write(a, d)
        uc.mem_map(RET, 0x1000)
        uc.mem_map(LIN, LIN_SIZE)
        uc.mem_map(GLOB, 0x1000)
        uc.mem_map(STACK, STACK_SIZE)

    def reset_image(self) -> bytes:
        """The embedder's reset: zeroed memory with the active data applied."""
        img = bytearray(LIN_SIZE)
        for off, blob in self.data:
            img[off:off + len(blob)] = blob
        return bytes(img)

    def load_state(self, mem: bytes, globs):
        self.uc.mem_write(LIN, mem)
        self.uc.mem_write(GLOB, b"".join(struct.pack("<I", g) for g in globs))

    def memory(self) -> bytes:
        return bytes(self.uc.mem_read(LIN, LIN_SIZE))

    def globals(self, n):
        return list(struct.unpack(f"<{n}I", bytes(self.uc.mem_read(GLOB, 4 * n))))

    def call(self, name, core_args, s_args, rng, garbage):
        """('ok', r0) / ('trap', info) / ('fault', info), plus a list of AAPCS
        violations."""
        uc = self.uc
        pick = (lambda: rng.getrandbits(32)) if garbage else (lambda: 0)
        stack = (rng.randbytes(STACK_SIZE) if garbage else bytes(STACK_SIZE))
        uc.mem_write(STACK, stack)
        uc.reg_write(A.UC_ARM_REG_C1_C0_2, 0x00F00000)   # CPACR: CP10/CP11
        uc.reg_write(A.UC_ARM_REG_FPEXC, 0x40000000)     # FPEXC.EN
        for n in ["R0", "R1", "R2", "R3", "R12"]:
            uc.reg_write(R[n], pick())
        saved = {}
        for n in CALLEE_CORE[:5]:
            saved[n] = pick()
            uc.reg_write(R[n], saved[n])
        saved_s = {}
        for i, r in enumerate(S_REGS):
            v = pick()
            uc.reg_write(r, v)
            if i >= 16:
                saved_s[i] = v
        for n, v in (("R9", GLOB), ("R10", LIN_SIZE), ("R11", LIN)):
            uc.reg_write(R[n], v)
            saved[n] = v
        for i, v in enumerate(core_args):
            uc.reg_write(R[f"R{i}"], v & 0xFFFFFFFF)
        for i, v in enumerate(s_args):
            uc.reg_write(S_REGS[i], v)
        uc.reg_write(R["SP"], SP0)
        uc.reg_write(R["LR"], RET | 1)
        entry = self.syms[name] & ~1
        try:
            uc.emu_start(entry | 1, RET, count=INSN_LIMIT)
        except UcError as e:
            pc = uc.reg_read(R["PC"]) & ~1
            if pc < self.code_end:
                hw = struct.unpack("<H", bytes(uc.mem_read(pc, 2)))[0]
                if hw & 0xFF00 == 0xDE00:  # Thumb UDF: synth's trap
                    return ("trap", f"udf at {pc:#x}"), []
            return ("fault", f"{e} at pc={pc:#x}"), []
        pc = uc.reg_read(R["PC"]) & ~1
        if pc != RET:
            return ("fault", f"did not return within {INSN_LIMIT} insns (pc={pc:#x})"), []
        bad = []
        if uc.reg_read(R["SP"]) != SP0:
            bad.append("SP not restored")
        for n, v in saved.items():
            if uc.reg_read(R[n]) & 0xFFFFFFFF != v:
                bad.append(f"{n} clobbered")
        for i, v in saved_s.items():
            if uc.reg_read(S_REGS[i]) & 0xFFFFFFFF != v:
                bad.append(f"S{i} clobbered")
        above = bytes(uc.mem_read(SP0, STACK + STACK_SIZE - SP0))
        if above != stack[SP0 - STACK:]:
            bad.append("caller's stack above SP written")
        return ("ok", uc.reg_read(R["R0"]) & 0xFFFFFFFF), bad


# ---- comparison -------------------------------------------------------------
def _is_nan32(w):
    return (w & 0x7F800000) == 0x7F800000 and (w & 0x007FFFFF) != 0


def diff_memory(a: bytes, b: bytes):
    """(n_differing_words, n_nan_payload_words). Aligned 4-byte words; a word
    where both sides hold a NaN (any payload) is NOT a difference."""
    if a == b:
        return 0, 0
    wa = struct.unpack(f"<{LIN_SIZE // 4}I", a)
    wb = struct.unpack(f"<{LIN_SIZE // 4}I", b)
    bad = nan = 0
    for x, y in zip(wa, wb):
        if x != y:
            if _is_nan32(x) and _is_nan32(y):
                nan += 1
            else:
                bad += 1
    return bad, nan


class Tally:
    def __init__(self):
        self.calls = self.match = self.traps = self.nan_words = 0
        self.first = None
        self.reasons = {}

    def add(self, ok, why, trapped, nan, label):
        self.calls += 1
        self.nan_words += nan
        if ok:
            self.match += 1
            self.traps += trapped
        else:
            self.reasons[why] = self.reasons.get(why, 0) + 1
            if self.first is None:
                self.first = f"{label}: {why}"


def judge(ref: Ref, arm: Arm, nglob, want, got, abi_bad):
    """Compare one call; returns (ok, why, trapped, nan_words)."""
    if got[0] == "fault":
        return False, f"ARM fault: {got[1]}", False, 0
    if want[0] == "trap" or got[0] == "trap":
        if want[0] != got[0]:
            return False, f"trap disagreement: wasmtime {want} vs ARM {got}", False, 0
    elif want[1] is not None and want[1] != got[1]:
        return False, f"return value {got[1]:#010x}, want {want[1]:#010x}", False, 0
    if abi_bad and got[0] == "ok":
        return False, "AAPCS: " + ", ".join(abi_bad), False, 0
    bad, nan = diff_memory(ref.memory(), arm.memory())
    if bad:
        return False, f"{bad} linear-memory words differ", False, nan
    if ref.globals() != arm.globals(nglob):
        return False, f"globals {arm.globals(nglob)} vs {ref.globals()}", False, nan
    return True, None, got[0] == "trap", nan


# ---- vectors (seeded; independent of the binary under test) -------------------
def rand_f32(rng):
    k = rng.random()
    if k < 0.70:
        v = rng.uniform(-20.0, 20.0)
    elif k < 0.82:
        v = rng.uniform(-1e-3, 1e-3)
    elif k < 0.90:
        v = rng.choice([0.0, -0.0, 1.0, -1.0, 0.5, -0.5, 9.81, -9.81])
    elif k < 0.97:
        v = rng.uniform(-1e6, 1e6)
    else:
        v = rng.choice([float("inf"), float("-inf"), float("nan"), 1e-40, 3.4e38])
    return struct.unpack("<I", struct.pack("<f", v))[0]


def f32_val(bits):
    return struct.unpack("<f", struct.pack("<I", bits))[0]


def step_record(rng) -> bytes:
    """The 100-byte record `step` reads through its pointer parameter: f32 at
    0..24, an option tag at 28 (payload f32 at 32/36/40), a tag at 44 (f32
    48/52/56), a tag at 60 (f32 64), a tag at 68 (four words 72..84), f32 at
    88/92/96. Padding stays zero."""
    rec = bytearray(100)
    for off in (0, 4, 8, 12, 16, 20, 24, 88, 92, 96):
        struct.pack_into("<I", rec, off, rand_f32(rng))
    for tag, payload in ((28, (32, 36, 40)), (44, (48, 52, 56)), (60, (64,)),
                         (68, (72, 76, 80, 84))):
        if rng.random() < 0.5:
            rec[tag] = 1
            for off in payload:
                struct.pack_into("<I", rec, off, rand_f32(rng))
    return bytes(rec)


def configure_args(rng):
    return [rand_f32(rng) for _ in range(9)]


def realloc_args(rng, live):
    """(old_ptr, old_size, align, new_size). Every old block is IN BOUNDS: the
    default `--safety-bounds none` envelope emits no OOB trap for memory.copy,
    so an out-of-bounds source would test the envelope, not the code."""
    align = rng.choice([1, 2, 4, 8, 16])
    new = rng.choice([0, rng.randrange(1, 64), rng.randrange(64, 256),
                      rng.randrange(256, 1024)])
    if live and rng.random() < 0.5:
        old_ptr, old_size = rng.choice(live)
    else:
        old_ptr, old_size = 0, 0
    return old_ptr, old_size, align, new


# ---- driver -------------------------------------------------------------------
def build(synth, wasm_path, tmp):
    obj = os.path.join(tmp, "opt.o")
    r = subprocess.run([synth, "compile", wasm_path, *COMPILE_FLAGS, "-o", obj],
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if r.returncode != 0 or "skipping function" in r.stdout:
        print(r.stdout)
        die(f"compile rc={r.returncode} (or a function was skipped)", 1)
    if "Compiled 17 functions" not in r.stdout:
        print(r.stdout)
        die("compile did not report 17 functions", 1)
    gcc = shutil.which("arm-none-eabi-gcc")
    ld = shutil.which("arm-none-eabi-ld")
    if not gcc or not ld:
        die("arm-none-eabi-gcc / arm-none-eabi-ld not found")
    libgcc = subprocess.run([gcc, *LIBGCC_QUERY], capture_output=True, text=True,
                            check=True).stdout.strip()
    if "v7e-m+fp/hard" not in libgcc:
        die(f"libgcc is not the thumb/v7e-m+fp/hard multilib: {libgcc}")
    elf = os.path.join(tmp, "opt.elf")
    r = subprocess.run([ld, "-Ttext=0", "-e", "0", obj, libgcc, "-o", elf],
                       capture_output=True, text=True)
    if r.returncode != 0 or r.stderr.strip():
        die(f"link failed:\n{r.stderr}")
    with open(obj, "rb") as fh:
        osha = hashlib.sha256(fh.read()).hexdigest()
    return obj, elf, osha, libgcc


def run_state(ref, arm, nglob, garbage, seed):
    label = "garbage" if garbage else "zeroed"
    rng_vec = random.Random(seed)            # inputs: identical in both states
    rng_mach = random.Random(seed ^ 0x5EED)  # machine garbage
    out = {}

    def one(tally, name, core, s_args, wasm_args, tag):
        arm.load_state(ref.memory(), ref.globals())
        want = ref.call(name, *wasm_args)
        got, abi_bad = arm.call(name, core, s_args, rng_mach, garbage)
        ok, why, trapped, nan = judge(ref, arm, nglob, want, got, abi_bad)
        tally.add(ok, why, trapped, nan, tag)
        return want

    # configure: a fresh instance per call.
    t = Tally()
    for i in range(N_CONFIGURE):
        ref.fresh()
        args = configure_args(rng_vec)
        one(t, CONFIGURE, [], args, [f32_val(a) for a in args], f"configure #{i}")
    out["configure"] = t

    # cabi_realloc: one instance, the arena accumulates until it traps.
    ref.fresh()
    t = Tally()
    live = []
    for i in range(N_REALLOC):
        a = realloc_args(rng_vec, live)
        want = one(t, REALLOC, list(a), [], list(a), f"cabi_realloc #{i} {a}")
        if want[0] == "ok" and a[3] > 0:
            live.append((want[1], a[3]))
    out["cabi_realloc"] = t

    # step: episodes on fresh instances, alternately unconfigured and
    # configured (the configure itself runs on wasmtime only; the ARM machine
    # takes its state from wasmtime before every compared call).
    t = Tally()
    for i in range(N_STEP):
        if i % STEP_EPISODE == 0:
            ref.fresh()
            if (i // STEP_EPISODE) % 2:
                gains = [f32_val(a) for a in configure_args(rng_vec)]
                if ref.call(CONFIGURE, *gains)[0] != "ok":
                    die("an episode's configure trapped in wasmtime")
        ref.write(INPUT, step_record(rng_vec))
        one(t, STEP, [INPUT], [], [INPUT], f"step #{i}")
    out["step"] = t

    print(f"[{label}]")
    for name in ("configure", "cabi_realloc", "step"):
        t = out[name]
        extra = f", {t.traps} of the matches are traps on both sides" if t.traps else ""
        print(f"  {name:13s} {t.match} of {t.calls} match{extra}; "
              f"NaN-payload words tolerated: {t.nan_words}")
        for why, n in sorted(t.reasons.items(), key=lambda kv: -kv[1])[:8]:
            print(f"      {n:5d} x {why}")
        if t.first:
            print(f"      first: {t.first}")
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("wasm", help="the reporter's opt.wasm (sha256-checked)")
    ap.add_argument("--synth", default=os.environ.get("SYNTH", "./target/debug/synth"))
    ap.add_argument("--seed", type=int, default=1318)
    args = ap.parse_args()

    wasm = Path(args.wasm).read_bytes()
    sha = hashlib.sha256(wasm).hexdigest()
    if sha != OPT_SHA256:
        die(f"{args.wasm}: sha256 {sha} is not the #1318 opt.wasm "
            f"({OPT_SHA256}, from {ATTACHMENT}); refusing")
    print(f"input: {args.wasm} sha256 {sha} (matches the #1318 attachment)")

    secs, globs, data = module_facts(wasm)
    nglob = len(globs)
    ref = Ref(with_global_exports(wasm, secs, nglob), nglob)

    with tempfile.TemporaryDirectory(prefix="falcon1318_") as tmp:
        obj, elf, osha, libgcc = build(args.synth, args.wasm, tmp)
        ver = subprocess.run([args.synth, "--version"], capture_output=True,
                             text=True).stdout.strip()
        print(f"tools: {ver}; wasmtime-py {importlib.metadata.version('wasmtime')}; "
              f"unicorn {unicorn.__version__}; libgcc {libgcc}")
        print(f"compile: rc 0, 17 of 17 functions; object sha256 {osha}")
        arm = Arm(elf, globs, data)
        missing = [n for n in (CONFIGURE, STEP, REALLOC) if n not in arm.syms]
        if missing:
            die(f"exports missing from the linked image: {missing}", 1)

        # The embedder reset image must equal wasmtime's fresh instance.
        ref.fresh()
        if arm.reset_image() != ref.memory() or globs != ref.globals():
            die("the embedder reset image (data segments + global inits) "
                "differs from wasmtime's fresh instance — the model is wrong")
        print(f"embedder reset image == wasmtime fresh instance "
              f"({len(data)} data segments, {nglob} globals)")

        results = {g: run_state(ref, arm, nglob, g, args.seed) for g in (True, False)}

    total = sum(t.calls for r in results.values() for t in r.values())
    matched = sum(t.match for r in results.values() for t in r.values())
    if matched != total:
        print(f"RESULT: FAIL — {total - matched} of {total} calls disagree with wasmtime")
        sys.exit(1)
    print(f"RESULT: PASS — {matched} of {total} calls bit-identical to wasmtime")


if __name__ == "__main__":
    main()
