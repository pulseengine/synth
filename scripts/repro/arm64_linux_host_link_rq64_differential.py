#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 3
"""RQ-64-ARM64LINUX — the arm64-LINUX host-library claim, linked by a REAL host
linker and EXECUTED, against wasmtime. Since RQ-65-FUNCN (#1180) also the
TWO-OBJECT claim: a second synth object links into the same program unaided.

THE CLAIM THIS ORACLE GATES. `synth compile -b aarch64 --relocatable` emits a
SysV ELF64 `ET_REL` for `EM_AARCH64` with AAPCS64 calls. Before v0.64 that
object linked into an arm64-Linux program BY ACCIDENT: no document claimed it,
no oracle handed it to a host linker for that target, nothing executed the
result. `file` and `nm` were the whole evidence base — the standard v0.63
rejected four times. This harness is the evidence.

WHAT IT DOES, in the order a consumer would:

  1. `synth compile <fixture> -b aarch64 --target cortex-a53 --relocatable
     --all-exports` -> `synth.o` (the object under test, byte-for-byte what
     ships).
  2. GENERATES a freestanding C harness FROM THE CASE TABLE BELOW (one source
     for the C call sequence and the wasmtime call sequence — a hand-mirrored
     pair would drift; globals persist across calls, so order matters), plus
     an assembly `_start` that establishes `x28` ONCE and never touches it
     again. The C is compiled with `clang -target aarch64-unknown-linux-gnu
     -ffreestanding -nostdlib -ffixed-x28`. The harness is a genuine
     arm64-Linux static executable: its only kernel surface is `write(2)` on
     fd 1 and `exit_group(2)`.
  3. Links all three with `ld.lld -m aarch64linux -static` — a real host
     linker resolving every R_AARCH64_CALL26 / JUMP26 / ADR_PREL_PG_HI21 /
     ADD_ABS_LO12_NC synth emitted, placing synth's `.data` (`__synth_globals`)
     and binding the SHN_UNDEF import `host_add` to the harness's C
     definition. The linked image is checked with pyelftools: ET_EXEC,
     EM_AARCH64, ELFOSABI_SYSV, ZERO undefined symbols, ZERO `.rela` sections
     left, every synth symbol present.
  4. EXECUTES the linked image under unicorn (UC_ARCH_ARM64) with the Linux
     ELF loader's semantics reproduced in ~30 lines — PT_LOAD segments at
     their vaddr, bss zero-filled, a fresh stack, PC = e_entry — and the two
     syscalls serviced. Every printed `name=hex` line is compared against a
     wasmtime instance that ran the SAME call sequence with the SAME host
     `host_add` (expected values are never written here).
  5. NATIVE-ABI LEGS, when the host can: on a Linux/aarch64 host the image is
     simply RUN (`REQUIRE_NATIVE=1` makes its absence a failure — the CI job
     on the `ubuntu-24.04-arm` runner sets it); when `qemu-aarch64[-static]`
     is on PATH it is run under qemu-user, an INDEPENDENT ELF loader + syscall
     layer (`REQUIRE_QEMU=1` likewise). Each leg's stdout must be
     byte-identical to the unicorn leg's and match wasmtime.
  6. RED-FIRST, built in. Three broken inputs must make the host linker
     REFUSE with the message naming the cause: an ARM (EM_ARM, Thumb-2)
     object handed to `-m aarch64linux`; the aarch64 object handed to
     `-m elf_x86_64`; and a harness that omits the `host_add` definition. And
     a MUTATION control: bit 30 of `add`'s first instruction is flipped in the
     LINKED image (ADD-shifted-reg -> SUB) and the differential must report a
     mismatch — a check that cannot fail is not a check (#1113).
  7. CO-LINK (RQ-65-FUNCN, #1180). A SECOND synth object —
     `colink_second_rq65.wat`, shaped to define its OWN `func_1`,
     `__synth_globals` and `__synth_func_table` (the three names two synth
     objects used to collide on; the leg is RED if either object lacks one)
     — is linked into the SAME program with `synth.o`, with NO objcopy step.
     Both objects are checked first: those names are STB_LOCAL, the exports
     and the import STB_GLOBAL, `.symtab` locals-first with `sh_info` at the
     first non-local. The co-linked image is checked like the single one and
     EXECUTED under unicorn (and natively on arm64-Linux) with every value
     from BOTH objects compared against wasmtime, in one combined harness.
     RED-FIRST, twice, because the binding is the whole mechanism: (a)
     `synth.o` linked with ITSELF must be refused on its GLOBAL exports
     (`duplicate symbol: add`) with NO `func_1` / `__synth_` name among the
     duplicates — the same linker, in the same link, still refuses
     duplicates, and the locals are what it does not see; (b) with `func_N`
     re-globalized in both objects by `llvm-objcopy --globalize-symbol`, the
     v0.64 collision must RETURN (`duplicate symbol: func_1`). Before
     RQ-65-FUNCN this step pinned that collision as a documented limitation
     and executed the `--localize-symbol` workaround; the pin moved with the
     doc in the same PR.

WHAT IT DOES NOT VERIFY (stated so the claim cannot outrun its instrument):
  * WASM traps. Every case is non-trapping on purpose — a trap is `brk #0`,
    which on Linux is SIGTRAP and kills the process. Trap placement is gated
    by the sibling unicorn oracles (`aarch64_bounds_865_differential.py`,
    `aarch64_call_indirect_851_differential.py`, ...); what the embedder does
    with SIGTRAP is the embedder's contract.
  * A dynamic link (shared object / PLT / GOT / TLS). synth emits none of
    those; the claim is a STATIC library. `-static` is what is exercised.
  * libc interplay. The harness is freestanding; a libc-linked embedder adds
    nothing synth's object depends on, but it is not what ran here.
  * On a non-Linux host (this repo's arm64-Darwin developers), the unicorn
    leg is an emulation of the Linux loader contract, not the Linux kernel —
    which is why the native and qemu legs exist and CI requires them.

Run (needs clang with the aarch64 target, ld.lld, wasmtime, unicorn,
pyelftools):
  SYNTH=<target>/debug/synth python scripts/repro/arm64_linux_host_link_rq64_differential.py
"""

import os
import platform
import shutil
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM64, UC_HOOK_INTR, UC_MODE_ARM, Uc, UcError
from unicorn import arm64_const as A

HERE = Path(__file__).parent
WAT = HERE / "arm64_linux_host_link_rq64.wat"
# RQ-65-FUNCN: the second object of the co-link leg (shared with the Mach-O
# oracle, so both containers prove the same two-object claim).
SECOND_WAT = HERE / "colink_second_rq65.wat"
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

# The names two synth objects used to collide on (#1180). The co-link leg
# requires BOTH objects to define all three, so it cannot pass vacuously.
CLASH = ["func_1", "__synth_globals", "__synth_func_table"]

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
LINMEM_BYTES = 65536  # the fixture declares (memory 1)

# The Linux ELF loader contract, reproduced for unicorn.
PAGE = 0x1000
STACK_TOP = 0x8000_0000
STACK_SIZE = 0x10_0000
SYS_WRITE, SYS_EXIT, SYS_EXIT_GROUP = 64, 93, 94

# --------------------------------------------------------------------------
# THE CASE TABLE — the single source for BOTH the generated C harness and the
# wasmtime reference sequence. Kinds:
#   ("call", label, export, [arg types], [args], result type, why)
#   ("peek", label, addr, why)          C reads u32 at linmem+addr; wasmtime reads memory
#   ("poke", label, addr, byte, why)    C writes a byte at linmem+addr; wasmtime writes memory
# Types: i32 / i64 / f64 (f64 args and results are carried as their IEEE bits).
# --------------------------------------------------------------------------
CASES = [
    ("call", "add", "add", ["i32", "i32"], [3, 4], "i32",
     "host -> synth, w-register args and result (AAPCS64)"),
    ("call", "add_wrap", "add", ["i32", "i32"], [0xFFFFFFFF, 1], "i32",
     "i32 wraps in the w view"),
    ("call", "mul64", "mul64", ["i64", "i64"], [0x1_0000_0001, 0x10], "i64",
     "x-register args and result"),
    ("call", "f64_scale", "f64_scale", ["f64", "f64"],
     [0x3FF8000000000000, 0xC010000000000000], "f64",
     "d-register args and result: 1.5 * -4.0"),
    ("call", "store_load", "store_load", ["i32", "i32"], [16, 0xDEADBEEF], "i32",
     "i32.store then i32.load through x28"),
    ("peek", "peek16", 16,
     "the HARNESS reads base+16 from C: the base it chose is the base synth used"),
    ("poke", "poke40", 40, 0xAB,
     "the harness writes a byte synth must see"),
    ("call", "load8u", "load8u", ["i32"], [40], "i32",
     "i32.load8_u of the byte the harness wrote"),
    ("call", "bump1", "bump", ["i32"], [1], "i32",
     "global RMW in synth's own .data (placed by the linker)"),
    ("call", "bump10", "bump", ["i32"], [10], "i32",
     "the global PERSISTED across calls"),
    ("call", "acc64", "acc64", ["i64"], [1], "i64",
     "an i64 global slot"),
    ("call", "dispatch_mul", "dispatch", ["i32", "i32", "i32"], [2, 6, 7], "i32",
     "call_indirect through the synth-emitted funcref table (JUMP26)"),
    ("call", "dispatch_sub", "dispatch", ["i32", "i32", "i32"], [1, 6, 7], "i32",
     "a second slot — the per-slot stride is real"),
    ("call", "via_import", "via_import", ["i32"], [5], "i32",
     "synth -> host: CALL26 bound to the C `host_add` by the linker"),
    ("call", "below_call", "below_call", ["i32", "i32"], [100, 20], "i32",
     "a value below the import call's args survives it (RQ-63-A64STACK)"),
    ("call", "helper_chain", "helper_chain", ["i32"], [50], "i32",
     "synth -> synth: CALL26 to a NON-exported local"),
    ("call", "mem_size", "mem_size", [], [], "i32",
     "memory.size is the declared-minimum constant"),
]

# RQ-65-FUNCN: the second object's cases, run AFTER `CASES` in the combined
# harness (labels must stay unique across both tables). Each one goes through
# a name that used to collide.
SECOND_CASES = [
    ("call", "b_g", "g", ["i32"], [41], "i32",
     "second object: synth -> host, CALL26 bound to the SAME C host_add"),
    ("call", "b_acc1", "acc_b", ["i32"], [1], "i32",
     "second object's OWN __synth_globals (collided when GLOBAL)"),
    ("call", "b_acc10", "acc_b", ["i32"], [10], "i32",
     "...and it persists across calls, separately from the first object's"),
    ("call", "b_disp_triple", "disp_b", ["i32", "i32"], [0, 7], "i32",
     "second object's OWN __synth_func_table (collided when GLOBAL)"),
    ("call", "b_disp_neg", "disp_b", ["i32", "i32"], [1, 7], "i32",
     "slot 1 of the second table"),
    ("call", "b_chain", "chain_b", ["i32"], [5], "i32",
     "second object's func_1/func_2 via CALL26 — LOCAL labels, resolved in-object"),
]

CTYPE = {"i32": "int32_t", "i64": "int64_t", "f64": "double"}

START_S = """\
// arm64-Linux _start: the kernel enters with SP set. Establish x28 ONCE (the
// synth linear-memory base precondition) and hand off to C, which is compiled
// with -ffixed-x28 so it never allocates the register.
.text
.globl _start
.type _start, %function
_start:
  adrp x28, linmem
  add  x28, x28, :lo12:linmem
  bl   harness_main
  mov  x8, #94
  svc  #0
"""


def c_literal(ty, v):
    if ty == "i32":
        return f"(int32_t)0x{v & M32:x}u"
    if ty == "i64":
        return f"(int64_t)0x{v & M64:x}ull"
    return f"dfrom(0x{v & M64:x}ull)"


def gen_harness_c(with_host_add=True, cases=CASES):
    """The C harness, derived from `cases`. Emits `label=<16 hex>` per case."""
    decls = {}
    for c in cases:
        if c[0] == "call":
            _, _, export, argtys, _, rty, _ = c
            args = ", ".join(CTYPE[t] for t in argtys) or "void"
            decls[export] = f"extern {CTYPE[rty]} {export}({args});"
    body = []
    for c in cases:
        if c[0] == "call":
            _, label, export, argtys, args, rty, _ = c
            call = f"{export}({', '.join(c_literal(t, a) for t, a in zip(argtys, args))})"
            if rty == "i32":
                body.append(f'  emit("{label}", (uint64_t)(uint32_t){call});')
            elif rty == "i64":
                body.append(f'  emit("{label}", (uint64_t){call});')
            else:
                body.append(f'  emit("{label}", dbits({call}));')
        elif c[0] == "peek":
            _, label, addr, _ = c
            body.append(f'  emit("{label}", *(volatile uint32_t *)(linmem + {addr}));')
        elif c[0] == "poke":
            _, label, addr, byte, _ = c
            body.append(f"  linmem[{addr}] = 0x{byte:02x};")
            body.append(f'  emit("{label}", 0x{byte:02x});')
    host = ("int32_t host_add(int32_t a, int32_t b) { return a + b; }\n"
            if with_host_add else "/* host_add deliberately NOT defined */\n")
    return f"""\
#include <stdint.h>
/* GENERATED by arm64_linux_host_link_rq64_differential.py from its CASES. */
{chr(10).join(decls.values())}

/* The import synth calls OUT to (AAPCS64, ordinary C). */
{host}
/* Linear memory: the harness owns it; x28 points here (set once in _start). */
__attribute__((aligned(4096))) uint8_t linmem[{LINMEM_BYTES}];

static long sys_write(int fd, const void *p, unsigned long n) {{
  register long x0 __asm__("x0") = fd;
  register long x1 __asm__("x1") = (long)p;
  register long x2 __asm__("x2") = (long)n;
  register long x8 __asm__("x8") = {SYS_WRITE};
  __asm__ volatile("svc #0" : "+r"(x0) : "r"(x1), "r"(x2), "r"(x8) : "memory");
  return x0;
}}
static void emit(const char *name, uint64_t v) {{
  char buf[96]; int n = 0;
  while (*name) buf[n++] = *name++;
  buf[n++] = '=';
  for (int i = 15; i >= 0; i--) buf[n++] = "0123456789abcdef"[(v >> (i * 4)) & 15];
  buf[n++] = '\\n';
  sys_write(1, buf, (unsigned long)n);
}}
static uint64_t dbits(double d) {{ union {{ double d; uint64_t u; }} u; u.d = d; return u.u; }}
static double dfrom(uint64_t b) {{ union {{ double d; uint64_t u; }} u; u.u = b; return u.d; }}

int harness_main(void) {{
{chr(10).join(body)}
  return 0;
}}
"""


# --------------------------------------------------------------------------
# wasmtime: the reference, run FIRST, same sequence, same host function.
# --------------------------------------------------------------------------
def to_signed(ty, v):
    if ty == "i32":
        return struct.unpack("<i", struct.pack("<I", v & M32))[0]
    if ty == "i64":
        return struct.unpack("<q", struct.pack("<Q", v & M64))[0]
    return struct.unpack("<d", struct.pack("<Q", v & M64))[0]


def norm(ty, r):
    if ty == "i32":
        return r & M32
    if ty == "i64":
        return r & M64
    return struct.unpack("<Q", struct.pack("<d", r))[0]


def wasmtime_expected(wat=WAT, cases=CASES):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(wat))
    store = wasmtime.Store(engine)
    linker = wasmtime.Linker(engine)
    i32 = wasmtime.ValType.i32()
    linker.define_func("env", "host_add", wasmtime.FuncType([i32, i32], [i32]),
                       lambda a, b: to_signed("i32", (a + b) & M32))
    inst = linker.instantiate(store, module)
    ex = inst.exports(store)
    out = []
    for c in cases:
        if c[0] == "call":
            _, label, export, argtys, args, rty, _ = c
            r = ex[export](store, *[to_signed(t, a) for t, a in zip(argtys, args)])
            out.append((label, norm(rty, r)))
        elif c[0] == "peek":
            _, label, addr, _ = c
            mem = ex["memory"]
            out.append((label, struct.unpack("<I", bytes(mem.read(store, addr, addr + 4)))[0]))
        elif c[0] == "poke":
            _, label, addr, byte, _ = c
            mem = ex["memory"]
            mem.write(store, bytes([byte]), addr)
            out.append((label, byte))
    return out


# --------------------------------------------------------------------------
# Toolchain
# --------------------------------------------------------------------------
def find_tool(env, *names):
    if os.environ.get(env):
        return os.environ[env]
    for n in names:
        p = shutil.which(n)
        if p:
            return p
    return None


def compile_synth(wat, out, backend="aarch64"):
    cmd = [SYNTH, "compile", str(wat), "-o", out, "--relocatable", "--all-exports"]
    if backend == "aarch64":
        cmd += ["-b", "aarch64", "--target", "cortex-a53"]
    return subprocess.run(cmd, capture_output=True, text=True,
                          env={"PATH": "/usr/bin:/bin"})


def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


# --------------------------------------------------------------------------
# The linked image: checks, and the Linux-loader-semantics unicorn run.
# --------------------------------------------------------------------------
def check_image(path, want_syms):
    f = ELFFile(open(path, "rb"))
    problems = []
    if f["e_type"] != "ET_EXEC":
        problems.append(f"e_type {f['e_type']} != ET_EXEC")
    if f["e_machine"] != "EM_AARCH64":
        problems.append(f"e_machine {f['e_machine']} != EM_AARCH64")
    osabi = f["e_ident"]["EI_OSABI"]
    if osabi != "ELFOSABI_SYSV":
        problems.append(f"EI_OSABI {osabi} != ELFOSABI_SYSV")
    rela = [s.name for s in f.iter_sections() if s.name.startswith(".rela")]
    if rela:
        problems.append(f"relocation sections survived the link: {rela}")
    symtab = f.get_section_by_name(".symtab")
    present = {}
    undefined = []
    for sy in symtab.iter_symbols():
        if not sy.name:
            continue
        if sy["st_shndx"] == "SHN_UNDEF":
            undefined.append(sy.name)
        else:
            present[sy.name] = sy["st_value"]
    if undefined:
        problems.append(f"undefined symbols in the linked image: {undefined}")
    missing = [s for s in want_syms if s not in present]
    if missing:
        problems.append(f"synth symbols missing from the image: {missing}")
    return problems, present, f["e_entry"]


def synth_object_symbols(path):
    f = ELFFile(open(path, "rb"))
    defined, undefined = [], []
    for sy in f.get_section_by_name(".symtab").iter_symbols():
        if not sy.name:
            continue
        (undefined if sy["st_shndx"] == "SHN_UNDEF" else defined).append(sy.name)
    return defined, undefined


def check_bindings(path):
    """RQ-65-FUNCN: the binding contract of ONE synth object, read back with
    pyelftools (an independent reader). Every name synth invents (`func_N`,
    `__synth_*`) must be STB_LOCAL; every export and the import STB_GLOBAL;
    all locals must precede all non-locals; `.symtab` sh_info must be the
    index of the first non-local. Returns (problems, locals, globals)."""
    f = ELFFile(open(path, "rb"))
    symtab = f.get_section_by_name(".symtab")
    problems, locals_, globals_ = [], [], []
    first_nonlocal = None
    for i, sy in enumerate(symtab.iter_symbols()):
        if i == 0:
            continue  # the null symbol
        bind = sy["st_info"]["bind"]
        invented = sy.name.startswith("func_") or sy.name.startswith("__synth_")
        if bind == "STB_LOCAL":
            locals_.append(sy.name)
            if not invented:
                problems.append(f"{sy.name} is STB_LOCAL but is not a synth-invented name")
            if first_nonlocal is not None:
                problems.append(f"STB_LOCAL {sy.name} at index {i} follows a non-local "
                                f"(ELF requires locals first)")
        else:
            globals_.append(sy.name)
            if first_nonlocal is None:
                first_nonlocal = i
            if invented:
                problems.append(f"{sy.name} is {bind}; synth-invented names must be STB_LOCAL")
            if bind != "STB_GLOBAL":
                problems.append(f"{sy.name} is {bind}, expected STB_GLOBAL")
    want_info = first_nonlocal if first_nonlocal is not None else symtab.num_symbols()
    if symtab["sh_info"] != want_info:
        problems.append(f".symtab sh_info {symtab['sh_info']} != first non-local index {want_info}")
    return problems, locals_, globals_


def emu_linux(path):
    """Load `path` the way the arm64 Linux kernel does and run it under
    unicorn, servicing write(1) and exit/exit_group. Returns
    (stdout bytes, exit status or None, fault string or None)."""
    f = ELFFile(open(path, "rb"))
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mapped = []
    for seg in f.iter_segments():
        if seg["p_type"] != "PT_LOAD":
            continue
        lo = seg["p_vaddr"] & ~(PAGE - 1)
        hi = (seg["p_vaddr"] + seg["p_memsz"] + PAGE - 1) & ~(PAGE - 1)
        for _, mhi in mapped:
            if lo < mhi:
                lo = mhi
        if hi > lo:
            mu.mem_map(lo, hi - lo)  # zero-filled: the bss contract
            mapped.append((lo, hi))
        mu.mem_write(seg["p_vaddr"], seg.data())
    mu.mem_map(STACK_TOP - STACK_SIZE, STACK_SIZE)
    mu.reg_write(A.UC_ARM64_REG_SP, STACK_TOP)
    out = bytearray()
    state = {"exit": None, "fault": None}

    def on_intr(uc, intno, _):
        nr = uc.reg_read(A.UC_ARM64_REG_X8)
        if nr == SYS_WRITE:
            fd = uc.reg_read(A.UC_ARM64_REG_X0)
            buf = uc.reg_read(A.UC_ARM64_REG_X1)
            n = uc.reg_read(A.UC_ARM64_REG_X2)
            if fd == 1:
                out.extend(uc.mem_read(buf, n))
            uc.reg_write(A.UC_ARM64_REG_X0, n)
        elif nr in (SYS_EXIT, SYS_EXIT_GROUP):
            state["exit"] = uc.reg_read(A.UC_ARM64_REG_X0)
            uc.emu_stop()
        else:
            state["fault"] = f"unsupported syscall {nr}"
            uc.emu_stop()

    mu.hook_add(UC_HOOK_INTR, on_intr)
    try:
        mu.emu_start(f["e_entry"], 0, count=10_000_000)
    except UcError as e:
        state["fault"] = f"{e} at pc={mu.reg_read(A.UC_ARM64_REG_PC):#x}"
    if state["exit"] is None and state["fault"] is None:
        state["fault"] = "instruction budget exhausted without exit"
    return bytes(out), state["exit"], state["fault"]


def parse_lines(stdout):
    got = []
    for line in stdout.decode(errors="replace").splitlines():
        if "=" not in line:
            return None, f"unparseable harness line {line!r}"
        k, v = line.split("=", 1)
        try:
            got.append((k, int(v, 16)))
        except ValueError:
            return None, f"unparseable harness value {line!r}"
    return got, None


def compare(tag, stdout, exit_code, fault, expected, verbose=True, cases=CASES):
    """Diff the harness output against wasmtime. Returns (#ok, #fail)."""
    if fault is not None:
        print(f"  FAIL [{tag}] the image FAULTED: {fault}")
        return 0, 1
    if exit_code != 0:
        print(f"  FAIL [{tag}] exit status {exit_code} != 0")
        return 0, 1
    got, err = parse_lines(stdout)
    if err:
        print(f"  FAIL [{tag}] {err}")
        return 0, 1
    if len(got) != len(expected):
        print(f"  FAIL [{tag}] harness printed {len(got)} lines, wasmtime sequence "
              f"has {len(expected)}")
        return 0, 1
    ok = fail = 0
    for (gl, gv), (el, ev), case in zip(got, expected, cases):
        why = case[-1]
        good = gl == el and gv == ev
        if good:
            ok += 1
        else:
            fail += 1
        if verbose or not good:
            print(f"  {'ok  ' if good else 'FAIL'} [{tag}] {gl} -> {gv:#x} "
                  f"(wasmtime {el}: {ev:#x}) — {why}")
    return ok, fail


# --------------------------------------------------------------------------
def main():
    clang = find_tool("CLANG", "clang", "clang-21", "clang-20", "clang-19", "clang-18")
    lld = find_tool("LLD", "ld.lld", "ld.lld-21", "ld.lld-20", "ld.lld-19", "ld.lld-18")
    if not clang or not lld:
        print(f"RED: host toolchain missing (clang={clang}, ld.lld={lld}) — "
              f"this oracle needs a real linker for arm64-linux")
        return 1
    tmp = Path(tempfile.mkdtemp(prefix="rq64-"))
    fails = 0
    try:
        # ---- 1. the object under test ------------------------------------
        print("== compile: synth -b aarch64 --target cortex-a53 --relocatable ==")
        obj = tmp / "synth.o"
        r = compile_synth(WAT, str(obj))
        if r.returncode != 0 or "skipping" in r.stderr or not obj.exists():
            print(f"RED: synth compile failed/declined:\n{r.stdout}\n{r.stderr}")
            return 1
        defined, undefined = synth_object_symbols(obj)
        print(f"  synth.o: {len(defined)} defined symbols, undefined = {undefined}")
        if undefined != ["host_add"]:
            print("RED: the object's only undefined symbol must be the import "
                  "`host_add` (#1017 contract)")
            return 1

        # ---- 2. the generated harness --------------------------------------
        print("== host link: clang -target aarch64-unknown-linux-gnu -ffixed-x28; "
              "ld.lld -m aarch64linux -static ==")
        (tmp / "start.s").write_text(START_S)
        (tmp / "harness.c").write_text(gen_harness_c())
        (tmp / "harness_nohost.c").write_text(gen_harness_c(with_host_add=False))
        cflags = ["-target", "aarch64-unknown-linux-gnu", "-O2", "-ffreestanding",
                  "-fno-builtin", "-nostdlib", "-ffixed-x28", "-c"]
        for src, out in (("start.s", "start.o"), ("harness.c", "harness.o"),
                         ("harness_nohost.c", "harness_nohost.o")):
            r = run([clang] + cflags + [str(tmp / src), "-o", str(tmp / out)])
            if r.returncode != 0:
                print(f"RED: clang failed on {src}:\n{r.stderr}")
                return 1
        image = tmp / "harness.elf"
        ldargs = [lld, "-m", "aarch64linux", "-static", "-e", "_start"]
        r = run(ldargs + ["-o", str(image), str(tmp / "start.o"),
                          str(tmp / "harness.o"), str(obj)])
        if r.returncode != 0:
            print(f"RED: ld.lld refused the synth object for arm64-linux:\n{r.stderr}")
            return 1
        want = defined + ["host_add", "harness_main", "_start", "linmem"]
        problems, present, entry = check_image(image, want)
        for p in problems:
            print(f"  FAIL image: {p}")
        fails += len(problems)
        print(f"  image: ET_EXEC EM_AARCH64 SYSV, entry {entry:#x}, "
              f"{len(present)} symbols, {len(defined)} synth symbols present, "
              f"0 undefined, 0 .rela sections"
              if not problems else "  image: PROBLEMS above")

        # ---- 3. wasmtime first ---------------------------------------------
        expected = wasmtime_expected()

        # ---- 4. unicorn with Linux-loader semantics -------------------------
        print("== execution differential: unicorn (PT_LOAD at vaddr, bss zeroed, "
              "write+exit_group serviced) vs wasmtime ==")
        out_uc, ec, fault = emu_linux(image)
        ok, bad = compare("unicorn", out_uc, ec, fault, expected)
        fails += bad
        executions = ok + bad

        # ---- 5. native-ABI legs ---------------------------------------------
        print("== native-ABI legs (the same image, a real Linux loader) ==")
        native_runs = 0
        is_linux_arm64 = platform.system() == "Linux" and platform.machine() == "aarch64"
        if is_linux_arm64:
            os.chmod(image, 0o755)
            r = subprocess.run([str(image)], capture_output=True)
            ok, bad = compare("native", r.stdout, r.returncode, None, expected,
                              verbose=False)
            same = r.stdout == out_uc
            print(f"  {'ok  ' if not bad and same else 'FAIL'} native arm64-linux: "
                  f"exit {r.returncode}, {ok} values match wasmtime, stdout "
                  f"{'==' if same else '!='} unicorn leg")
            fails += bad + (0 if same else 1)
            native_runs += 1
        elif os.environ.get("REQUIRE_NATIVE") == "1":
            print(f"  FAIL REQUIRE_NATIVE=1 but host is {platform.system()}/"
                  f"{platform.machine()}")
            fails += 1
        else:
            print(f"  skip native: host is {platform.system()}/{platform.machine()} "
                  f"(set REQUIRE_NATIVE=1 on an arm64-Linux runner)")
        qemu = find_tool("QEMU_AARCH64", "qemu-aarch64", "qemu-aarch64-static")
        if qemu and not is_linux_arm64:
            r = subprocess.run([qemu, str(image)], capture_output=True)
            ok, bad = compare("qemu-user", r.stdout, r.returncode, None, expected,
                              verbose=False)
            same = r.stdout == out_uc
            print(f"  {'ok  ' if not bad and same else 'FAIL'} qemu-user ({qemu}): "
                  f"exit {r.returncode}, {ok} values match wasmtime, stdout "
                  f"{'==' if same else '!='} unicorn leg")
            fails += bad + (0 if same else 1)
            native_runs += 1
        elif os.environ.get("REQUIRE_QEMU") == "1" and not is_linux_arm64:
            print("  FAIL REQUIRE_QEMU=1 but no qemu-aarch64[-static] on PATH")
            fails += 1
        elif not is_linux_arm64:
            print("  skip qemu-user: no qemu-aarch64[-static] on PATH")

        # ---- 6a. host-linker refusals (red-first) ---------------------------
        print("== host-linker refusals (red-first: broken inputs must be REFUSED "
              "by name) ==")
        refusals = 0
        tiny = tmp / "tiny.wat"
        tiny.write_text('(module (func (export "f") (result i32) (i32.const 7)))\n')
        arm_obj = tmp / "tiny_arm.o"
        r = compile_synth(tiny, str(arm_obj), backend="arm")
        if r.returncode != 0:
            print(f"  FAIL could not build the EM_ARM control object:\n{r.stderr}")
            fails += 1
        probes = [
            ("EM_ARM (Thumb-2) object into -m aarch64linux",
             ldargs + ["-o", str(tmp / "n1.elf"), str(tmp / "start.o"),
                       str(tmp / "harness.o"), str(arm_obj)],
             "is incompatible with aarch64linux"),
            ("aarch64 object into -m elf_x86_64",
             [lld, "-m", "elf_x86_64", "-static", "-e", "_start", "-o",
              str(tmp / "n3.elf"), str(tmp / "start.o"), str(tmp / "harness.o"),
              str(obj)],
             "is incompatible with elf_x86_64"),
            ("harness without a host_add definition",
             ldargs + ["-o", str(tmp / "n2.elf"), str(tmp / "start.o"),
                       str(tmp / "harness_nohost.o"), str(obj)],
             "undefined symbol: host_add"),
        ]
        for name, cmd, needle in probes:
            r = run(cmd)
            good = r.returncode != 0 and needle in r.stderr
            print(f"  {'ok  ' if good else 'FAIL'} {name}: "
                  f"{'refused' if r.returncode else 'LINKED'} "
                  f"(exit {r.returncode}), needle {needle!r} "
                  f"{'present' if needle in r.stderr else 'ABSENT'}")
            if good:
                refusals += 1
            else:
                fails += 1
                print(f"       stderr: {r.stderr.strip()[:300]}")

        # ---- 6b. mutation control -------------------------------------------
        print("== mutation control (can the differential fail?) ==")
        mutated = tmp / "mutated.elf"
        data = bytearray(image.read_bytes())
        f = ELFFile(open(image, "rb"))
        add_va = present["add"]
        text = next(s for s in f.iter_sections() if s.name == ".text")
        off = text["sh_offset"] + (add_va - text["sh_addr"])
        word = struct.unpack_from("<I", data, off)[0]
        struct.pack_into("<I", data, off, word ^ (1 << 30))  # ADD(shifted) -> SUB
        mutated.write_bytes(data)
        out_m, ec_m, fault_m = emu_linux(mutated)
        ok_m, bad_m = compare("mutated", out_m, ec_m, fault_m, expected, verbose=False)
        detected = bad_m > 0
        print(f"  {'ok  ' if detected else 'FAIL'} flipped bit 30 of `add`'s first "
              f"instruction ({word:#010x} -> {word ^ (1 << 30):#010x}): "
              f"{'mismatch reported' if detected else 'NOT DETECTED — the check is vacuous'}")
        if not detected:
            fails += 1

        # ---- 7. co-link (RQ-65-FUNCN, #1180): two synth objects, one program --
        # Before RQ-65-FUNCN aarch64 emitted `func_N` GLOBAL (elf.rs `0x12`) and
        # this leg PINNED the resulting `duplicate symbol: func_1` refusal plus
        # an objcopy workaround. The plan now carries binding: `func_N`,
        # `__synth_globals` and `__synth_func_table` are STB_LOCAL, so a second
        # object that defines ALL THREE itself links unaided — and the
        # co-linked image must EXECUTE with every value from BOTH objects
        # matching wasmtime. Two red-first controls follow, because the binding
        # is the whole mechanism.
        print("== co-link (RQ-65-FUNCN): synth.o + second.o — its own func_1, "
              "__synth_globals, __synth_func_table — link UNAIDED and execute ==")
        second_obj = tmp / "second.o"
        r = compile_synth(SECOND_WAT, str(second_obj))
        if r.returncode != 0 or "skipping" in r.stderr or not second_obj.exists():
            print(f"RED: the second object failed/declined:\n{r.stdout}\n{r.stderr}")
            return 1
        defined2, undefined2 = synth_object_symbols(second_obj)
        # Non-vacuity: the collision surface must EXIST in both objects.
        missing = [s for s in CLASH if s not in defined or s not in defined2]
        if missing:
            print(f"  FAIL both objects must define {CLASH}; missing: {missing}")
            fails += 1
        else:
            print(f"  ok   both objects define {CLASH} (the v0.64 collision surface)")
        if undefined2 != ["host_add"]:
            print(f"  FAIL second.o's only undefined symbol must be host_add, got {undefined2}")
            fails += 1
        # The binding contract, read back from each object by pyelftools.
        for tag_o, path in (("synth.o", obj), ("second.o", second_obj)):
            probs, loc, glob = check_bindings(path)
            for p in probs:
                print(f"  FAIL {tag_o} binding: {p}")
            fails += len(probs)
            if not probs:
                print(f"  ok   {tag_o}: {len(loc)} STB_LOCAL (func_N/__synth_*), "
                      f"{len(glob)} STB_GLOBAL (exports + import), locals first, "
                      f"sh_info = first non-local")
        # One combined harness: the fixture's cases, then the second object's.
        (tmp / "colink.c").write_text(gen_harness_c(cases=CASES + SECOND_CASES))
        r = run([clang] + cflags + [str(tmp / "colink.c"), "-o", str(tmp / "colink.o")])
        if r.returncode != 0:
            print(f"RED: clang failed on colink.c:\n{r.stderr}")
            return 1
        colink_img = tmp / "colink.elf"
        r = run(ldargs + ["-o", str(colink_img), str(tmp / "start.o"),
                          str(tmp / "colink.o"), str(obj), str(second_obj)])
        colink_runs = 0
        if r.returncode != 0:
            print(f"  FAIL synth.o + second.o: REFUSED (exit {r.returncode}) — "
                  f"{r.stderr.strip()[:300]}")
            fails += 1
        else:
            print("  ok   synth.o + second.o: LINKED (no objcopy)")
            want2 = want + defined2
            problems, present2, _ = check_image(colink_img, want2)
            for p in problems:
                print(f"  FAIL co-linked image: {p}")
            fails += len(problems)
            if not problems:
                print(f"  image: ET_EXEC EM_AARCH64 SYSV, {len(present2)} symbols, "
                      f"both objects' symbols present, 0 undefined, 0 .rela sections")
            expected2 = wasmtime_expected(SECOND_WAT, SECOND_CASES)
            both = CASES + SECOND_CASES
            out_c, ec_c, fault_c = emu_linux(colink_img)
            ok_c, bad_c = compare("co-linked", out_c, ec_c, fault_c, expected + expected2,
                                  verbose=True, cases=both)
            fails += bad_c
            colink_runs += 1
            print(f"  {'ok  ' if not bad_c else 'FAIL'} co-linked image executed: "
                  f"{ok_c} of {len(both)} values match wasmtime "
                  f"({len(CASES)} from synth.o + {len(SECOND_CASES)} from second.o)")
            if is_linux_arm64:
                os.chmod(colink_img, 0o755)
                r = subprocess.run([str(colink_img)], capture_output=True)
                ok_n, bad_n = compare("co-linked native", r.stdout, r.returncode, None,
                                      expected + expected2, verbose=False, cases=both)
                same = r.stdout == out_c
                print(f"  {'ok  ' if not bad_n and same else 'FAIL'} co-linked image "
                      f"natively: exit {r.returncode}, {ok_n} values match wasmtime, "
                      f"stdout {'==' if same else '!='} unicorn leg")
                fails += bad_n + (0 if same else 1)
                colink_runs += 1

        # ---- 7b. binding red-first: the LOCAL binding is what makes the link
        #          possible — show the SAME linker still refuses duplicates. ----
        print("== binding red-first (the same linker, the same objects: GLOBAL "
              "duplicates are refused, LOCAL labels are not seen) ==")
        # (a) synth.o with ITSELF: every export collides, no invented name does.
        r = run(ldargs + ["-o", str(tmp / "twice.elf"), str(tmp / "start.o"),
                          str(tmp / "harness.o"), str(obj), str(obj)])
        dup_names = [line.split("duplicate symbol: ", 1)[1].strip()
                     for line in r.stderr.splitlines() if "duplicate symbol: " in line]
        invented_dups = [n for n in dup_names if n.startswith("func_") or n.startswith("__synth_")]
        twice_ok = (r.returncode != 0 and "add" in dup_names and not invented_dups)
        print(f"  {'ok  ' if twice_ok else 'FAIL'} synth.o + synth.o: "
              f"{'refused' if r.returncode else 'LINKED'} — duplicates {sorted(dup_names)}"
              f"{'' if not invented_dups else ' — INVENTED NAMES COLLIDED'}")
        if not twice_ok:
            fails += 1
        # (b) re-globalize func_N in BOTH objects: the v0.64 collision returns.
        objcopy = find_tool("OBJCOPY", "llvm-objcopy", "llvm-objcopy-21",
                            "llvm-objcopy-20", "llvm-objcopy-19", "llvm-objcopy-18")
        binding_control = "skipped"
        if objcopy:
            g1, g2 = tmp / "synth_glob.o", tmp / "second_glob.o"
            r1 = run([objcopy, "--regex", "--globalize-symbol=func_[0-9]+", str(obj), str(g1)])
            r2 = run([objcopy, "--regex", "--globalize-symbol=func_[0-9]+",
                      str(second_obj), str(g2)])
            if r1.returncode != 0 or r2.returncode != 0:
                print(f"  FAIL objcopy --globalize-symbol failed:\n{r1.stderr}{r2.stderr}")
                fails += 1
                binding_control = "objcopy-failed"
            else:
                r = run(ldargs + ["-o", str(tmp / "glob.elf"), str(tmp / "start.o"),
                                  str(tmp / "colink.o"), str(g1), str(g2)])
                refused = r.returncode != 0 and "duplicate symbol: func_1" in r.stderr
                binding_control = "refused" if refused else "LINKED"
                print(f"  {'ok  ' if refused else 'FAIL'} func_N re-globalized in both "
                      f"(`llvm-objcopy --regex --globalize-symbol='func_[0-9]+'`): "
                      f"{'refused, `duplicate symbol: func_1` — the v0.64 collision returns' if refused else 'LINKED — the binding is NOT what prevents the collision'}")
                if not refused:
                    fails += 1
        else:
            print("  skip re-globalize control: no llvm-objcopy on PATH "
                  "(CI installs it and requires `binding red-first: refused`)")

        if executions == 0 or refusals == 0 or colink_runs == 0:
            print(f"VACUOUS: executions={executions} refusals={refusals} "
                  f"colink_runs={colink_runs}")
            return 1
        print(f"\nexecutions: {executions}")
        print(f"host-linker refusals: {refusals}")
        print(f"native-abi runs: {native_runs}")
        print(f"co-link runs: {colink_runs}")
        print(f"binding red-first: {binding_control}")
        print(f"mutation: {'detected' if detected else 'undetected'}")
        if fails:
            print(f"RESULT: FAIL ({fails})")
            return 1
        print("RESULT: PASS")
        return 0
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
