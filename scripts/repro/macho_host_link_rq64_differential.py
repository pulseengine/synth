#!/usr/bin/env python3
# ci-status: wired
# ci-checks: compiles >= 100
"""RQ-64-MACHO — the SAME instruction bytes in a second container: the aarch64
Mach-O `MH_OBJECT` is checked BYTE-IDENTICAL to the ELF `ET_REL` for every
module, then linked by the REAL macOS host linker and EXECUTED against
wasmtime.

THE THESIS THIS ORACLE GATES. Shipping synth output as a normal host library
is blocked by the CONTAINER, not the ISA. `synth -b aarch64 --relocatable`
already emits a SysV ELF64 `ET_REL` that arm64-Linux links and runs
(RQ-64-ARM64LINUX, `arm64_linux_host_link_rq64_differential.py`); macOS cannot
load that container — Apple's `ld` says `unknown file type` — but the code
bytes inside it are already right. `--object-format macho` re-containers the
IDENTICAL plan (same `.text`, same `.data`, same relocation set, same symbols
under Darwin's `_` prefix) as a `CPU_TYPE_ARM64` `MH_OBJECT`. This oracle is
what makes that a claim rather than an assertion, and it is structured so the
cheapest, strongest evidence runs everywhere and the execution evidence runs
where the target host is:

  1. BYTE IDENTITY, on EVERY host (the increment that needs no linker and no
     execution). For the fixture AND for every `.wat` under `scripts/repro/`
     and `tests/` that the aarch64 backend accepts, compile BOTH containers
     and require: the acceptance decision agrees (a container flag must not
     change what compiles), `__TEXT,__text` == `.text` byte for byte,
     `__DATA,__data` == `.data`, the symbol table maps 1:1 (`name` ->
     `_name`, same section class, same offset, and — RQ-65-FUNCN, #1180 —
     the same BINDING: ELF `STB_LOCAL` <-> `N_EXT` clear, `STB_GLOBAL` <->
     `N_EXT` set, with `LC_DYSYMTAB`'s local range exactly the non-`N_EXT`
     prefix), and the relocation SET maps
     1:1 under the ELF->Mach-O type map (`R_AARCH64_CALL26`/`JUMP26` ->
     `ARM64_RELOC_BRANCH26`, `ADR_PREL_PG_HI21` -> `PAGE21`,
     `ADD_ABS_LO12_NC` -> `PAGEOFF12`; every one `r_extern`, `r_length`=2,
     pc-relative exactly where the ELF kind is). A dropped relocation is the
     silent-miscompile class (`bl #0` / `adrp #0`), so the set equality is
     load-bearing, not cosmetic. The Mach-O is parsed by THIS FILE's own
     ~60-line reader (header, load commands, sections, nlist_64, relocs), not
     by a library, so the leg runs on the Linux CI runner too.
  2. MUTATION CONTROL on the identity leg: bit 30 of `add`'s first
     instruction is flipped in the Mach-O `__text` and the identity check
     must REPORT it — a check that cannot fail is not a check (#1113). And a
     BINDING mutation control (RQ-65-FUNCN): `N_EXT` is set on `_func_1` in
     the Mach-O `nlist` and the identity check must report the binding
     disagreement with the ELF twin — the check that would have caught a
     writer deciding binding on its own.
  3. On an arm64-Darwin host (`REQUIRE_NATIVE=1` makes any other host RED,
     never a skip): GENERATE a C harness FROM THE CASE TABLE BELOW (one
     source for the C call sequence and the wasmtime call sequence — a
     hand-mirrored pair would drift; globals persist across calls, so order
     matters), compiled with the HOST clang (`-arch arm64 -ffixed-x28`), plus
     an assembly shim that saves x28, sets it to the linear-memory base,
     calls the C body and restores it. Link all three with the HOST linker
     via the `clang` driver (Apple `ld`, libSystem, ad-hoc code signature —
     the ordinary macOS toolchain, nothing synth-specific). Check the image
     with Apple `nm` (an INDEPENDENT reader, not this file's parser): every
     synth symbol defined, the import bound to the C definition. EXECUTE it
     natively and compare every printed `name=hex` line against a wasmtime
     instance that ran the SAME call sequence with the SAME host `host_add`
     (expected values are never written here).
  4. RED-FIRST, built in, on the Darwin leg: the ELF twin of the very same
     module handed to the macOS linker must be REFUSED (`unknown file type`
     — the container IS the blocker, measured); a harness that omits the
     `host_add` definition must be refused by name (`Undefined symbols …
     "_host_add"`); when `ld.lld` is on PATH the Mach-O handed to
     `-m aarch64linux` must be refused the same way (the containers are
     mutually exclusive, not one a superset); and the MUTATED object from
     step 2 is linked and run and the differential must report a mismatch.
  5. CO-LINK (RQ-65-FUNCN, #1180), on the Darwin leg: a SECOND synth Mach-O
     — `colink_second_rq65.wat`, shaped to define its OWN `_func_1`,
     `___synth_globals` and `___synth_func_table` (the three names two synth
     objects used to collide on; RED if either object lacks one, RED if any
     is `N_EXT`) — is linked into the SAME executable with `synth.o` by
     Apple `ld`, with no objcopy step, checked with `nm`, and EXECUTED with
     every value from BOTH objects compared against wasmtime in one combined
     harness. RED-FIRST: `synth.o` linked with ITSELF must be refused on its
     GLOBAL exports (`duplicate symbol '_add'`) with NO invented name among
     the duplicates — the same linker, in the same link, still refuses
     duplicates; the locals are what it does not see. Before RQ-65-FUNCN
     this step pinned `duplicate symbol '_func_1'` as a documented
     limitation; the pin moved with the doc in the same PR.

WHAT IT DOES NOT VERIFY (stated so the claim cannot outrun its instrument):
  * WASM traps — every case is non-trapping on purpose; `brk #0` is SIGTRAP
    on Darwin and kills an unprepared process. Trap placement is the sibling
    unicorn oracles' business.
  * A dylib / dynamic export. What is linked is an MH_OBJECT into an
    executable with the host's own dynamic libSystem; no `-dylib` link is
    claimed. Every relocation synth emits is PC-relative or PAGEOFF, so a
    dylib link is plausible — and NOT claimed.
  * x86_64 or any CPU type but ARM64. There is no writer for one.
  * Linux/unicorn execution of the Mach-O — Mach-O has no unicorn loader
    here; the Linux-side execution evidence for the same bytes is
    RQ-64-ARM64LINUX's, and step 1 is what ties the two together.

Run (needs the synth binary; on macOS additionally clang/ld/nm and wasmtime):
  SYNTH=<target>/debug/synth python scripts/repro/macho_host_link_rq64_differential.py
"""

import os
import platform
import re
import shutil
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile

HERE = Path(__file__).parent
REPO = HERE.parent.parent
WAT = HERE / "macho_host_link_rq64.wat"
# RQ-65-FUNCN: the second object of the co-link leg (shared with the ELF
# oracle, so both containers prove the same two-object claim).
SECOND_WAT = HERE / "colink_second_rq65.wat"
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

# The names two synth objects used to collide on (#1180), Darwin-prefixed.
CLASH = ["_func_1", "___synth_globals", "___synth_func_table"]

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
LINMEM_BYTES = 65536  # the fixture declares (memory 1)

# --------------------------------------------------------------------------
# THE CASE TABLE — the single source for BOTH the generated C harness and the
# wasmtime reference sequence (the RQ-64-ARM64LINUX table, so the values the
# same bytes produced on arm64-Linux can be read side by side). Kinds:
#   ("call", label, export, [arg types], [args], result type, why)
#   ("peek", label, addr, why)          C reads u32 at linmem+addr; wasmtime reads memory
#   ("poke", label, addr, byte, why)    C writes a byte at linmem+addr; wasmtime writes memory
# --------------------------------------------------------------------------
CASES = [
    ("call", "add", "add", ["i32", "i32"], [3, 4], "i32",
     "host -> synth, w-register args and result (Apple arm64 ABI == AAPCS64 here)"),
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
     "global RMW in synth's own __DATA,__data (placed by the linker)"),
    ("call", "bump10", "bump", ["i32"], [10], "i32",
     "the global PERSISTED across calls"),
    ("call", "acc64", "acc64", ["i64"], [1], "i64",
     "an i64 global slot"),
    ("call", "dispatch_mul", "dispatch", ["i32", "i32", "i32"], [2, 6, 7], "i32",
     "call_indirect through the synth-emitted funcref table (BRANCH26)"),
    ("call", "dispatch_sub", "dispatch", ["i32", "i32", "i32"], [1, 6, 7], "i32",
     "a second slot — the per-slot stride is real"),
    ("call", "via_import", "via_import", ["i32"], [5], "i32",
     "synth -> host: BRANCH26 bound to the C `host_add` (`_host_add`) by ld"),
    ("call", "below_call", "below_call", ["i32", "i32"], [100, 20], "i32",
     "a value below the import call's args survives it (RQ-63-A64STACK)"),
    ("call", "helper_chain", "helper_chain", ["i32"], [50], "i32",
     "synth -> synth: BRANCH26 to a NON-exported local"),
    ("call", "mem_size", "mem_size", [], [], "i32",
     "memory.size is the declared-minimum constant"),
]

# RQ-65-FUNCN: the second object's cases, run AFTER `CASES` in the combined
# harness (labels unique across both tables; the ELF oracle's table, so the
# two containers' co-link values can be read side by side).
SECOND_CASES = [
    ("call", "b_g", "g", ["i32"], [41], "i32",
     "second object: synth -> host, BRANCH26 bound to the SAME C host_add"),
    ("call", "b_acc1", "acc_b", ["i32"], [1], "i32",
     "second object's OWN ___synth_globals (collided when N_EXT)"),
    ("call", "b_acc10", "acc_b", ["i32"], [10], "i32",
     "...and it persists across calls, separately from the first object's"),
    ("call", "b_disp_triple", "disp_b", ["i32", "i32"], [0, 7], "i32",
     "second object's OWN ___synth_func_table (collided when N_EXT)"),
    ("call", "b_disp_neg", "disp_b", ["i32", "i32"], [1, 7], "i32",
     "slot 1 of the second table"),
    ("call", "b_chain", "chain_b", ["i32"], [5], "i32",
     "second object's _func_1/_func_2 via BRANCH26 — non-N_EXT labels, resolved in-object"),
]

CTYPE = {"i32": "int32_t", "i64": "int64_t", "f64": "double"}

# The shim: x28 is callee-saved under the Apple arm64 ABI exactly as under
# AAPCS64, so it is saved, set to the linear-memory base, and restored around
# the whole C body. The body is compiled with -ffixed-x28 so it never
# allocates the register; libSystem's `write` preserves it by the ABI.
SHIM_S = """\
.text
.globl _synth_call_with_x28
.p2align 2
_synth_call_with_x28:            // void synth_call_with_x28(void *base, void (*body)(void))
  stp x29, x30, [sp, #-32]!
  mov x29, sp
  str x28, [sp, #16]
  mov x28, x0
  blr x1
  ldr x28, [sp, #16]
  ldp x29, x30, [sp], #32
  ret
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
#include <unistd.h>
/* GENERATED by macho_host_link_rq64_differential.py from its CASES. */
{chr(10).join(decls.values())}
extern void synth_call_with_x28(void *base, void (*body)(void));

/* The import synth calls OUT to (ordinary C; Darwin symbol `_host_add`). */
{host}
/* Linear memory: the harness owns it; x28 points here (set by the shim). */
__attribute__((aligned(4096))) uint8_t linmem[{LINMEM_BYTES}];

static void emit(const char *name, uint64_t v) {{
  char buf[96]; int n = 0;
  while (*name) buf[n++] = *name++;
  buf[n++] = '=';
  for (int i = 15; i >= 0; i--) buf[n++] = "0123456789abcdef"[(v >> (i * 4)) & 15];
  buf[n++] = '\\n';
  write(1, buf, (size_t)n);
}}
static uint64_t dbits(double d) {{ union {{ double d; uint64_t u; }} u; u.d = d; return u.u; }}
static double dfrom(uint64_t b) {{ union {{ double d; uint64_t u; }} u; u.u = b; return u.d; }}

static void harness_body(void) {{
{chr(10).join(body)}
}}

int main(void) {{
  synth_call_with_x28(linmem, harness_body);
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


def compile_synth(wat, out, fmt="elf", backend="aarch64"):
    cmd = [SYNTH, "compile", str(wat), "-o", str(out), "--relocatable", "--all-exports"]
    if backend == "aarch64":
        cmd += ["-b", "aarch64", "--target", "cortex-a53"]
    if fmt != "elf":
        cmd += ["--object-format", fmt]
    return subprocess.run(cmd, capture_output=True, text=True,
                          env={"PATH": "/usr/bin:/bin"})


def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


# --------------------------------------------------------------------------
# The ELF side (pyelftools) — what RQ-64-ARM64LINUX links.
# --------------------------------------------------------------------------
ELF_TO_MACHO_RELOC = {
    "R_AARCH64_CALL26": ("ARM64_RELOC_BRANCH26", True),
    "R_AARCH64_JUMP26": ("ARM64_RELOC_BRANCH26", True),
    "R_AARCH64_ADR_PREL_PG_HI21": ("ARM64_RELOC_PAGE21", True),
    "R_AARCH64_ADD_ABS_LO12_NC": ("ARM64_RELOC_PAGEOFF12", False),
}


def read_elf(path):
    f = ELFFile(open(path, "rb"))
    text = f.get_section_by_name(".text")
    data = f.get_section_by_name(".data")
    symtab = f.get_section_by_name(".symtab")
    syms = {}
    by_index = []
    for sy in symtab.iter_symbols():
        by_index.append(sy.name)
        if not sy.name:
            continue
        shndx = sy["st_shndx"]
        if shndx == "SHN_UNDEF":
            cls = "undef"
        elif shndx == text["sh_name"] or f.get_section(shndx).name == ".text":
            cls = "text"
        elif f.get_section(shndx).name == ".data":
            cls = "data"
        else:
            cls = f"other:{shndx}"
        # RQ-65-FUNCN: the binding is part of the identity — STB_LOCAL must
        # come out as N_EXT-clear in the Mach-O, STB_GLOBAL as N_EXT-set.
        bind = "local" if sy["st_info"]["bind"] == "STB_LOCAL" else "global"
        syms[sy.name] = (cls, sy["st_value"], bind)
    relocs = set()
    rela = f.get_section_by_name(".rela.text")
    if rela is not None:
        for r in rela.iter_relocations():
            ty = r["r_info_type"]
            name = by_index[r["r_info_sym"]]
            from elftools.elf.enums import ENUM_RELOC_TYPE_AARCH64
            tyname = next(k for k, v in ENUM_RELOC_TYPE_AARCH64.items() if v == ty)
            relocs.add((r["r_offset"], tyname, name))
    return {
        "text": text.data(),
        "data": data.data() if data is not None else b"",
        "syms": syms,
        "relocs": relocs,
    }


# --------------------------------------------------------------------------
# The Mach-O side — this file's own reader. Deliberately not a library, so the
# identity leg runs on any host and the leg does not inherit a parser's idea
# of what is "valid" (a parser that fills in defaults hides a missing field).
# --------------------------------------------------------------------------
MH_MAGIC_64 = 0xFEEDFACF
CPU_TYPE_ARM64 = 0x0100000C
MH_OBJECT, MH_EXECUTE = 1, 2
LC_SEGMENT_64, LC_SYMTAB, LC_DYSYMTAB, LC_BUILD_VERSION = 0x19, 0x2, 0xB, 0x32
N_EXT, N_TYPE, N_UNDF, N_SECT = 0x01, 0x0E, 0x00, 0x0E
ARM64_RELOC_NAMES = {0: "ARM64_RELOC_UNSIGNED", 1: "ARM64_RELOC_SUBTRACTOR",
                     2: "ARM64_RELOC_BRANCH26", 3: "ARM64_RELOC_PAGE21",
                     4: "ARM64_RELOC_PAGEOFF12", 10: "ARM64_RELOC_ADDEND"}


def parse_macho(data):
    """Header, load commands, sections (with their relocations), symbols."""
    magic, cputype, cpusubtype, filetype, ncmds, sizeofcmds, flags, _ = \
        struct.unpack_from("<IIIIIIII", data, 0)
    mo = {"magic": magic, "cputype": cputype, "cpusubtype": cpusubtype,
          "filetype": filetype, "flags": flags, "cmds": [], "sections": [],
          "symbols": [], "dysymtab": None, "build_version": None}
    off = 32
    symtab_cmd = None
    for _ in range(ncmds):
        cmd, cmdsize = struct.unpack_from("<II", data, off)
        mo["cmds"].append(cmd)
        if cmd == LC_SEGMENT_64:
            (segname, vmaddr, vmsize, fileoff, filesize, maxprot, initprot,
             nsects, segflags) = struct.unpack_from("<16sQQQQiiII", data, off + 8)
            mo["segment"] = {"name": segname.rstrip(b"\0").decode(), "vmaddr": vmaddr,
                             "vmsize": vmsize, "fileoff": fileoff,
                             "filesize": filesize, "nsects": nsects}
            so = off + 72
            for _s in range(nsects):
                (sectname, sname, addr, size, soff, align, reloff, nreloc,
                 sflags) = struct.unpack_from("<16s16sQQIIIII", data, so)
                sec = {"name": sectname.rstrip(b"\0").decode(),
                       "seg": sname.rstrip(b"\0").decode(), "addr": addr,
                       "size": size, "offset": soff, "align": align,
                       "flags": sflags, "relocs": []}
                sec["bytes"] = data[soff:soff + size]
                for i in range(nreloc):
                    r_address, packed = struct.unpack_from("<iI", data, reloff + 8 * i)
                    sec["relocs"].append({
                        "address": r_address,
                        "symbolnum": packed & 0xFFFFFF,
                        "pcrel": (packed >> 24) & 1,
                        "length": (packed >> 25) & 3,
                        "extern": (packed >> 27) & 1,
                        "type": (packed >> 28) & 0xF,
                    })
                mo["sections"].append(sec)
                so += 80
        elif cmd == LC_SYMTAB:
            symtab_cmd = struct.unpack_from("<IIII", data, off + 8)
        elif cmd == LC_DYSYMTAB:
            v = struct.unpack_from("<18I", data, off + 8)
            mo["dysymtab"] = {"ilocalsym": v[0], "nlocalsym": v[1],
                              "iextdefsym": v[2], "nextdefsym": v[3],
                              "iundefsym": v[4], "nundefsym": v[5]}
        elif cmd == LC_BUILD_VERSION:
            plat, minos, sdk, ntools = struct.unpack_from("<IIII", data, off + 8)
            mo["build_version"] = {"platform": plat, "minos": minos, "sdk": sdk,
                                   "ntools": ntools}
        off += cmdsize
    mo["symtab"] = symtab_cmd
    if symtab_cmd:
        symoff, nsyms, stroff, strsize = symtab_cmd
        strtab = data[stroff:stroff + strsize]
        for i in range(nsyms):
            n_strx, n_type, n_sect, n_desc, n_value = \
                struct.unpack_from("<IBBHQ", data, symoff + 16 * i)
            end = strtab.index(b"\0", n_strx)
            mo["symbols"].append({"name": strtab[n_strx:end].decode(),
                                  "type": n_type, "sect": n_sect,
                                  "desc": n_desc, "value": n_value})
    return mo


def macho_view(mo):
    """The Mach-O reduced to the same shape `read_elf` returns, so the two
    can be compared field by field. Symbol names keep their `_`."""
    secs = {s["name"]: s for s in mo["sections"]}
    text = secs.get("__text")
    data = secs.get("__data")
    # section ordinals are 1-based in section order
    ordinal = {i + 1: s["name"] for i, s in enumerate(mo["sections"])}
    syms = {}
    for sy in mo["symbols"]:
        bind = "global" if sy["type"] & N_EXT else "local"
        if (sy["type"] & N_TYPE) == N_UNDF:
            syms[sy["name"]] = ("undef", 0, bind)
        elif (sy["type"] & N_TYPE) == N_SECT:
            sec = secs[ordinal[sy["sect"]]]
            cls = {"__text": "text", "__data": "data"}.get(sec["name"], sec["name"])
            syms[sy["name"]] = (cls, sy["value"] - sec["addr"], bind)
    relocs = set()
    problems = []
    if text is not None:
        for r in text["relocs"]:
            tyname = ARM64_RELOC_NAMES.get(r["type"], f"type{r['type']}")
            if not r["extern"]:
                problems.append(f"reloc at __text+{r['address']:#x} is not r_extern")
            if r["length"] != 2:
                problems.append(f"reloc at __text+{r['address']:#x} r_length {r['length']} != 2")
            if r["symbolnum"] >= len(mo["symbols"]):
                problems.append(f"reloc at __text+{r['address']:#x} symbol index out of range")
                continue
            relocs.add((r["address"], tyname, r["pcrel"],
                        mo["symbols"][r["symbolnum"]]["name"]))
    return {
        "text": text["bytes"] if text is not None else None,
        "data": data["bytes"] if data is not None else b"",
        "syms": syms,
        "relocs": relocs,
        "problems": problems,
    }


def check_macho_structure(mo):
    p = []
    if mo["magic"] != MH_MAGIC_64:
        p.append(f"magic {mo['magic']:#x} != MH_MAGIC_64")
    if mo["cputype"] != CPU_TYPE_ARM64:
        p.append(f"cputype {mo['cputype']:#x} != CPU_TYPE_ARM64")
    if mo["filetype"] != MH_OBJECT:
        p.append(f"filetype {mo['filetype']} != MH_OBJECT")
    names = [s["name"] for s in mo["sections"]]
    if not names or names[0] != "__text" or mo["sections"][0]["seg"] != "__TEXT":
        p.append(f"first section is {names[:1]} not __TEXT,__text")
    for s in mo["sections"]:
        if s["name"] == "__text" and (s["flags"] & 0x80000400) != 0x80000400:
            p.append("__text lacks S_ATTR_PURE_INSTRUCTIONS|S_ATTR_SOME_INSTRUCTIONS")
        if s["name"] == "__data" and s["seg"] != "__DATA":
            p.append("__data is not in __DATA")
    if mo["build_version"] is None:
        p.append("no LC_BUILD_VERSION (Apple ld would assume a platform)")
    if LC_SYMTAB not in mo["cmds"]:
        p.append("no LC_SYMTAB")
    d = mo["dysymtab"]
    if d is None:
        p.append("no LC_DYSYMTAB")
    else:
        n = len(mo["symbols"])
        if d["ilocalsym"] + d["nlocalsym"] != d["iextdefsym"] or \
           d["iextdefsym"] + d["nextdefsym"] != d["iundefsym"] or \
           d["iundefsym"] + d["nundefsym"] != n:
            p.append(f"LC_DYSYMTAB ranges do not tile the {n} symbols: {d}")
        for i, sy in enumerate(mo["symbols"]):
            undef = (sy["type"] & N_TYPE) == N_UNDF
            ext = bool(sy["type"] & N_EXT)
            in_undef_range = d["iundefsym"] <= i < d["iundefsym"] + d["nundefsym"]
            if undef != in_undef_range:
                p.append(f"symbol {sy['name']} ({'undef' if undef else 'defined'}) "
                         f"sits outside its LC_DYSYMTAB range")
            # RQ-65-FUNCN: the LC_DYSYMTAB local range must be EXACTLY the
            # non-N_EXT symbols (locals first), and an undefined symbol must
            # be external — the Mach-O half of the ELF locals-first/sh_info
            # rule, read off the plan by the writer.
            in_local_range = d["ilocalsym"] <= i < d["ilocalsym"] + d["nlocalsym"]
            if (not ext) != in_local_range:
                p.append(f"symbol {sy['name']} ({'N_EXT' if ext else 'local'}) "
                         f"{'sits outside' if not ext else 'sits inside'} the LC_DYSYMTAB local range")
            if undef and not ext:
                p.append(f"undefined symbol {sy['name']} is not N_EXT")
    return p


def identity_problems(elf, mv):
    """The load-bearing comparison: everything the ELF says, the Mach-O says."""
    p = []
    if mv["text"] is None:
        return ["Mach-O has no __text"]
    if elf["text"] != mv["text"]:
        n = next((i for i, (a, b) in enumerate(zip(elf["text"], mv["text"])) if a != b),
                 min(len(elf["text"]), len(mv["text"])))
        p.append(f".text != __text (len {len(elf['text'])} vs {len(mv['text'])}, "
                 f"first difference at +{n:#x})")
    if elf["data"] != mv["data"]:
        p.append(f".data != __data ({len(elf['data'])} vs {len(mv['data'])} bytes)")
    want_syms = {"_" + k: v for k, v in elf["syms"].items()}
    if want_syms != mv["syms"]:
        only_elf = sorted(set(want_syms) - set(mv["syms"]))
        only_mo = sorted(set(mv["syms"]) - set(want_syms))
        both = set(want_syms) & set(mv["syms"])
        diff = sorted(k for k in both if want_syms[k][:2] != mv["syms"][k][:2])
        bind_diff = sorted(f"{k}: ELF {want_syms[k][2]} vs Mach-O {mv['syms'][k][2]}"
                           for k in both if want_syms[k][:2] == mv["syms"][k][:2]
                           and want_syms[k][2] != mv["syms"][k][2])
        p.append(f"symbols differ: only-ELF={only_elf} only-MachO={only_mo} "
                 f"class/offset-differ={diff} binding-differs={bind_diff}")
    want_relocs = set()
    for off, ty, name in elf["relocs"]:
        mty, pcrel = ELF_TO_MACHO_RELOC[ty]
        want_relocs.add((off, mty, int(pcrel), "_" + name))
    if want_relocs != mv["relocs"]:
        p.append(f"relocation sets differ: ELF-mapped-only={sorted(want_relocs - mv['relocs'])} "
                 f"MachO-only={sorted(mv['relocs'] - want_relocs)}")
    p.extend(mv["problems"])
    return p


def compare_containers(elf_path, macho_path):
    elf = read_elf(elf_path)
    mo = parse_macho(Path(macho_path).read_bytes())
    mv = macho_view(mo)
    return check_macho_structure(mo) + identity_problems(elf, mv), elf, mo


def mutate_binding(data, name):
    """RQ-65-FUNCN mutation control: set N_EXT on the nlist entry of `name`
    (a writer deciding binding on its own would look exactly like this)."""
    mo = parse_macho(data)
    symoff = mo["symtab"][0]
    out = bytearray(data)
    for i, sy in enumerate(mo["symbols"]):
        if sy["name"] == name:
            out[symoff + 16 * i + 4] |= N_EXT
            return bytes(out)
    raise KeyError(name)


def defined_names(mo, local_only=False):
    """Section-defined symbol names of a parsed Mach-O (optionally only the
    non-N_EXT ones)."""
    return {s["name"] for s in mo["symbols"]
            if (s["type"] & N_TYPE) == N_SECT and (not local_only or not (s["type"] & N_EXT))}


# --------------------------------------------------------------------------
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


def compare(tag, stdout, exit_code, expected, verbose=True, cases=CASES):
    """Diff the harness output against wasmtime. Returns (#ok, #fail)."""
    if exit_code != 0:
        print(f"  FAIL [{tag}] exit status {exit_code} != 0 "
              f"({'signal ' + str(-exit_code) if exit_code < 0 else 'nonzero'})")
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


def nm_symbols(nm, path):
    """Apple nm: (defined names, undefined names)."""
    r = run([nm, str(path)])
    defined, undefined = set(), set()
    for line in r.stdout.splitlines():
        parts = line.split()
        if len(parts) == 2 and parts[0] == "U":
            undefined.add(parts[1])
        elif len(parts) == 3:
            defined.add(parts[2])
    return r.returncode, defined, undefined


def fixture_corpus():
    wats = sorted(REPO.glob("scripts/repro/*.wat")) + sorted(REPO.glob("tests/**/*.wat"))
    return [w for w in wats if w.resolve() != WAT.resolve()]


# --------------------------------------------------------------------------
def main():
    tmp = Path(tempfile.mkdtemp(prefix="rq64macho-"))
    fails = 0
    try:
        # ---- 1. the object under test, in BOTH containers -------------------
        print("== compile: synth -b aarch64 --target cortex-a53 --relocatable "
              "(ELF) and --object-format macho (Mach-O) ==")
        elf_obj = tmp / "synth_elf.o"
        mo_obj = tmp / "synth.o"
        r = compile_synth(WAT, elf_obj, "elf")
        if r.returncode != 0 or "skipping" in r.stderr or not elf_obj.exists():
            print(f"RED: ELF compile failed/declined:\n{r.stdout}\n{r.stderr}")
            return 1
        r = compile_synth(WAT, mo_obj, "macho")
        if r.returncode != 0 or "skipping" in r.stderr or not mo_obj.exists():
            print(f"RED: --object-format macho compile failed/declined "
                  f"(exit {r.returncode}):\n{r.stdout}\n{r.stderr}")
            return 1
        problems, elf, mo = compare_containers(elf_obj, mo_obj)
        for p in problems:
            print(f"  FAIL identity/structure: {p}")
        fails += len(problems)
        if not problems:
            print(f"  ok   .text == __text ({len(elf['text'])} bytes), .data == __data "
                  f"({len(elf['data'])} bytes), {len(elf['syms'])} symbols map 1:1, "
                  f"{len(elf['relocs'])} relocations map 1:1 "
                  f"(MH_OBJECT CPU_TYPE_ARM64, {len(mo['sections'])} sections, "
                  f"LC_BUILD_VERSION platform {mo['build_version']['platform']})")
        add_off = elf["syms"]["add"][1]
        word = struct.unpack_from("<I", elf["text"], add_off)[0]

        # ---- 2. the corpus sweep ------------------------------------------
        print("== byte-identity sweep: every repo .wat the aarch64 backend accepts, "
              "both containers ==")
        identical = disagree = swept = 0
        for w in fixture_corpus():
            e = tmp / "sweep_elf.o"
            m = tmp / "sweep_macho.o"
            for f in (e, m):
                if f.exists():
                    f.unlink()
            re_ = compile_synth(w, e, "elf")
            rm_ = compile_synth(w, m, "macho")
            acc_e = re_.returncode == 0 and e.exists()
            acc_m = rm_.returncode == 0 and m.exists()
            if acc_e != acc_m:
                disagree += 1
                print(f"  FAIL acceptance differs for {w.relative_to(REPO)}: "
                      f"elf={'accepted' if acc_e else 'declined'} "
                      f"macho={'accepted' if acc_m else 'declined'}\n"
                      f"       {(rm_ if acc_e else re_).stderr.strip()[:300]}")
                continue
            if not acc_e:
                continue
            swept += 1
            probs, _, _ = compare_containers(e, m)
            if probs:
                print(f"  FAIL {w.relative_to(REPO)}: {probs[0]}")
                fails += 1
            else:
                identical += 1
        print(f"  {swept} modules accepted by both containers, {identical} byte-identical, "
              f"{disagree} acceptance disagreements")
        fails += disagree
        if swept == 0:
            print("VACUOUS: the sweep compiled nothing")
            return 1

        # ---- 3. identity mutation control -----------------------------------
        print("== identity mutation control (can the identity check fail?) ==")
        mutated = tmp / "mutated.o"
        mdata = bytearray(mo_obj.read_bytes())
        text_sec = next(s for s in mo["sections"] if s["name"] == "__text")
        moff = text_sec["offset"] + add_off
        assert struct.unpack_from("<I", mdata, moff)[0] == word
        struct.pack_into("<I", mdata, moff, word ^ (1 << 30))  # ADD(shifted) -> SUB
        mutated.write_bytes(mdata)
        mprobs, _, _ = compare_containers(elf_obj, mutated)
        id_detected = any(".text != __text" in p for p in mprobs)
        print(f"  {'ok  ' if id_detected else 'FAIL'} flipped bit 30 of `add`'s first "
              f"instruction in __text ({word:#010x} -> {word ^ (1 << 30):#010x}): "
              f"{'identity mismatch reported' if id_detected else 'NOT DETECTED — the check is vacuous'}")
        if not id_detected:
            fails += 1
        # RQ-65-FUNCN: can the identity check see a BINDING disagreement? Set
        # N_EXT on `_func_1` in the Mach-O (the ELF twin says STB_LOCAL): the
        # per-symbol identity must report it, and the LC_DYSYMTAB local range
        # now holds an external symbol, which the structure check must also
        # report.
        print("== binding mutation control (can the identity check see a writer "
              "deciding binding on its own?) ==")
        mutated_b = tmp / "mutated_binding.o"
        mutated_b.write_bytes(mutate_binding(mo_obj.read_bytes(), "_func_1"))
        bprobs, _, _ = compare_containers(elf_obj, mutated_b)
        bind_detected = any("_func_1" in p and ("binding" in p or "local range" in p)
                            for p in bprobs)
        print(f"  {'ok  ' if bind_detected else 'FAIL'} N_EXT set on `_func_1` in the nlist: "
              f"{'binding disagreement reported' if bind_detected else 'NOT DETECTED — the binding check is vacuous'}")
        if bind_detected:
            print(f"       {next(p for p in bprobs if '_func_1' in p)[:160]}")
        else:
            fails += 1

        # ---- 4. the Darwin leg: host link + native execution -----------------
        is_darwin_arm64 = platform.system() == "Darwin" and platform.machine() == "arm64"
        executions = refusals = native_runs = colink_runs = 0
        exec_detected = None
        binding_control = "not-run"
        clang = find_tool("CLANG", "clang")
        nm = find_tool("NM", "nm")
        if is_darwin_arm64 and clang and nm:
            print("== host link: clang -arch arm64 -ffixed-x28 (Apple ld, libSystem, "
                  "ad-hoc signed) ==")
            (tmp / "shim.s").write_text(SHIM_S)
            (tmp / "harness.c").write_text(gen_harness_c())
            (tmp / "harness_nohost.c").write_text(gen_harness_c(with_host_add=False))
            cflags = ["-arch", "arm64", "-O2", "-ffixed-x28", "-c"]
            for src, out in (("shim.s", "shim.o"), ("harness.c", "harness.o"),
                             ("harness_nohost.c", "harness_nohost.o")):
                r = run([clang] + cflags + [str(tmp / src), "-o", str(tmp / out)])
                if r.returncode != 0:
                    print(f"RED: clang failed on {src}:\n{r.stderr}")
                    return 1
            image = tmp / "harness"
            link = [clang, "-arch", "arm64", "-o"]
            r = run(link + [str(image), str(tmp / "shim.o"), str(tmp / "harness.o"),
                            str(mo_obj)])
            if r.returncode != 0:
                print(f"RED: the macOS linker refused the synth Mach-O:\n{r.stderr}")
                return 1
            if r.stderr.strip():
                print(f"  linker stderr (warnings are findings, not noise):\n"
                      f"       {r.stderr.strip()[:400]}")
            rc, defined, undefined = nm_symbols(nm, image)
            want = {"_" + s for s in elf["syms"] if elf["syms"][s][0] != "undef"} | \
                   {"_host_add", "_main", "_synth_call_with_x28", "_linmem"}
            missing = sorted(want - defined)
            still_undef = sorted(("_" + s for s in elf["syms"] if elf["syms"][s][0] == "undef"
                                  and "_" + s in undefined))
            hdr = parse_macho(image.read_bytes())
            img_probs = []
            if hdr["filetype"] != MH_EXECUTE:
                img_probs.append(f"linked filetype {hdr['filetype']} != MH_EXECUTE")
            if hdr["cputype"] != CPU_TYPE_ARM64:
                img_probs.append("linked cputype != ARM64")
            if rc != 0:
                img_probs.append(f"nm exit {rc}")
            if missing:
                img_probs.append(f"symbols missing from the image (nm): {missing}")
            if still_undef:
                img_probs.append(f"synth imports still undefined in the image: {still_undef}")
            for p in img_probs:
                print(f"  FAIL image: {p}")
            fails += len(img_probs)
            if not img_probs:
                print(f"  image: MH_EXECUTE CPU_TYPE_ARM64, nm sees {len(defined)} defined "
                      f"symbols incl. all {len(want)} wanted; libSystem undefineds: "
                      f"{len(undefined)}")

            # ---- 5. wasmtime first, then run the thing itself ----------------
            expected = wasmtime_expected()
            print("== execution differential: native arm64-macOS vs wasmtime ==")
            r = subprocess.run([str(image)], capture_output=True)
            ok, bad = compare("native", r.stdout, r.returncode, expected)
            fails += bad
            executions = ok + bad
            native_runs = 1

            # ---- 6a. host-linker refusals (red-first) -----------------------
            print("== host-linker refusals (red-first: the ELF twin and a missing "
                  "import must be REFUSED by name) ==")
            probes = [
                ("the ELF twin (same bytes, wrong container) into Apple ld",
                 link + [str(tmp / "n1"), str(tmp / "shim.o"), str(tmp / "harness.o"),
                         str(elf_obj)],
                 "unknown file type"),
                ("harness without a host_add definition",
                 link + [str(tmp / "n2"), str(tmp / "shim.o"),
                         str(tmp / "harness_nohost.o"), str(mo_obj)],
                 '"_host_add"'),
            ]
            lld = find_tool("LLD", "ld.lld")
            if lld:
                probes.append(("the Mach-O into ld.lld -m aarch64linux",
                               [lld, "-m", "aarch64linux", "-o", str(tmp / "n3"),
                                str(mo_obj)],
                               "unknown file type"))
            else:
                print("  skip ld.lld reverse-refusal: no ld.lld on PATH (set LLD=)")
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

            # ---- 6b. execution mutation control -------------------------------
            print("== execution mutation control (the mutated object, linked and run) ==")
            r = run(link + [str(tmp / "mut"), str(tmp / "shim.o"), str(tmp / "harness.o"),
                            str(mutated)])
            if r.returncode != 0:
                print(f"  FAIL the mutated object did not link:\n{r.stderr[:300]}")
                fails += 1
                exec_detected = False
            else:
                r = subprocess.run([str(tmp / "mut")], capture_output=True)
                ok_m, bad_m = compare("mutated", r.stdout, r.returncode, expected,
                                      verbose=False)
                exec_detected = bad_m > 0
                print(f"  {'ok  ' if exec_detected else 'FAIL'} mutated `add` executed: "
                      f"{'mismatch reported' if exec_detected else 'NOT DETECTED — the check is vacuous'}")
                if not exec_detected:
                    fails += 1

            # ---- 7. co-link (RQ-65-FUNCN, #1180): two synth Mach-O objects ----
            # Before RQ-65-FUNCN every symbol was N_EXT and this step PINNED
            # `duplicate symbol '_func_1'`. The plan now carries binding, so a
            # second object that defines all three formerly-colliding names
            # itself links unaided with Apple ld — and the pair must EXECUTE.
            print("== co-link (RQ-65-FUNCN): synth.o + second.o — its own _func_1, "
                  "___synth_globals, ___synth_func_table — link UNAIDED (Apple ld) "
                  "and execute ==")
            second_obj = tmp / "second.o"
            r = compile_synth(SECOND_WAT, second_obj, "macho")
            if r.returncode != 0 or "skipping" in r.stderr or not second_obj.exists():
                print(f"RED: the second object failed/declined:\n{r.stdout}\n{r.stderr}")
                return 1
            mo2 = parse_macho(second_obj.read_bytes())
            probs2 = check_macho_structure(mo2)
            for p in probs2:
                print(f"  FAIL second.o structure: {p}")
            fails += len(probs2)
            # Non-vacuity: the collision surface must EXIST in both objects,
            # and be non-N_EXT in both.
            missing = [c for c in CLASH if c not in defined_names(mo) or c not in defined_names(mo2)]
            if missing:
                print(f"  FAIL both objects must define {CLASH}; missing: {missing}")
                fails += 1
            ext_clash = [c for c in CLASH
                         if c not in defined_names(mo, local_only=True)
                         or c not in defined_names(mo2, local_only=True)]
            if ext_clash:
                print(f"  FAIL these must be non-N_EXT in both objects: {ext_clash}")
                fails += 1
            if not missing and not ext_clash:
                print(f"  ok   both objects define {CLASH}, all non-N_EXT "
                      f"(synth.o: {len(defined_names(mo, True))} local / "
                      f"{len(defined_names(mo)) - len(defined_names(mo, True))} external defined; "
                      f"second.o: {len(defined_names(mo2, True))} / "
                      f"{len(defined_names(mo2)) - len(defined_names(mo2, True))})")
            (tmp / "colink.c").write_text(gen_harness_c(cases=CASES + SECOND_CASES))
            r = run([clang] + cflags + [str(tmp / "colink.c"), "-o", str(tmp / "colink.o")])
            if r.returncode != 0:
                print(f"RED: clang failed on colink.c:\n{r.stderr}")
                return 1
            colink_img = tmp / "colink"
            r = run(link + [str(colink_img), str(tmp / "shim.o"), str(tmp / "colink.o"),
                            str(mo_obj), str(second_obj)])
            if r.returncode != 0:
                print(f"  FAIL synth.o + second.o: REFUSED (exit {r.returncode}) — "
                      f"{r.stderr.strip()[:300]}")
                fails += 1
            else:
                print("  ok   synth.o + second.o: LINKED (Apple ld, no objcopy)")
                rc, defined_c, undefined_c = nm_symbols(nm, colink_img)
                want_c = want | defined_names(mo2)
                missing_c = sorted(want_c - defined_c)
                if rc != 0 or missing_c:
                    print(f"  FAIL co-linked image: nm exit {rc}, missing {missing_c}")
                    fails += 1
                else:
                    print(f"  image: MH_EXECUTE, nm sees all {len(want_c)} wanted symbols "
                          f"from both objects")
                expected2 = wasmtime_expected(SECOND_WAT, SECOND_CASES)
                both = CASES + SECOND_CASES
                r = subprocess.run([str(colink_img)], capture_output=True)
                ok_c, bad_c = compare("co-linked", r.stdout, r.returncode,
                                      expected + expected2, verbose=True, cases=both)
                fails += bad_c
                colink_runs = 1
                print(f"  {'ok  ' if not bad_c else 'FAIL'} co-linked image executed "
                      f"natively: {ok_c} of {len(both)} values match wasmtime "
                      f"({len(CASES)} from synth.o + {len(SECOND_CASES)} from second.o)")

            # ---- 7b. binding red-first: synth.o with ITSELF — the same linker
            #          refuses its GLOBAL exports and does not see its locals. --
            print("== binding red-first (the same linker, the same object twice: "
                  "N_EXT duplicates refused, non-N_EXT labels not seen) ==")
            r = run(link + [str(tmp / "twice"), str(tmp / "shim.o"), str(tmp / "harness.o"),
                            str(mo_obj), str(mo_obj)])
            dup_names = re.findall(r"duplicate symbol '([^']+)'", r.stderr)
            invented_dups = [n for n in dup_names
                             if n.startswith("_func_") or n.startswith("___synth_")]
            twice_ok = r.returncode != 0 and "_add" in dup_names and not invented_dups
            binding_control = "refused" if twice_ok else "LINKED"
            print(f"  {'ok  ' if twice_ok else 'FAIL'} synth.o + synth.o: "
                  f"{'refused' if r.returncode else 'LINKED'} — duplicates {sorted(dup_names)}"
                  f"{'' if not invented_dups else ' — INVENTED NAMES COLLIDED'}")
            if not twice_ok:
                fails += 1
        elif os.environ.get("REQUIRE_NATIVE") == "1":
            print(f"  FAIL REQUIRE_NATIVE=1 but host is {platform.system()}/"
                  f"{platform.machine()} clang={clang} nm={nm}")
            fails += 1
        else:
            print(f"== skip host link + execution: host is {platform.system()}/"
                  f"{platform.machine()} (clang={clang}, nm={nm}); set REQUIRE_NATIVE=1 "
                  f"on an arm64-macOS runner ==")

        print(f"\nbyte-identical modules: {identical + (0 if problems else 1)}")
        print(f"acceptance disagreements: {disagree}")
        print(f"identity mutation: {'detected' if id_detected else 'undetected'}")
        print(f"binding mutation: {'detected' if bind_detected else 'undetected'}")
        print(f"executions: {executions}")
        print(f"host-linker refusals: {refusals}")
        print(f"native-abi runs: {native_runs}")
        print(f"co-link runs: {colink_runs}")
        print(f"binding red-first: {binding_control}")
        print(f"mutation: {'detected' if exec_detected else ('undetected' if exec_detected is False else 'not-run')}")
        if fails:
            print(f"RESULT: FAIL ({fails})")
            return 1
        print("RESULT: PASS")
        return 0
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
