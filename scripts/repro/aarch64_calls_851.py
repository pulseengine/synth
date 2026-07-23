#!/usr/bin/env python3
"""synth aarch64 direct-`call` execution differential (#851, lane L3).

The standing gate `aarch64_matrix.sh` is single-function (it loads only the
`.text` of one function), so it cannot exercise CALLS. This harness compiles a
MULTI-function module with `synth -b aarch64 --relocatable`, resolves the
R_AARCH64_CALL26 relocations itself (patching each `bl` imm26 for the concatenated
layout), loads the combined blob into MAP_JIT executable memory, runs the
exported entry, and diffs the result bit-exact against wasmtime.

RED before the lane: the module DECLINES (aarch64 loud-skips `call`) → synth
compile fails → this harness reports the compile error (no green run possible).
GREEN after: bit-identical to wasmtime.

Requires an arm64 host (Apple Silicon / Linux arm64), clang, wasm-tools,
wasmtime. Env: SYNTH, WASMTIME, WASMTOOLS (defaults on PATH). Exits non-zero on
any MISCOMPILE or on a call module that should compile but declines.
"""
import os
import struct
import subprocess
import sys
import tempfile

SYNTH = os.environ.get("SYNTH", "synth")
WASMTIME = os.environ.get("WASMTIME", "wasmtime")
WASMTOOLS = os.environ.get("WASMTOOLS", "wasm-tools")

R_AARCH64_CALL26 = 283

# --- native MAP_JIT runner: loads a full multi-function blob, calls it at
#     entry offset 0 (the harness places the entry function first). ---
RUNNER_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <sys/mman.h>
#ifdef __APPLE__
#include <pthread.h>
#endif
int main(int c, char** v){
  // argv: <hexblob> <a> <b> ...  up to 4 i64 args. Entry is at blob offset 0.
  if(c < 2){ fprintf(stderr,"usage: %s <hex> [args...]\n", v[0]); return 2; }
  size_t n = strlen(v[1])/2; uint8_t* code = malloc(n);
  for(size_t i=0;i<n;i++){ unsigned b; sscanf(v[1]+2*i,"%2x",&b); code[i]=(uint8_t)b; }
  int mf = MAP_PRIVATE|MAP_ANON;
#ifdef MAP_JIT
  mf |= MAP_JIT;
#endif
  size_t pg = (n + 4095) & ~((size_t)4095);
  void* m = mmap(0, pg, PROT_READ|PROT_WRITE|PROT_EXEC, mf, -1, 0);
  if(m==MAP_FAILED){ perror("mmap"); return 2; }
#ifdef __APPLE__
  pthread_jit_write_protect_np(0); memcpy(m, code, n); pthread_jit_write_protect_np(1);
#else
  memcpy(m, code, n);
#endif
  __builtin___clear_cache((char*)m, (char*)m+n);
  long a0 = c>2 ? strtoll(v[2],0,10) : 0;
  long a1 = c>3 ? strtoll(v[3],0,10) : 0;
  long a2 = c>4 ? strtoll(v[4],0,10) : 0;
  long a3 = c>5 ? strtoll(v[5],0,10) : 0;
  long (*fn)(long,long,long,long) = (void*)m;
  printf("%lld\n", (long long)fn(a0,a1,a2,a3));
  return 0;
}
"""


def sh(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def parse_elf(path):
    """Minimal ELF64 parser: returns (text_bytes, {symname:(value,size)},
    [(r_offset, sym_value, sym_size)] for CALL26 relocs)."""
    with open(path, "rb") as f:
        data = f.read()
    assert data[:4] == b"\x7fELF", "not ELF"
    assert data[4] == 2, "not ELF64"
    e_shoff = struct.unpack_from("<Q", data, 40)[0]
    e_shentsize = struct.unpack_from("<H", data, 58)[0]
    e_shnum = struct.unpack_from("<H", data, 60)[0]
    e_shstrndx = struct.unpack_from("<H", data, 62)[0]

    secs = []
    for i in range(e_shnum):
        base = e_shoff + i * e_shentsize
        (sh_name, sh_type, sh_flags, sh_addr, sh_offset, sh_size, sh_link,
         sh_info, sh_align, sh_entsize) = struct.unpack_from("<IIQQQQIIQQ", data, base)
        secs.append(dict(name=sh_name, type=sh_type, offset=sh_offset,
                         size=sh_size, link=sh_link, info=sh_info,
                         entsize=sh_entsize))
    shstr = secs[e_shstrndx]
    shstrtab = data[shstr["offset"]:shstr["offset"] + shstr["size"]]

    def secname(s):
        end = shstrtab.index(b"\0", s["name"])
        return shstrtab[s["name"]:end].decode()

    named = {secname(s): s for s in secs}
    text = data[named[".text"]["offset"]:named[".text"]["offset"] + named[".text"]["size"]]

    # symtab + strtab
    symtab = named[".symtab"]
    strtab = secs[symtab["link"]]
    strtab_bytes = data[strtab["offset"]:strtab["offset"] + strtab["size"]]
    syms = []  # index -> (name, value, size)
    nsym = symtab["size"] // 24
    for i in range(nsym):
        b = symtab["offset"] + i * 24
        st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from("<IBBHQQ", data, b)
        end = strtab_bytes.index(b"\0", st_name)
        nm = strtab_bytes[st_name:end].decode()
        syms.append((nm, st_value, st_size))
    symtab_by_name = {}
    for nm, val, sz in syms:
        if nm and nm not in symtab_by_name:
            symtab_by_name[nm] = (val, sz)

    relocs = []
    if ".rela.text" in named:
        rs = named[".rela.text"]
        nrel = rs["size"] // 24
        for i in range(nrel):
            b = rs["offset"] + i * 24
            r_offset, r_info, r_addend = struct.unpack_from("<QQq", data, b)
            r_type = r_info & 0xFFFFFFFF
            r_sym = r_info >> 32
            assert r_type == R_AARCH64_CALL26, f"unexpected reloc type {r_type}"
            sym_nm, sym_val, sym_sz = syms[r_sym]
            relocs.append((r_offset, sym_val, r_addend))
    return text, symtab_by_name, relocs


def resolve_and_link(text, relocs):
    """Patch each CALL26 in-place: bl imm26 = (target - site)/4, encoded into the
    low 26 bits. .text already holds all functions concatenated at their final
    offsets, so no relayout is needed — just fill in the branch displacements."""
    blob = bytearray(text)
    for (site, target, addend) in relocs:
        disp = (target + addend - site) // 4
        # 26-bit signed
        imm26 = disp & 0x03FFFFFF
        word = struct.unpack_from("<I", blob, site)[0]
        word = (word & 0xFC000000) | imm26  # keep opcode bits (bl = 0x94)
        struct.pack_into("<I", blob, site, word)
    return bytes(blob)


def main():
    if os.uname().machine not in ("arm64", "aarch64"):
        print("SKIP: needs a native arm64 host")
        return 0
    W = tempfile.mkdtemp()
    runner_c = os.path.join(W, "run.c")
    with open(runner_c, "w") as f:
        f.write(RUNNER_C)
    runner = os.path.join(W, "run")
    r = sh(["clang", "-O0", "-o", runner, runner_c])
    if r.returncode != 0:
        print("SKIP: cannot build JIT runner\n" + r.stderr)
        return 0

    # Each case: (name, wat, expected_syms, [(arg-tuple)]). The entry export MUST
    # be the FIRST local function so it sits at .text offset 0 (the runner enters
    # there). `expected_syms` are function symbols that MUST appear in the emitted
    # object — if any is missing (a caller silently skipped by a decline), the
    # harness FAILS LOUDLY rather than running an unrelocated `bl #0`
    # (branch-to-self infinite loop).
    #
    # SCOPE (honest): a CALLER that reads its OWN incoming params while calling
    # loud-declines (param homing across a call is a later increment). So every
    # exported ENTRY here marshals CONST or COMPUTED args; the CALLEE freely reads
    # its params (a leaf). This exercises the real call path end-to-end.
    cases = [
        (
            "call_const_args",
            """(module
  (func (export "run") (result i32)
    (call $mul (i32.const 6) (i32.const 7)))
  (func $mul (param i32 i32) (result i32)
    (i32.mul (local.get 0) (local.get 1))))""",
            ["run", "func_1"],
            [()],
        ),
        (
            "call_computed_args",
            """(module
  (func (export "run") (result i32)
    (call $add (i32.add (i32.const 100) (i32.const 23)) (i32.const 22)))
  (func $add (param i32 i32) (result i32)
    (i32.add (local.get 0) (local.get 1))))""",
            ["run", "func_1"],
            [()],
        ),
        (
            "void_call_then_value",
            """(module
  (func (export "run") (result i32)
    (call $noop)
    (i32.const 99))
  (func $noop))""",
            ["run", "func_1"],
            [()],
        ),
        (
            "i64_call_const_args",
            """(module
  (func (export "run") (result i64)
    (call $add64 (i64.const 1000000000000) (i64.const 2000000000000)))
  (func $add64 (param i64 i64) (result i64)
    (i64.add (local.get 0) (local.get 1))))""",
            ["run", "func_1"],
            [()],
        ),
        (
            "call_returns_helper_result",
            """(module
  (func (export "run") (result i32)
    (i32.add (call $seven) (i32.const 1)))
  (func $seven (result i32)
    (i32.const 7)))""",
            ["run", "func_1"],
            [()],
        ),
    ]

    fails = []
    ran = 0
    for name, wat, expected_syms, argsets in cases:
        wat_p = os.path.join(W, f"{name}.wat")
        wasm_p = os.path.join(W, f"{name}.wasm")
        obj_p = os.path.join(W, f"{name}.o")
        with open(wat_p, "w") as f:
            f.write(wat)
        if sh([WASMTOOLS, "validate", wat_p]).returncode != 0:
            fails.append(f"{name}: wat invalid")
            continue
        sh([WASMTOOLS, "parse", wat_p, "-o", wasm_p])
        c = sh([SYNTH, "compile", wat_p, "-b", "aarch64", "--relocatable", "-o", obj_p])
        if c.returncode != 0:
            fails.append(f"{name}: synth DECLINED/failed: {c.stderr.strip()[:200]}")
            continue
        try:
            text, syms, relocs = parse_elf(obj_p)
            blob = resolve_and_link(text, relocs)
        except Exception as e:
            fails.append(f"{name}: ELF/link error: {e}")
            continue
        # sanity: `run` symbol must be at offset 0 (entry-first requirement).
        run_val = syms.get("run", (None, None))[0]
        if run_val != 0:
            fails.append(f"{name}: export 'run' not at .text offset 0 (got {run_val})")
            continue
        # LOUD skip-masking guard: every function we expect MUST be in the object.
        # A silently-skipped caller (declined) would leave a dangling `bl #0`
        # (branch-to-self infinite loop) — fail here instead of hanging.
        missing = [s for s in expected_syms if s not in syms]
        if missing:
            fails.append(f"{name}: expected symbols missing from object (a caller "
                         f"was silently declined/skipped): {missing}")
            continue
        hexblob = blob.hex()
        for args in argsets:
            native = sh([runner, hexblob, *[str(a) for a in args]])
            wt = sh([WASMTIME, "run", "--invoke", "run", wasm_p, *[str(a) for a in args]])
            g = native.stdout.strip()
            o = wt.stdout.strip()
            ran += 1
            if g != o:
                fails.append(f"{name}{args}: native={g!r} wasmtime={o!r} "
                             f"(native_err={native.stderr.strip()[:80]} "
                             f"wt_err={wt.stderr.strip()[:80]})")

    if fails:
        print(f"FAIL ({ran} runs, {len(fails)} problems):")
        for f in fails:
            print("  " + f)
        return 1
    print(f"PASS: {ran} call runs bit-identical to wasmtime "
          f"across {len(cases)} modules")
    return 0


if __name__ == "__main__":
    sys.exit(main())
