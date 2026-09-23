#!/usr/bin/env python3
"""Assert an ELF has no dynamic loader and no glibc version symbols.

RQ-71-MUSL (#1349), corrected after the v0.71 cold review. The first version of
this gate asserted `file "$BIN" | grep -q 'statically linked'`. That string is
NOT what rustc's musl target produces: the target spec sets
`crt-static-default=true` AND `static-position-independent-executables=true`, so
the link is `-static-pie`, and `file` reports "static-pie linked" (or, without
DF_1_PIE, "dynamically linked") — never "statically linked". The gate would have
REFUSED A CORRECT ARTIFACT, and `create-release` has `needs: [build-binaries]`,
so that means no GitHub Release at all rather than one missing archive.

The fix is not a better string. `file`'s wording is a presentation detail of a
tool we do not control; the PROPERTY we care about is "this binary asks no
loader to run it", which is exactly "no PT_INTERP program header". That is read
straight from the ELF here, with no dependency beyond the stdlib.
"""
import struct
import subprocess
import sys

PT_INTERP = 3


def program_headers(data):
    if data[:4] != b"\x7fELF":
        raise SystemExit("FAIL: not an ELF file")
    if data[4] != 2:
        raise SystemExit("FAIL: not ELF64")
    little = data[5] == 1
    end = "<" if little else ">"
    phoff, = struct.unpack_from(end + "Q", data, 32)
    phentsize, phnum = struct.unpack_from(end + "HH", data, 54)
    for i in range(phnum):
        off = phoff + i * phentsize
        ptype, = struct.unpack_from(end + "I", data, off)
        yield ptype, off, end


def main():
    path = sys.argv[1]
    data = open(path, "rb").read()
    try:
        out = subprocess.run(["file", path], capture_output=True, text=True).stdout.strip()
        print(f"  file: {out}")
    except FileNotFoundError:
        pass

    interp = [p for p, _o, _e in program_headers(data) if p == PT_INTERP]
    print(f"  PT_INTERP segments: {len(interp)} (want 0 — no dynamic loader)")

    # `strings` is not guaranteed present; scan the bytes directly.
    n = data.count(b"GLIBC_")
    print(f"  GLIBC_ occurrences: {n} (want 0)")

    bad = []
    if interp:
        bad.append("carries a PT_INTERP dynamic loader")
    if n:
        bad.append(f"references glibc versions ({n} occurrences)")
    if bad:
        raise SystemExit("FAIL: " + "; ".join(bad))
    print("  OK: no loader, no glibc version references")


if __name__ == "__main__":
    main()
