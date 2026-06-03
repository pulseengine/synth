#!/usr/bin/env bash
# Regenerate the RV32 object from the committed loom.wasm, link the icount harness, run on qemu.
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"; FX="$HERE/.."
RV="${RV:-riscv64-unknown-elf-gcc}"; QEMU="${QEMU:-qemu-system-riscv32}"
synth riscv-runtime -t rv32imac --flash-origin 0x80000000 --ram-origin 0x80010000 \
  --linear-memory-size 4096 --stack-size 8192 -o "$HERE" >/dev/null 2>&1 || true
synth compile "$FX/flat_flight.loom.wasm" -b riscv -t rv32imac --all-exports --relocatable -o "$HERE/flat.o"
$RV -march=rv32imac_zicsr -mabi=ilp32 -O2 -nostartfiles -nostdlib -ffreestanding -I"$FX" \
  -T "$HERE/linker.ld" -o "$HERE/fw.elf" "$HERE/startup.c" "$HERE/main_ffm.c" "$HERE/rv_ff_tramp.S" "$HERE/flat.o"
"$QEMU" -machine virt -bios none -nographic -icount shift=0 -kernel "$HERE/fw.elf" &
p=$!; sleep 5; kill $p 2>/dev/null || true
