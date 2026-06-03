# `flat_flight` — shared Opt-3 measurement fixture & regression oracle

This is the **single loom-dissolved `flat_flight`** referenced in pulseengine/synth#209 —
the composed `filter_step + controller_step` as one function. It's the artifact behind the
disassembly numbers in that thread (RV32: **756 bytes / 186 instructions** on v0.11.27),
so const-CSE (Opt-3 #1) and pressure-aware spilling (#2) should be measured against *this*,
not the 3-export `flight_seam_flat.wasm`.

## Files
- `flat_flight.loom.wasm` — the fixture (546 B wasm). `clang -O2 → wasm-ld → loom optimize --passes inline`.
- `flat_flight.c` — source. NB: this is the **manually pre-inlined** composition (one function, no
  internal calls) — i.e. a stand-in for "what full loom dissolution of the seam produces". It is
  behaviorally identical to `benches/flight_control/src/control.c` (`filter_step`+`controller_step`)
  in the gale repo (verified: same outputs on every vector below). Use it as the frozen oracle.
- `control.h` — the `flight_state` / `imu_sample` struct layouts (needed to build/drive it).
- `harness/` — a reference qemu_riscv32 measurement rig (startup + linker + `main_ffm.c` icount loop +
  `rv_ff_tramp.S`, the `s11=0` native-pointer-deref trampoline). `synth riscv-runtime` provides the rest.

## Signature & ABI
`uint32_t flat_flight(struct flight_state *st, const struct imu_sample *s)` — reads `*s` + `*st`,
**mutates `*st`** (the filter step), returns the packed controller command. Pointer args ⇒ the caller
sets the linear-memory base (`s11` on RV32, `r11/fp` on ARM); the trampoline uses base=0 so
`[base+ptr] == [ptr]` is a native deref. (synth passes the 2 ptr args in `a0/a1` — no stack args here.)

## Vectors (ground truth from native `control.c`, behavior-frozen)
`st` fields are `pitch_mdeg,roll_mdeg,yaw_mdeg,pitch_rate,roll_rate,yaw_rate,updates`;
`imu` fields are `gyro_x,gyro_y,gyro_z,accel_x,accel_y,accel_z`.

| name | st in | imu in | → cmd | → st_after (p,r,y) |
|------|-------|--------|-------|--------------------|
| nominal | 1000,-500,200,0,0,0,7 | 100,-50,30,300,-200,0 | `0x07FDF307` | 937,-396,230 |
| zero | 0,0,0,0,0,0,0 | 0,0,0,0,0,0 | `0x00000000` | 0,0,0 |
| saturate | 99999,-99999,99999,99999,-99999,99999,255 | 1000,-1000,1000,2000,-2000,0 | `0xFF81817F` | 97059,-97059,100999 |
| neg | -3000,1500,-700,0,0,0,42 | -200,80,-40,-500,400,0 | `0x2A0D2DEE` | -2871,1282,-740 |

The `saturate` / `neg` vectors exercise the ±127 clamps and the signed-div sign paths — the spots a
bad const-CSE dedup (reusing a register clobbered across the reuse span) would break first.

## Build + measure (RV32)
```sh
./harness/run.sh        # regenerates the .o from the wasm, links the icount harness, runs on qemu
# expect: SYNTH-RV32 flat_flight cmd=0x07fdf307 ... and E,flat_flight,synth_rv32=<icount>,native_rv32=75
```
Baseline to beat: v0.11.27 = **181 icount** (2.41× vs native 75), 0 callee-saved spills, but ~57% of its
37 constant materializations are redundant (per-axis ±127/coeffs/guards). That's the const-CSE target.
