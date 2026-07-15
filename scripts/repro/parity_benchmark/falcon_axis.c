/* #735 parity benchmark — native C twin of falcon_axis.wat (one f32
 * complementary-filter axis update, dt = 5 ms). Same expression, same
 * constants, float (f32) throughout.
 *
 * Build (see run.py / artifacts/parity-benchmark.md for the pinned flags):
 *   arm-none-eabi-gcc -Os -mcpu=cortex-m4 -mthumb -mfloat-abi=hard \
 *       -mfpu=fpv4-sp-d16 -c falcon_axis.c
 *
 * NB: GCC contracts a*b+c to vfma/vmla here (a transformation WebAssembly
 * semantics forbid — wasm has no fma, so synth must preserve the two
 * rounding steps to stay bit-exact vs wasmtime). run.py measures both
 * default and -ffp-contract=off variants; the size is the same on this
 * kernel, but the comparison is not IEEE-like-for-like either way.
 */
float falcon_axis(float angle, float gyro, float accel)
{
	return 0.98f * (angle + gyro * 0.005f) + 0.02f * accel;
}
