/* #735 parity benchmark — native C twin of the gust_mix clamp shape
 * (scripts/repro/fact_spec_clamp_494.wat): clamp(ch + 476, 1000, 2000).
 *
 * Build (see run.py / artifacts/parity-benchmark.md for the pinned flags):
 *   arm-none-eabi-gcc -Os -mcpu=cortex-m4 -mthumb -c gust_mix_clamp.c
 *
 * This is the #494 proof-carrying-specialization benchmark shape: under the
 * loom-proven premise ch ∈ [524, 1524] both clamp branches are dead, and
 * synth (SYNTH_FACT_SPEC=1) elides them with a per-site ordeal-certified
 * UNSAT obligation. C has no channel to express that premise — the native
 * compiler must keep both compares no matter how smart it is, because it
 * cannot prove the range. That asymmetry is the point of the benchmark row.
 */
#include <stdint.h>

int32_t gust_mix(int32_t ch)
{
	int32_t v = ch + 476;
	if (v < 1000)
		v = 1000;
	if (v > 2000)
		v = 2000;
	return v;
}
