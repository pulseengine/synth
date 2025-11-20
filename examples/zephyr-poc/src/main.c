/*
 * Synth WASM POC for Zephyr
 *
 * Demonstrates calling WASM-compiled function from Zephyr
 */

#include <zephyr/kernel.h>
#include <zephyr/sys/printk.h>

/* Declare WASM function compiled by Synth */
extern int32_t synth_add(int32_t a, int32_t b);

int main(void)
{
	int32_t counter = 0;
	int32_t result;

	printk("\n");
	printk("===========================================\n");
	printk("  Synth WASM Compiler - Zephyr POC\n");
	printk("===========================================\n");
	printk("\n");
	printk("Calling WASM function every 100ms...\n");
	printk("\n");

	while (1) {
		/* Call the WASM-compiled function */
		result = synth_add(counter, 42);

		printk("[%6d ms] synth_add(%d, 42) = %d\n",
		       k_uptime_get_32(), counter, result);

		counter++;

		/* Sleep 100ms */
		k_msleep(100);
	}

	return 0;
}
