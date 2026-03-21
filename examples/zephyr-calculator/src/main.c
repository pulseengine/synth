/*
 * Synth WASM Compiler - Zephyr Calculator
 *
 * Interactive calculator using Synth-compiled WASM functions.
 * Demonstrates: i32 arithmetic, bitwise ops, memory (accumulator),
 *               and if/else control flow (max/min/abs).
 *
 * All computation functions are compiled from calculator.wat to
 * native ARM Thumb-2 assembly -- zero interpreter overhead.
 */

#include <zephyr/kernel.h>
#include <zephyr/sys/printk.h>

/* -------------------------------------------------------------------
 * Declare WASM functions compiled by Synth
 * ---------------------------------------------------------------- */

/* Basic arithmetic */
extern int32_t synth_add(int32_t a, int32_t b);
extern int32_t synth_sub(int32_t a, int32_t b);
extern int32_t synth_mul(int32_t a, int32_t b);
extern int32_t synth_div_safe(int32_t a, int32_t b);

/* Accumulator (uses WASM linear memory) */
extern void    synth_acc_set(int32_t v);
extern int32_t synth_acc_get(void);
extern int32_t synth_acc_add(int32_t v);

/* Bitwise */
extern int32_t synth_bit_and(int32_t a, int32_t b);
extern int32_t synth_bit_or(int32_t a, int32_t b);
extern int32_t synth_bit_xor(int32_t a, int32_t b);
extern int32_t synth_bit_not(int32_t a);

/* Comparison */
extern int32_t synth_max(int32_t a, int32_t b);
extern int32_t synth_min(int32_t a, int32_t b);
extern int32_t synth_abs(int32_t x);

/* -------------------------------------------------------------------
 * Test helpers
 * ---------------------------------------------------------------- */

static int tests_run;
static int tests_passed;

#define CHECK(desc, expr, expected) do {                              \
    int32_t _got = (expr);                                            \
    int32_t _exp = (expected);                                        \
    tests_run++;                                                      \
    if (_got == _exp) {                                               \
        tests_passed++;                                               \
        printk("  PASS  %-36s = %d\n", desc, _got);                  \
    } else {                                                          \
        printk("  FAIL  %-36s = %d (expected %d)\n",                  \
               desc, _got, _exp);                                     \
    }                                                                 \
} while (0)

/* -------------------------------------------------------------------
 * Main: exercise every Synth-compiled function
 * ---------------------------------------------------------------- */

int main(void)
{
    printk("\n");
    printk("===========================================================\n");
    printk("  Synth WASM Compiler - Zephyr Calculator\n");
    printk("===========================================================\n");
    printk("\n");
    printk("14 WASM functions compiled to native ARM Thumb-2 assembly.\n");
    printk("Source: calculator.wat   Target: Cortex-M\n");
    printk("\n");

    tests_run = 0;
    tests_passed = 0;

    /* ---- Arithmetic ---- */
    printk("--- Arithmetic ---\n");
    CHECK("add(3, 4)",        synth_add(3, 4),          7);
    CHECK("add(-1, 1)",       synth_add(-1, 1),         0);
    CHECK("add(0, 0)",        synth_add(0, 0),          0);
    CHECK("sub(10, 3)",       synth_sub(10, 3),         7);
    CHECK("sub(3, 10)",       synth_sub(3, 10),        -7);
    CHECK("mul(6, 7)",        synth_mul(6, 7),         42);
    CHECK("mul(-3, 4)",       synth_mul(-3, 4),       -12);
    CHECK("mul(0, 999)",      synth_mul(0, 999),        0);
    CHECK("div_safe(20, 4)",  synth_div_safe(20, 4),    5);
    CHECK("div_safe(7, 2)",   synth_div_safe(7, 2),     3);
    CHECK("div_safe(1, 0)",   synth_div_safe(1, 0),     0);
    CHECK("div_safe(-9, 3)",  synth_div_safe(-9, 3),   -3);
    printk("\n");

    /* ---- Accumulator ---- */
    printk("--- Accumulator (WASM memory) ---\n");
    synth_acc_set(100);
    CHECK("acc_set(100); acc_get()", synth_acc_get(), 100);
    CHECK("acc_add(50)",             synth_acc_add(50), 150);
    CHECK("acc_get() after add",     synth_acc_get(), 150);
    CHECK("acc_add(-200)",           synth_acc_add(-200), -50);
    CHECK("acc_get() after add",     synth_acc_get(), -50);
    synth_acc_set(0);
    CHECK("acc_set(0); acc_get()",   synth_acc_get(), 0);
    printk("\n");

    /* ---- Bitwise ---- */
    printk("--- Bitwise ---\n");
    CHECK("bit_and(0xFF, 0x0F)",  synth_bit_and(0xFF, 0x0F), 0x0F);
    CHECK("bit_and(0x00, 0xFF)",  synth_bit_and(0x00, 0xFF), 0x00);
    CHECK("bit_or(0xF0, 0x0F)",   synth_bit_or(0xF0, 0x0F),  0xFF);
    CHECK("bit_or(0x00, 0x00)",   synth_bit_or(0x00, 0x00),  0x00);
    CHECK("bit_xor(0xFF, 0x0F)",  synth_bit_xor(0xFF, 0x0F), 0xF0);
    CHECK("bit_xor(0xAA, 0xAA)",  synth_bit_xor(0xAA, 0xAA), 0x00);
    CHECK("bit_not(0)",           synth_bit_not(0),           -1);
    CHECK("bit_not(-1)",          synth_bit_not(-1),           0);
    printk("\n");

    /* ---- Comparison ---- */
    printk("--- Comparison ---\n");
    CHECK("max(5, 3)",   synth_max(5, 3),    5);
    CHECK("max(3, 5)",   synth_max(3, 5),    5);
    CHECK("max(-1, -5)", synth_max(-1, -5), -1);
    CHECK("max(7, 7)",   synth_max(7, 7),    7);
    CHECK("min(5, 3)",   synth_min(5, 3),    3);
    CHECK("min(3, 5)",   synth_min(3, 5),    3);
    CHECK("min(-1, -5)", synth_min(-1, -5), -5);
    CHECK("abs(42)",     synth_abs(42),     42);
    CHECK("abs(-42)",    synth_abs(-42),    42);
    CHECK("abs(0)",      synth_abs(0),       0);
    printk("\n");

    /* ---- Summary ---- */
    printk("===========================================================\n");
    printk("  Results: %d / %d tests passed\n", tests_passed, tests_run);
    printk("===========================================================\n");

    if (tests_passed == tests_run) {
        printk("\n  All tests passed -- WASM compilation verified!\n\n");
    } else {
        printk("\n  Some tests FAILED.\n\n");
    }

    printk("Each function is native ARM -- no interpreter, no runtime,\n");
    printk("no overhead.  Compilation correctness is backed by Rocq proofs.\n");
    printk("\n");

    /* ---- Continuous demo loop ---- */
    printk("Running continuous accumulator demo...\n\n");

    synth_acc_set(0);
    int32_t step = 1;

    while (1) {
        int32_t acc = synth_acc_add(step);
        int32_t neg = synth_abs(synth_sub(0, acc));

        printk("[%6u ms] acc=%d  |0-acc|=%d  max(acc,50)=%d  min(acc,-50)=%d\n",
               k_uptime_get_32(), acc, neg,
               synth_max(acc, 50), synth_min(acc, -50));

        /* Reverse direction at boundaries */
        if (acc >= 100) {
            step = -1;
        } else if (acc <= -100) {
            step = 1;
        }

        k_msleep(500);
    }

    return 0;
}
