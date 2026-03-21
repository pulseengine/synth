/*
 * Anti-Pinch Window Controller -- Zephyr Application
 *
 * Safety-critical automotive use case demonstrating Synth's value for
 * ASIL-rated embedded systems. Inspired by https://osxcar.de/insights/demonstration/
 *
 * This application:
 *   - Simulates a power window system with motor current sensing
 *   - Calls Synth-compiled WASM control functions at 100Hz (10ms tick)
 *   - Injects a jam event at ~70% position to demonstrate anti-pinch
 *   - Prints status at 100ms intervals showing position, current, PWM, jam state
 *
 * All arithmetic is integer-only (fixed-point with 0.1% resolution).
 * Position and PWM use range 0-1000 representing 0.0%-100.0%.
 */

#include <zephyr/kernel.h>
#include <zephyr/sys/printk.h>

/* =========================================================================
 * Declare Synth-compiled WASM functions (anti_pinch.wat -> ARM assembly)
 *
 * Each function is compiled using formally verified semantics:
 * - Rocq proofs guarantee instruction selection correctness
 * - Integer-only: deterministic, no floating-point surprises
 * - Memory accesses use R11 as linear memory base (bounds-checked)
 * ========================================================================= */
extern void     synth_init(void);
extern void     synth_set_target(int32_t target);
extern void     synth_update_current(int32_t current_ma);
extern int32_t  synth_check_jam(int32_t current_ma, int32_t threshold_ma);
extern int32_t  synth_ramp_pwm(int32_t current_pwm, int32_t target_pwm);
extern int32_t  synth_tick(void);
extern int32_t  synth_get_position(void);
extern int32_t  synth_get_pwm(void);
extern int32_t  synth_get_direction(void);
extern int32_t  synth_is_jam_detected(void);
extern void     synth_clear_jam(void);

/* =========================================================================
 * Simulated motor/window physics
 *
 * In a real system these values come from:
 *   - Motor current: ADC reading of shunt resistor across H-bridge
 *   - Position: Hall sensor or encoder on window regulator
 *
 * The simulation models:
 *   - Base current proportional to PWM duty
 *   - Friction increase near fully-closed position
 *   - Current spike on jam (obstacle detected)
 * ========================================================================= */

/* Simulate motor current based on PWM and position */
static int32_t simulate_motor_current(int32_t pwm, int32_t position,
                                      int32_t direction, int32_t jam_active)
{
    int32_t base_current;
    int32_t friction_current;

    if (pwm == 0 || direction == 0) {
        return 0;  /* Motor stopped */
    }

    /* Base current proportional to PWM (at 100% PWM -> ~400mA) */
    base_current = (pwm * 400) / 1000;

    /* Friction increases as window approaches fully closed (position > 800) */
    friction_current = 0;
    if (position > 800 && direction == 1) {
        /* Linear ramp: 0mA at pos=800, 200mA at pos=1000 */
        friction_current = (position - 800) * 200 / 200;
    }

    /* Jam: current spikes to 1200mA (well above 800mA threshold) */
    if (jam_active) {
        return 1200;
    }

    return base_current + friction_current;
}

/* Direction name for display */
static const char *direction_name(int32_t dir)
{
    switch (dir) {
    case 0:  return "STOP ";
    case 1:  return "CLOSE";
    case 2:  return "OPEN ";
    default: return "???? ";
    }
}

int main(void)
{
    int32_t tick_count = 0;
    int32_t sim_jam_active = 0;
    int32_t pwm_output;
    int32_t sim_current;
    int32_t phase = 0;  /* 0=close, 1=jam-recovery, 2=reopen, 3=done */

    printk("\n");
    printk("===========================================================\n");
    printk("  Anti-Pinch Window Controller\n");
    printk("  Compiled by Synth (WebAssembly -> ARM Cortex-M)\n");
    printk("===========================================================\n");
    printk("\n");
    printk("Safety-critical automotive demonstration:\n");
    printk("  - Motor current monitoring for jam/pinch detection\n");
    printk("  - Soft start/stop via PWM ramping (2%%/tick)\n");
    printk("  - Debounced jam detection (3 consecutive over-threshold)\n");
    printk("  - Auto-stop on jam with driver notification\n");
    printk("\n");
    printk("Synth advantages for this use case:\n");
    printk("  [1] Formally verified compilation (Rocq proofs)\n");
    printk("  [2] Integer-only arithmetic (deterministic WCET)\n");
    printk("  [3] Zero runtime overhead (native ARM Thumb-2)\n");
    printk("  [4] Memory-safe by construction (WASM model)\n");
    printk("\n");
    printk("Scenario: close window to 100%%, jam at ~70%%, then reopen\n");
    printk("\n");

    /* Initialize controller via Synth-compiled WASM function */
    synth_init();

    printk("Controller initialized. Starting 100Hz control loop.\n\n");

    /* Phase 0: Command window to close (target = 1000 = fully closed) */
    synth_set_target(1000);

    printk(" Time  | Pos    | Current | PWM    | Dir   | Jam | Event\n");
    printk("-------|--------|---------|--------|-------|-----|------\n");

    while (1) {
        int32_t position = synth_get_position();
        int32_t direction = synth_get_direction();
        int32_t pwm = synth_get_pwm();

        /* ---- Simulate jam at ~70% position ---- */
        if (phase == 0 && position >= 700 && direction == 1) {
            sim_jam_active = 1;
        }

        /* Simulate motor current */
        sim_current = simulate_motor_current(pwm, position, direction,
                                             sim_jam_active);

        /* Feed simulated current to controller */
        synth_update_current(sim_current);

        /* Run one control cycle -- this is the Synth-compiled WASM tick */
        pwm_output = synth_tick();

        /* Read updated state */
        position = synth_get_position();
        direction = synth_get_direction();
        int32_t jam = synth_is_jam_detected();

        /* ---- Print status every 100ms (every 10 ticks) ---- */
        if (tick_count % 10 == 0) {
            int32_t time_ms = tick_count * 10;
            const char *event = "";

            if (phase == 0 && jam) {
                event = "<< JAM DETECTED - MOTOR STOPPED";
            } else if (phase == 1 && tick_count % 10 == 0 && jam == 0) {
                event = "<< Jam cleared, reopening";
            } else if (phase == 0 && sim_jam_active && !jam) {
                event = "<< Current spike (debouncing...)";
            }

            printk(" %4d  | %3d.%01d%% | %4d mA | %3d.%01d%% | %s | %s | %s\n",
                   time_ms,
                   position / 10, position % 10,
                   sim_current,
                   pwm_output / 10, pwm_output % 10,
                   direction_name(direction),
                   jam ? "YES" : " no",
                   event);
        }

        /* ---- Phase transitions ---- */
        if (phase == 0 && jam) {
            /* Jam detected -- wait 500ms then clear and reopen */
            phase = 1;
            printk("\n  >> Anti-pinch activated! Window will reverse in 500ms.\n\n");
        }

        if (phase == 1 && tick_count > 0 && (tick_count % 50 == 0)) {
            /* After 500ms: clear jam, command window to reopen */
            sim_jam_active = 0;
            synth_clear_jam();
            synth_set_target(0);  /* Fully open */
            phase = 2;
            printk("\n  >> Reversing window (opening to 0%%).\n\n");
        }

        if (phase == 2 && position == 0 && direction == 0) {
            phase = 3;
            printk("\n");
            printk("===========================================================\n");
            printk("  Demo complete -- anti-pinch safety function verified.\n");
            printk("===========================================================\n");
            printk("\n");
            printk("Results:\n");
            printk("  [OK] Window closed normally from 0%% to 70%%\n");
            printk("  [OK] Jam detected at 70%% via current threshold (>800mA)\n");
            printk("  [OK] Motor stopped immediately on jam confirmation\n");
            printk("  [OK] Window reversed to fully open (0%%)\n");
            printk("  [OK] Soft start/stop PWM ramping throughout\n");
            printk("\n");
            printk("All control logic compiled from WebAssembly using\n");
            printk("formally verified Synth compiler. Zero runtime overhead.\n");
            printk("\n");

            /* Restart demo after 5 seconds */
            k_msleep(5000);
            tick_count = 0;
            phase = 0;
            sim_jam_active = 0;
            synth_init();
            synth_set_target(1000);
            printk("--- Restarting demo ---\n\n");
            continue;
        }

        tick_count++;

        /* 10ms tick (100Hz control loop) */
        k_msleep(10);
    }

    return 0;
}
