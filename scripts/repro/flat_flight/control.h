/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 PulseEngine
 *
 * Flight-control macro benchmark — shared types.
 *
 * The bench composes five Zephyr primitives (ring_buf, sem, mutex,
 * msgq, condvar) on a 100 Hz fixed-rate flight-control loop. See
 * docs/research/macro-bench-design.md for the design contract.
 *
 * Pure C, no float (CONFIG_FPU stays off) — measurements must be
 * stable across builds, the algo segment must be byte-identical
 * baseline vs gale, same constraint as engine_control.
 */

#ifndef GALE_FLIGHT_CONTROL_H
#define GALE_FLIGHT_CONTROL_H

#include <stdint.h>

/*
 * Per-sensor-ISR sample published into the SPSC ring_buf and consumed
 * by the fusion thread. Mirrors crank_sample's role in engine_control:
 * carries the in-ISR cycle delta (algo) and a sequence number that
 * keys the side-channel slot for handoff_cycles. Step is the sweep
 * triple index (sensor_hz × contention × payload).
 */
struct imu_sample {
	int16_t  gyro_x;       /* milli-deg/s */
	int16_t  gyro_y;
	int16_t  gyro_z;
	int16_t  accel_x;      /* milli-g */
	int16_t  accel_y;
	int16_t  accel_z;
	uint32_t algo_cycles;  /* in-ISR filter math (t_algo - t_entry) */
	uint16_t seq;          /* wraps; indexes side-channel slot */
	uint8_t  step;         /* sweep index (0..SWEEP_STEPS-1) */
	uint8_t  _pad;
};

/*
 * Vehicle attitude / rates — protected by the contended state mutex.
 * Updated by fusion, read by controller + telemetry. Plain integers,
 * no float (CONFIG_FPU off), keeps the algo deterministic across
 * baseline and gale builds.
 */
struct flight_state {
	int32_t  pitch_mdeg;   /* milli-degrees */
	int32_t  roll_mdeg;
	int32_t  yaw_mdeg;
	int32_t  pitch_rate;   /* milli-deg/s */
	int32_t  roll_rate;
	int32_t  yaw_rate;
	uint32_t updates;      /* monotonic — fusion increments under mutex */
};

/*
 * Complementary-filter step: integrates gyro rates and biases toward
 * the accelerometer-derived attitude. Pure integer math, no divides
 * inside the ISR (the only divide is by GYRO_DT_INV_PERMILLE, taken
 * outside the hot path). Identity across builds — passes engine_control's
 * algo-delta-< 10 % integrity check.
 */
void filter_step(struct flight_state *st, const struct imu_sample *s);

/*
 * Trivial integer-only attitude controller. Computes a 32-bit packed
 * "command" (effort encoded in 3 channels: aileron / elevator / rudder).
 * Identity across builds.
 */
uint32_t controller_step(const struct flight_state *st);

#endif /* GALE_FLIGHT_CONTROL_H */
