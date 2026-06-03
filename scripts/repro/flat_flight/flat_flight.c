/* Manually fully-inlined flight_algo (filter_step + controller_step, NO calls) —
 * a preview of what loom full dissolution would produce, to test whether a flat
 * memory-heavy function dodges synth#210 or still clobbers under register pressure. */
#include "control.h"
__attribute__((export_name("flat_flight")))
uint32_t flat_flight(struct flight_state *st, const struct imu_sample *s)
{
	/* --- filter_step inlined --- */
	int32_t accel_pitch = s->accel_x, accel_roll = s->accel_y;
	int32_t gyro_pitch = st->pitch_mdeg + s->gyro_y;
	int32_t gyro_roll  = st->roll_mdeg  + s->gyro_x;
	int32_t gyro_yaw   = st->yaw_mdeg   + s->gyro_z;
	st->pitch_mdeg = (gyro_pitch*980 + accel_pitch*20)/1000;
	st->roll_mdeg  = (gyro_roll *980 + accel_roll *20)/1000;
	st->yaw_mdeg   = gyro_yaw;
	st->pitch_rate = s->gyro_y; st->roll_rate = s->gyro_x; st->yaw_rate = s->gyro_z;
	/* --- controller_step inlined --- */
	int32_t ail = -(st->roll_mdeg>>6) - (st->roll_rate>>7);
	int32_t ele = -(st->pitch_mdeg>>6) - (st->pitch_rate>>7);
	int32_t rud = -(st->yaw_mdeg>>6) - (st->yaw_rate>>7);
	if(ail>127)ail=127; if(ail<-127)ail=-127;
	if(ele>127)ele=127; if(ele<-127)ele=-127;
	if(rud>127)rud=127; if(rud<-127)rud=-127;
	return ((uint32_t)(uint8_t)(int8_t)ail)|((uint32_t)(uint8_t)(int8_t)ele<<8)
	     |((uint32_t)(uint8_t)(int8_t)rud<<16)|((uint32_t)(st->updates&0xFF)<<24);
}
