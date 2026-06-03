#include <stdint.h>
#include "control.h"
uint32_t rv_ff_call(struct flight_state*, const struct imu_sample*);   /* synth flat_flight via s11=0 tramp */
__attribute__((noinline)) uint32_t ff_native(struct flight_state*st,const struct imu_sample*s){
  int32_t ap=s->accel_x,ar=s->accel_y,gp=st->pitch_mdeg+s->gyro_y,gr=st->roll_mdeg+s->gyro_x,gy=st->yaw_mdeg+s->gyro_z;
  st->pitch_mdeg=(gp*980+ap*20)/1000;st->roll_mdeg=(gr*980+ar*20)/1000;st->yaw_mdeg=gy;
  st->pitch_rate=s->gyro_y;st->roll_rate=s->gyro_x;st->yaw_rate=s->gyro_z;
  int32_t a=-(st->roll_mdeg>>6)-(st->roll_rate>>7),e=-(st->pitch_mdeg>>6)-(st->pitch_rate>>7),r=-(st->yaw_mdeg>>6)-(st->yaw_rate>>7);
  if(a>127)a=127;if(a<-127)a=-127;if(e>127)e=127;if(e<-127)e=-127;if(r>127)r=127;if(r<-127)r=-127;
  return ((uint32_t)(uint8_t)(int8_t)a)|((uint32_t)(uint8_t)(int8_t)e<<8)|((uint32_t)(uint8_t)(int8_t)r<<16)|((st->updates&0xFF)<<24);}
#define UART (*(volatile uint8_t*)0x10000000u)
static void pc_(char c){UART=(uint8_t)c;}static void ps_(const char*s){while(*s)pc_(*s++);}
static void pd_(int32_t v){char b[12];int i=0;uint32_t u=v;if(!u)b[i++]='0';while(u){b[i++]='0'+u%10;u/=10;}while(i)pc_(b[--i]);}
static inline uint32_t rc(void){uint32_t c;__asm__ volatile("csrr %0, mcycle":"=r"(c));return c;}
static const struct imu_sample S0={.gyro_x=100,.gyro_y=-50,.gyro_z=30,.accel_x=300,.accel_y=-200};
int main(void){
  uint32_t ovh=~0u;for(int i=0;i<200;i++){uint32_t a=rc(),b=rc();uint32_t d=b-a;if(d<ovh)ovh=d;}
  volatile uint32_t sink=0;uint32_t bs=~0u,bn=~0u;struct imu_sample s=S0;
  for(int i=0;i<200;i++){struct flight_state st={0};st.pitch_mdeg=1000;st.roll_mdeg=-500;st.yaw_mdeg=200;st.updates=7;uint32_t t0=rc();sink+=rv_ff_call(&st,&s);uint32_t t1=rc();uint32_t d=t1-t0;if(d<bs)bs=d;}
  for(int i=0;i<200;i++){struct flight_state st={0};st.pitch_mdeg=1000;st.roll_mdeg=-500;st.yaw_mdeg=200;st.updates=7;uint32_t t0=rc();sink+=ff_native(&st,&s);uint32_t t1=rc();uint32_t d=t1-t0;if(d<bn)bn=d;}
  ps_("E,flat_flight,synth_rv32=");pd_((int32_t)(bs-ovh));ps_(" (incl ~6-cyc s11=0 tramp),native_rv32=");pd_((int32_t)(bn-ovh));ps_("\n=== END ===\n");for(;;){}
}
