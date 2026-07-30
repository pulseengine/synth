#!/usr/bin/env bash
# ci-status: wired
# synth aarch64 execution-differential acceptance gate.
# Compiles a broad WASM op set with `synth -b aarch64`, executes each accepted op NATIVELY on an
# arm64 host (MAP_JIT), and diffs bit-exact vs wasmtime. Exits non-zero on any MISCOMPILE (a declined
# op is fine — the gate is "no accepted op is WRONG"). Also prints the current aarch64 frontier.
#
# Requires: an arm64 host (Apple Silicon / Linux arm64), clang, llvm-objcopy, wasm-tools, wasmtime.
# Env: SYNTH (path to synth binary; default `synth` on PATH), WASMTIME (default `wasmtime`),
#      WASMTOOLS (default `wasm-tools`), OBJCOPY (default `llvm-objcopy`).
set -uo pipefail
SYNTH="${SYNTH:-synth}"; WASMTIME="${WASMTIME:-wasmtime}"; WASMTOOLS="${WASMTOOLS:-wasm-tools}"; OBJCOPY="${OBJCOPY:-llvm-objcopy}"
[ "$(uname -m)" = "arm64" ] || [ "$(uname -m)" = "aarch64" ] || { echo "SKIP: needs a native arm64 host"; exit 0; }
W=$(mktemp -d); trap 'rm -rf "$W"' EXIT

# --- embed the native JIT runners (i32 and i64) ---
cat > "$W/run32.c" <<'C'
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#include <signal.h>
#include <sys/mman.h>
#ifdef __APPLE__
#include <pthread.h>
#endif
static void on_trap(int s){(void)s;write(1,"TRAP\n",5);_exit(0);}
int main(int c,char**v){
  if(c<4){fprintf(stderr,"usage: %s <hex> <a> <b>\n",v[0]);return 2;}
  size_t n=strlen(v[1])/2; uint8_t*code=malloc(n);
  for(size_t i=0;i<n;i++){unsigned b;sscanf(v[1]+2*i,"%2x",&b);code[i]=(uint8_t)b;}
  struct sigaction sa; memset(&sa,0,sizeof sa); sa.sa_handler=on_trap; sigemptyset(&sa.sa_mask);
  sigaction(SIGILL,&sa,0);sigaction(SIGTRAP,&sa,0);sigaction(SIGFPE,&sa,0);sigaction(SIGSEGV,&sa,0);sigaction(SIGBUS,&sa,0);
  int mf=MAP_PRIVATE|MAP_ANON;
#ifdef MAP_JIT
  mf|=MAP_JIT;
#endif
  void*m=mmap(0,4096,PROT_READ|PROT_WRITE|PROT_EXEC,mf,-1,0);
  if(m==MAP_FAILED){perror("mmap");return 2;}
#ifdef __APPLE__
  pthread_jit_write_protect_np(0); memcpy(m,code,n); pthread_jit_write_protect_np(1);
#else
  memcpy(m,code,n);
#endif
  __builtin___clear_cache((char*)m,(char*)m+n);
  int32_t a=(int32_t)strtol(v[2],0,10), b=(int32_t)strtol(v[3],0,10);
  int32_t(*fn)(int32_t,int32_t)=(void*)m; printf("%d\n",fn(a,b)); return 0;
}
C
sed 's/int32_t/int64_t/g; s/strtol/strtoll/g; s/%d\\n/%lld\\n/' "$W/run32.c" > "$W/run64.c"
clang -O0 -o "$W/r32" "$W/run32.c" 2>/dev/null || { echo "SKIP: cannot build JIT runner"; exit 0; }
clang -O0 -o "$W/r64" "$W/run64.c" 2>/dev/null

sd(){ printf '%d' "$(( $1>2147483647 ? $1-4294967296 : ($1<-2147483648 ? $1+4294967296 : $1) ))"; }
bad=""; n=0; acc=0; dec=""
hexof(){ printf '(module (func (export "f") %s %s))\n' "$1" "$2" > "$W/t.wat"
  "$WASMTOOLS" validate "$W/t.wat" >/dev/null 2>&1 || { echo ""; return; }
  "$WASMTOOLS" parse "$W/t.wat" -o "$W/t.wasm" 2>/dev/null
  "$SYNTH" compile "$W/t.wat" -b aarch64 -n f --relocatable -o "$W/t.o" >/dev/null 2>&1 || { echo ""; return; }
  local sz; sz=$(objdump -t "$W/t.o" 2>/dev/null|awk '$NF=="f"&&/F .text/{print $(NF-1);exit}')
  "$OBJCOPY" -O binary --only-section=.text "$W/t.o" "$W/t.bin" 2>/dev/null; xxd -p -l "$((16#$sz))" "$W/t.bin"|tr -d '\n'; }
op2(){ local nm="$1" b="$2"; shift 2; local h; h=$(hexof '(param i32 i32)(result i32)' "$b"); [ -z "$h" ]&&{ dec="$dec $nm";return;}; acc=$((acc+1))
  while [ $# -ge 2 ]; do local a=$1 c=$2; shift 2; local g o; g=$("$W/r32" "$h" "$(sd $a)" "$(sd $c)" 2>/dev/null); o=$("$WASMTIME" run --invoke f "$W/t.wasm" "$(sd $a)" "$(sd $c)" 2>/dev/null); n=$((n+1)); [ "$g" = "$o" ]||bad="$bad $nm($a,$c):s=$g,w=$o"; done; }
op1(){ local nm="$1" b="$2"; shift 2; local h; h=$(hexof '(param i32)(result i32)' "$b"); [ -z "$h" ]&&{ dec="$dec $nm";return;}; acc=$((acc+1))
  for a in "$@"; do local g o; g=$("$W/r32" "$h" "$(sd $a)" 0 2>/dev/null); o=$("$WASMTIME" run --invoke f "$W/t.wasm" "$(sd $a)" 2>/dev/null); n=$((n+1)); [ "$g" = "$o" ]||bad="$bad $nm($a):s=$g,w=$o"; done; }
lop2(){ local nm="$1" b="$2"; shift 2; local h; h=$(hexof '(param i64 i64)(result i64)' "$b"); [ -z "$h" ]&&{ dec="$dec i64.$nm";return;}; acc=$((acc+1))
  while [ $# -ge 2 ]; do local a=$1 c=$2; shift 2; local g o; g=$("$W/r64" "$h" "$a" "$c" 2>/dev/null); o=$("$WASMTIME" run --invoke f "$W/t.wasm" "$a" "$c" 2>/dev/null); n=$((n+1)); [ "$g" = "$o" ]||bad="$bad i64.$nm($a,$c):s=$g,w=$o"; done; }
fop2(){ local nm="$1" op="$2"; shift 2; local h; h=$(hexof '(param i32 i32)(result i32)' "(i32.reinterpret_f32 ($op (f32.reinterpret_i32 (local.get 0))(f32.reinterpret_i32 (local.get 1))))"); [ -z "$h" ]&&{ dec="$dec $nm";return;}; acc=$((acc+1))
  while [ $# -ge 2 ]; do local a=$1 c=$2; shift 2; local g o gh oh; g=$("$W/r32" "$h" "$(sd $a)" "$(sd $c)" 2>/dev/null); o=$("$WASMTIME" run --invoke f "$W/t.wasm" "$(sd $a)" "$(sd $c)" 2>/dev/null); gh=$(printf '%08x' $((g&0xffffffff)) 2>/dev/null); oh=$(printf '%08x' $((o&0xffffffff)) 2>/dev/null); n=$((n+1)); [ "$gh" = "$oh" ]||bad="$bad $nm($a,$c):s=0x$gh,w=0x$oh"; done; }

op2 add "(i32.add (local.get 0)(local.get 1))" 5 3 -1 1 2147483647 1
op2 sub "(i32.sub (local.get 0)(local.get 1))" 10 3 -2147483648 1
op2 mul "(i32.mul (local.get 0)(local.get 1))" 7 6 65535 65535 -1 -1
op2 and "(i32.and (local.get 0)(local.get 1))" -1 43690
op2 or  "(i32.or (local.get 0)(local.get 1))"  43690 21845
op2 xor "(i32.xor (local.get 0)(local.get 1))" -1 43690
op2 shl "(i32.shl (local.get 0)(local.get 1))" 1 31 1 32 1 33
op2 shr_s "(i32.shr_s (local.get 0)(local.get 1))" -8 2 -1 40
op2 shr_u "(i32.shr_u (local.get 0)(local.get 1))" -1 1 -1 32
op2 rotl "(i32.rotl (local.get 0)(local.get 1))" 1 1 -2147483648 1 305419896 8
op2 rotr "(i32.rotr (local.get 0)(local.get 1))" 1 1 1 33
op1 clz "(i32.clz (local.get 0))" 0 1 -1 65536
op1 ctz "(i32.ctz (local.get 0))" 0 8 -2147483648
op1 popcnt "(i32.popcnt (local.get 0))" 0 -1 43690
op1 eqz "(i32.eqz (local.get 0))" 0 5 -1
op2 div_s "(i32.div_s (local.get 0)(local.get 1))" 7 2
op2 rem_s "(i32.rem_s (local.get 0)(local.get 1))" 7 3
for c in eq ne lt_s lt_u gt_s gt_u le_s le_u ge_s ge_u; do op2 "$c" "(i32.$c (local.get 0)(local.get 1))" 3 5 5 3 -1 1 -2147483648 2147483647; done
lop2 add "(i64.add (local.get 0)(local.get 1))" 4000000000 5000000000 -1 1
lop2 mul "(i64.mul (local.get 0)(local.get 1))" 100000 100000 4294967296 3
lop2 shl "(i64.shl (local.get 0)(local.get 1))" 1 63 1 64
lop2 rotl "(i64.rotl (local.get 0)(local.get 1))" 256 4
fop2 f32.add "f32.add" 1069547520 1077936128
fop2 f32.min "f32.min" 0 2147483648 2143289344 1065353216
fop2 f32.max "f32.max" 0 2147483648 2143289344 1065353216
fop2 f32.copysign "f32.copysign" 1065353216 2147483648
# --- #851 v0.53 op-surface closes (select / extends / wrap / drop / nop) ---
# select with a COMPUTED condition exercises both arms across the case list.
op2 select "(select (local.get 0)(local.get 1)(i32.gt_s (local.get 0)(local.get 1)))" 3 5 5 3 -7 -9 -2147483648 2147483647
op1 select_c "(select (i32.const 7)(i32.const 9)(local.get 0))" 0 1 -1
op1 extend8_s "(i32.extend8_s (local.get 0))" 128 127 255 -1
op1 extend16_s "(i32.extend16_s (local.get 0))" 32768 32767 65535 0
op1 nop_drop "(nop)(drop (i32.const 9))(i32.add (local.get 0)(i32.const 1))" 41 -1
lop2 select "(select (local.get 0)(local.get 1)(i64.gt_s (local.get 0)(local.get 1)))" 4000000000 5000000000 -1 1
lop2 extend32_s "(i64.extend32_s (local.get 0))" 4294967295 0 2147483647 0
lop2 extend8_s "(i64.extend8_s (local.get 0))" 128 0 255 0
lop2 extend16_s "(i64.extend16_s (local.get 0))" 40000 0 32767 0
# f32 select through the reinterpret wrapper: NaN vs 1.0 both directions.
op2 f32.select "(i32.reinterpret_f32 (select (f32.reinterpret_i32 (local.get 0))(f32.reinterpret_i32 (local.get 1))(i32.lt_u (local.get 0)(local.get 1))))" 2143289344 1065353216 1065353216 2143289344 0 2147483648

# --- v0.54 L2 (#851): the float-completion surface ---
# f32/f64 rounding, i64->float converts and the TRAPPING i64-target
# truncations. Args and results travel as BIT PATTERNS through reinterprets, so
# the comparison is bit-exact (±0 sign and NaN passthrough included).
# f32/f64 LOAD/STORE are deliberately NOT here: they need `x28` = linear-memory
# base on entry, which this bare JIT runner cannot establish — they are
# execution-verified under unicorn in
# scripts/repro/aarch64_float_completion_851_differential.py.

# unary f32 op, i32 bit pattern in and out.
fop1(){ local nm="$1" op="$2"; shift 2; local h; h=$(hexof '(param i32)(result i32)' "(i32.reinterpret_f32 ($op (f32.reinterpret_i32 (local.get 0))))"); [ -z "$h" ]&&{ dec="$dec $nm";return;}; acc=$((acc+1))
  for a in "$@"; do local g o gh oh; g=$("$W/r32" "$h" "$(sd $a)" 0 2>/dev/null); o=$("$WASMTIME" run --invoke f "$W/t.wasm" "$(sd $a)" 2>/dev/null); gh=$(printf '%08x' $((g&0xffffffff)) 2>/dev/null); oh=$(printf '%08x' $((o&0xffffffff)) 2>/dev/null); n=$((n+1)); [ "$gh" = "$oh" ]||bad="$bad $nm(0x$(printf '%08x' $((a&0xffffffff)))):s=0x$gh,w=0x$oh"; done; }
# unary f64 op, i64 bit pattern in and out.
dop1(){ local nm="$1" op="$2"; shift 2; local h; h=$(hexof '(param i64 i64)(result i64)' "(i64.reinterpret_f64 ($op (f64.reinterpret_i64 (local.get 0))))"); [ -z "$h" ]&&{ dec="$dec $nm";return;}; acc=$((acc+1))
  for a in "$@"; do local g o; g=$("$W/r64" "$h" "$a" 0 2>/dev/null); o=$("$WASMTIME" run --invoke f "$W/t.wasm" "$a" 0 2>/dev/null); n=$((n+1)); [ "$g" = "$o" ]||bad="$bad $nm($a):s=$g,w=$o"; done; }
# i64-in / i64-bit-pattern-out (the i64->float converts, compared bit-exactly).
cvt64(){ local nm="$1" b="$2"; shift 2; local h; h=$(hexof '(param i64 i64)(result i64)' "$b"); [ -z "$h" ]&&{ dec="$dec $nm";return;}; acc=$((acc+1))
  for a in "$@"; do local g o; g=$("$W/r64" "$h" "$a" 0 2>/dev/null); o=$("$WASMTIME" run --invoke f "$W/t.wasm" "$a" 0 2>/dev/null); n=$((n+1)); [ "$g" = "$o" ]||bad="$bad $nm($a):s=$g,w=$o"; done; }
# TRAPPING op: the JIT runner's signal handler prints TRAP; wasmtime exits
# non-zero with no stdout. Normalize both so a "traps where wasmtime traps"
# disagreement is a MISCOMPILE, not an unnoticed empty string.
trap64(){ local nm="$1" b="$2"; shift 2; local h; h=$(hexof '(param i64 i64)(result i64)' "$b"); [ -z "$h" ]&&{ dec="$dec $nm";return;}; acc=$((acc+1))
  for a in "$@"; do local g o; g=$("$W/r64" "$h" "$a" 0 2>/dev/null); o=$("$WASMTIME" run --invoke f "$W/t.wasm" "$a" 0 2>/dev/null); [ -z "$o" ]&&o=TRAP; [ -z "$g" ]&&g=TRAP; n=$((n+1)); [ "$g" = "$o" ]||bad="$bad $nm($a):s=$g,w=$o"; done; }

# Rounding. The halfway values are load-bearing: WASM `nearest` is
# ties-to-EVEN, so 0.5->0, 1.5->2, 2.5->2, 3.5->4 — a ties-away lowering
# (A64 FRINTA instead of FRINTN) fails exactly here. ±inf/NaN/1e30 catch the
# other classic wrong lowering, a round-trip through a 32-bit integer.
F32R="1056964608 1069547520 1075838976 1080033280 3204448256 3217031168 3223322624 3227516928 1072902963 3220386611 0 2147483648 2139095040 4286578688 2143289344 1900671690 4048155338 1258291199"
for r in ceil floor trunc nearest; do fop1 "f32.$r" "f32.$r" $F32R; done
F64R="4602678819172646912 4609434218613702656 4612811918334230528 4615063718147915776 -4620693217682128896 -4613937818241073152 4611235658464650854 -4612136378390124954 9218868437227405312 -4503599627370496 9221120237041090560 9094988921128908188 4841369599423283199"
for r in ceil floor trunc nearest; do dop1 "f64.$r" "f64.$r" $F64R; done

# i64 -> float converts. Above 2^24 (f32) / 2^53 (f64) the convert must ROUND
# to nearest-EVEN; the ±1/±3 offsets past each onset pin that.
CVTV="0 1 -1 16777216 16777217 16777219 -16777217 -16777219 9007199254740992 9007199254740993 9007199254740995 4611686018427387904 9223372036854775807 -9223372036854775808"
cvt64 f64.convert_i64_s "(i64.reinterpret_f64 (f64.convert_i64_s (local.get 0)))" $CVTV
cvt64 f64.convert_i64_u "(i64.reinterpret_f64 (f64.convert_i64_u (local.get 0)))" $CVTV
cvt64 f32.convert_i64_s "(i64.extend_i32_u (i32.reinterpret_f32 (f32.convert_i64_s (local.get 0))))" $CVTV
cvt64 f32.convert_i64_u "(i64.extend_i32_u (i32.reinterpret_f32 (f32.convert_i64_u (local.get 0))))" $CVTV

# TRAPPING i64-target truncations — the soundness-critical class. A64
# FCVTZ{S,U} SATURATE where WASM traps, so every out-of-range/NaN input below
# MUST trap; the in-range ones must match bit-exactly. Inputs are f64/f32 bit
# patterns: ±2^63 and ±2^64 exactly, the nearest representable value strictly
# inside each bound, -1.0/-0.5 (the strict unsigned lower bound), ±inf, NaN.
# (The full both-sides-of-every-boundary table lives in the differential; this
# is gale's on-silicon confirmation that traps really fire.)
T64D="4890909195324358656 4890909195324358655 -4332462841530417152 -4332462841530417151 4895412794951729152 4895412794951729151 -4616189618054758400 -4620693217682128896 9218868437227405312 -4503599627370496 9221120237041090560 0 -9223372036854775808 4886405595696988160"
trap64 i64.trunc_f64_s "(i64.trunc_f64_s (f64.reinterpret_i64 (local.get 0)))" $T64D
trap64 i64.trunc_f64_u "(i64.trunc_f64_u (f64.reinterpret_i64 (local.get 0)))" $T64D
T64S="1593835520 1593835519 3741319168 3741319169 1602224128 1602224127 3212836864 3204448256 2139095040 4286578688 2143289344 0 2147483648 1266679808"
trap64 i64.trunc_f32_s "(i64.trunc_f32_s (f32.reinterpret_i32 (i32.wrap_i64 (local.get 0))))" $T64S
trap64 i64.trunc_f32_u "(i64.trunc_f32_u (f32.reinterpret_i32 (i32.wrap_i64 (local.get 0))))" $T64S

echo "aarch64: $acc ops accepted, $n native checks. Declined frontier:$dec"
if [ -z "$bad" ]; then echo "PASS: all accepted aarch64 ops match wasmtime"; exit 0
else echo "FAIL: aarch64 MISCOMPILE:$bad"; exit 1; fi
