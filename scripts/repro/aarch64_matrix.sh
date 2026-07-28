#!/usr/bin/env bash
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

echo "aarch64: $acc ops accepted, $n native checks. Declined frontier:$dec"
if [ -z "$bad" ]; then echo "PASS: all accepted aarch64 ops match wasmtime"; exit 0
else echo "FAIL: aarch64 MISCOMPILE:$bad"; exit 1; fi
