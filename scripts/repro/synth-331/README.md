# synth#331 — spill-slot collision miscompiles dissolved `k_mutex_unlock`

Committed failing fixture for **pulseengine/synth#331**, per the maintainer's request to
lock it as a frozen repro. This is the register-pressure-dependent case the minimal shapes
did **not** reproduce — the full multi-path unlock body (tag dispatch + has-waiter/no-waiter)
generates the pressure that forces the call result onto arg0's home slot.

## Toolchain (reproduces as of)
- synth **0.11.40**
- loom **1.1.13**
- clang (wasm32) 22.1.4 + wasm-ld

## The failing input
`k_mutex_unlock.dissolved.wasm` (+ `.wat` for reading) is the loom-dissolved module synth
miscompiles. `wasm_mutex_shim_poc.c` is the source; the decision seam
(`gale_k_mutex_unlock_decide`) is linked in from gale's FFI wasm staticlib and inlined by loom,
so the dissolved module is self-contained for synth.

## Reproduce
```sh
synth compile k_mutex_unlock.dissolved.wasm \
  --target cortex-m4f --native-pointer-abi --all-exports --relocatable \
  -o out.o
llvm-objdump -d --triple=thumbv7em-unknown-none-eabi out.o
```
`k_mutex_unlock.cortex-m4f.FAILING.o` is the reference miscompiled output (the `z_impl_k_mutex_unlock`
body, 574 B). All offsets below are relative to the body start (`0x138` in the multi-function object).

## The collision (the bug)
arg0 (the `struct k_mutex *`) home spill slot is `[sp,#0x24]`, established at entry and **live to
the no-waiter `lock_count` store**. The `z_unpend_first_thread` result is parked on the **same**
slot, clobbering arg0. The no-waiter path then reloads the clobbered slot as the mutex base:

```
+0x008   140: str.w r0, [sp, #0x24]   ; arg0 (mutex ptr) HOME slot — live to +0x1ee
...
         26e: bl    z_unpend_first_thread     ; r0 = new_owner (NULL when no waiter)
+0x13a   272: str.w r0, [sp, #0x24]   ; *** parks unpend result on arg0's home slot ***
...
+0x150   28e: str.w r1, [r11, r12]    ; owner = new_owner   (uses a reg copy — CORRECT)
...
; no-waiter sub-path:
+0x1e2   31a: ldr.w r3, [sp, #0x24]   ; reloads the CLOBBERED slot = unpend result = 0
+0x1ea   322: add.w r12, r3, #0xc     ; intended mutex+12 (lock_count) — actually 0+12
+0x1ee   326: str.w r5, [r11, r12]    ; lock_count = 0  -> writes linmem[12], NOT mutex->lock_count
```

Relocation at `0x26e` is `R_ARM_THM_CALL z_unpend_first_thread`, confirming the clobbering value's
identity (NULL for the no-waiter case).

## Expected vs actual
- **Expected** (no-waiter unlock): `mutex->owner = NULL; mutex->lock_count = 0`.
- **Actual**: `owner = 0` lands (the owner store at `+0x150` uses a register copy), but `lock_count`
  is left at its prior value `1` because its store goes to `linmem[0+12]` instead of `mutex+12`.

## Silicon symptom (NUCLEO-G474RE, 170 MHz)
Deadlock, not a fault: after a no-waiter unlock the mutex is left `owner=0, lock_count=1` — an
impossible-by-construction state. The next `k_mutex_lock(&m, K_FOREVER)` sees `lock_count≠0 ∧
owner≠current` → block path → pends forever on an ownerless mutex → CPU idles. Observed hung
backtrace = idle thread with exactly `owner=0, lock_count=1`. (Also: the has-waiter path at
`+0x132 16a: ldr r7,[sp,#0x24]` then `+0x13a 172: add r7,#0xc; str` reloads the same clobbered
slot for its `lock_count=1` store — corrupt too, just unexercised by the single-thread selfcheck.)

## Kill-criterion
Fixed when, on a synth build, the no-waiter `lock_count` store derives its base from a slot/reg
holding the **mutex pointer** (not the unpend result) at `+0x1e2`, and on-silicon a no-waiter
`k_mutex_lock`/`unlock` round-trip leaves `lock_count == 0` (no deadlock). gale will re-measure
`k_mutex_unlock` cycles (native ref 124) on the fix.
