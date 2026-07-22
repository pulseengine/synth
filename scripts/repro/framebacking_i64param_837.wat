;; #837 — a FRAME-BACKING function (body contains a call) with a 64-bit VALUE
;; param. gale's `gust:os/timer` provider shape. The u64 param arrives in an
;; AAPCS even-aligned register pair (here R2:R3, after the leading i32 in R0)
;; and MUST survive the call's caller-saved clobber, so the pair is homed into
;; the frame in the prologue and reloaded after the call. Previously this class
;; loud-declined (#518): the frame-backing param_slots path sized an i64 param's
;; slot from a width set (`i64_set`) that excludes params, dropping the high
;; half. #837 sizes it from the declared AAPCS width instead. Executes bit-
;; identically to the reference model via framebacking_i64param_837_differential.py.
(module
  ;; deterministic mmio read stub (the harness installs read32(x) = x ^ 0xA5A5A5A5)
  (import "env" "read32" (func $read32 (param i32) (result i32)))

  ;; in-module fn the body also calls (result dropped) — proves two BLs, both of
  ;; which clobber R0..R3, so the u64 pair must be frame-resident across BOTH.
  (func $combine (param i32) (result i32)
    local.get 0
    i32.const 7
    i32.add)

  ;; sleep(handle: u32, ticks: u64) -> u32
  ;; = low32(ticks) + read32(handle). Uses only the LOW half after the calls, but
  ;; the WHOLE pair is homed/reloaded — a dropped hi is caught by sleep_hi below.
  (func (export "sleep") (param $handle i32) (param $ticks i64) (result i32)
    (local $mmio i32)
    local.get $handle
    call $read32
    local.set $mmio
    local.get $mmio
    call $combine
    drop
    local.get $ticks
    i32.wrap_i64
    local.get $mmio
    i32.add)

  ;; sleep_hi(handle: u32, ticks: u64) -> u32
  ;; = (low32(ticks) XOR high32(ticks)) + read32(handle). Result depends on BOTH
  ;; halves of the u64 param, so the full R2:R3 pair must survive the call.
  (func (export "sleep_hi") (param $handle i32) (param $ticks i64) (result i32)
    (local $mmio i32)
    local.get $handle
    call $read32
    local.set $mmio
    local.get $mmio
    call $combine
    drop
    (i32.wrap_i64 (local.get $ticks))
    (i32.wrap_i64 (i64.shr_u (local.get $ticks) (i64.const 32)))
    i32.xor
    local.get $mmio
    i32.add)

  ;; sibling with NO 64-bit param — the control that always compiled.
  (func (export "slept") (param $handle i32) (result i32)
    local.get $handle
    call $read32)

  (export "combine" (func $combine)))
