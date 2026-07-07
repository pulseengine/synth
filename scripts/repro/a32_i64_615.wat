;; #615: on the A32 path (--target cortex-r5) every i64 op encoded as a
;; literal NOP (0xE1A00000) — the operation silently vanished and the
;; function returned garbage (typically the first operand / stale registers).
;;
;; Every exported function takes its i64 operands as i32 half-pairs (lo, hi)
;; and combines them inline ((i64.extend_i32_u hi) << 32 | lo). This keeps
;; the module free of i64 params (the #518 ABI surface) and of internal
;; calls (a raw-.text unicorn harness applies no BL relocations).
;;
;; Oracle: scripts/repro/a32_i64_615_differential.py (unicorn UC_MODE_ARM vs
;; the wasmtime CLI, symbols from the ELF symtab per #489).
(module
  ;; --- i64 binops: (a_lo a_hi b_lo b_hi) -> i64 ---
  (func (export "add64") (param i32 i32 i32 i32) (result i64)
    (i64.add
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "sub64") (param i32 i32 i32 i32) (result i64)
    (i64.sub
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "mul64") (param i32 i32 i32 i32) (result i64)
    (i64.mul
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "and64") (param i32 i32 i32 i32) (result i64)
    (i64.and
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "or64") (param i32 i32 i32 i32) (result i64)
    (i64.or
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "xor64") (param i32 i32 i32 i32) (result i64)
    (i64.xor
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "div_u64") (param i32 i32 i32 i32) (result i64)
    (i64.div_u
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "div_s64") (param i32 i32 i32 i32) (result i64)
    (i64.div_s
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "rem_u64") (param i32 i32 i32 i32) (result i64)
    (i64.rem_u
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "rem_s64") (param i32 i32 i32 i32) (result i64)
    (i64.rem_s
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))

  ;; --- i64 shifts/rotates: (a_lo a_hi amount) -> i64 ---
  (func (export "shl64") (param i32 i32 i32) (result i64)
    (i64.shl
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.extend_i32_u (local.get 2))))
  (func (export "shr_u64") (param i32 i32 i32) (result i64)
    (i64.shr_u
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.extend_i32_u (local.get 2))))
  (func (export "shr_s64") (param i32 i32 i32) (result i64)
    (i64.shr_s
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.extend_i32_u (local.get 2))))
  (func (export "rotl64") (param i32 i32 i32) (result i64)
    (i64.rotl
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.extend_i32_u (local.get 2))))
  (func (export "rotr64") (param i32 i32 i32) (result i64)
    (i64.rotr
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.extend_i32_u (local.get 2))))

  ;; --- i64 comparisons: (a_lo a_hi b_lo b_hi) -> i32 ---
  (func (export "eq64") (param i32 i32 i32 i32) (result i32)
    (i64.eq
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "ne64") (param i32 i32 i32 i32) (result i32)
    (i64.ne
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "lt_s64") (param i32 i32 i32 i32) (result i32)
    (i64.lt_s
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "lt_u64") (param i32 i32 i32 i32) (result i32)
    (i64.lt_u
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "gt_s64") (param i32 i32 i32 i32) (result i32)
    (i64.gt_s
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "gt_u64") (param i32 i32 i32 i32) (result i32)
    (i64.gt_u
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "le_s64") (param i32 i32 i32 i32) (result i32)
    (i64.le_s
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "le_u64") (param i32 i32 i32 i32) (result i32)
    (i64.le_u
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "ge_s64") (param i32 i32 i32 i32) (result i32)
    (i64.ge_s
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))
  (func (export "ge_u64") (param i32 i32 i32 i32) (result i32)
    (i64.ge_u
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))
      (i64.or (i64.extend_i32_u (local.get 2))
              (i64.shl (i64.extend_i32_u (local.get 3)) (i64.const 32)))))

  ;; --- i64 unary: (a_lo a_hi) -> i64 / i32 ---
  (func (export "clz64") (param i32 i32) (result i64)
    (i64.clz
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))))
  (func (export "ctz64") (param i32 i32) (result i64)
    (i64.ctz
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))))
  (func (export "popcnt64") (param i32 i32) (result i64)
    (i64.popcnt
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))))
  (func (export "eqz64") (param i32 i32) (result i32)
    (i64.eqz
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))))
  (func (export "extend8_s64") (param i32 i32) (result i64)
    (i64.extend8_s
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))))
  (func (export "extend16_s64") (param i32 i32) (result i64)
    (i64.extend16_s
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))))
  (func (export "extend32_s64") (param i32 i32) (result i64)
    (i64.extend32_s
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))))
  (func (export "wrap64") (param i32 i32) (result i32)
    (i32.wrap_i64
      (i64.or (i64.extend_i32_u (local.get 0))
              (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32)))))

  ;; --- i64 extends from i32, i64 const ---
  (func (export "extend_s") (param i32) (result i64)
    (i64.extend_i32_s (local.get 0)))
  (func (export "extend_u") (param i32) (result i64)
    (i64.extend_i32_u (local.get 0)))
  (func (export "const64") (result i64)
    (i64.const 0x123456789ABCDEF0))

  ;; --- i32 ops in the same silent-NOP class (Popcnt / SetCond / SelectMove) ---
  (func (export "popcnt32") (param i32) (result i32)
    (i32.popcnt (local.get 0)))
  (func (export "lt_s32") (param i32 i32) (result i32)
    (i32.lt_s (local.get 0) (local.get 1)))
  (func (export "sel32") (param i32 i32 i32) (result i32)
    (select (local.get 0) (local.get 1) (local.get 2))))
