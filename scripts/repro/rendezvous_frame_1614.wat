;; RQ-89-BRF32 (#1614) — the f32 branch RENDEZVOUS slot and the frame.
;;
;; RQ-76-FALCON (#1318) lands an f32 carried over br/br_if/br_table in a FRAME
;; SLOT that every edge stores and the block join reloads. The slot is drawn
;; from the shared spill pool. That pool only EXISTS in the frame when
;; `compute_local_layout` reserved it (an i64-touching function, or a retry
;; rung); otherwise its base is just the end of the frame fields, so the slot
;; lands on whatever sits there: the prologue's saved R4 (no other frame use),
;; a #204 param-backing slot (a function with a call), or the frame padding
;; (harmless by luck). Without a call the return value is right, so a
;; value-only oracle is blind to it; the caller's R4 is not. With a call the
;; param-backing slot is overwritten and the VALUE is wrong too.
;;
;; Every export is a CLASS ROW: the edge kind, the result consumer, and what
;; else uses the frame. (A br into a result-typed `if` is declined by #509 and
;; an f32 `if`/`else` result by #313 on this path, so neither reaches the slot.)
;; The `_i32` and `_i64op` rows are CONTROLS (no rendezvous, or
;; the pool already reserved) that must stay correct and byte-identical.
(module
  (func $h (param f32) (result f32) (f32.mul (local.get 0) (f32.const 2)))

  ;; --- the issue's own reduction ------------------------------------------
  (func (export "br_bare") (result f32)
    (block (result f32) (br 0 (f32.const 1))))
  (func (export "brif_drop") (param i32) (result f32)
    (block (result f32) (br_if 0 (f32.const 2) (local.get 0)) (drop) (f32.const 3)))

  ;; --- edge kinds, carrying a PARAM -----------------------------------------
  (func (export "br_p") (param f32) (result f32)
    (block (result f32) (local.get 0) (br 0)))
  (func (export "brif_p") (param f32 i32) (result f32)
    (block (result f32) (local.get 0) (local.get 1) (br_if 0) (f32.const 1) (f32.add)))
  (func (export "brtable_p") (param f32 i32) (result f32)
    (block (result f32)
      (block (result f32) (local.get 0) (local.get 1) (br_table 0 1 0))
      (f32.const 0.5) (f32.add)))

  ;; --- the block result consumed by a unary op (spec `as-unary-operand`) ---
  (func (export "unary_br") (param f32) (result f32)
    (f32.neg (block (result f32) (br 0 (local.get 0)))))

  ;; --- a br_if OUT of a loop, carrying the accumulator ----------------------
  (func (export "loop_brif") (param f32 i32) (result f32)
    (local i32)
    (block (result f32)
      (loop
        (local.set 0 (f32.add (local.get 0) (f32.const 1.5)))
        (local.set 2 (i32.add (local.get 2) (i32.const 1)))
        (br_if 1 (local.get 0) (i32.ge_u (local.get 2) (i32.and (local.get 1) (i32.const 7))))
        (br 0))
      (f32.const -1)))

  ;; --- two f32 rendezvous slots in one function -----------------------------
  (func (export "nested2") (param f32 i32) (result f32)
    (block (result f32)
      (block (result f32)
        (br_if 0 (local.get 0) (i32.and (local.get 1) (i32.const 1)))
        (drop)
        (br 1 (f32.neg (local.get 0))))
      (f32.const 4) (f32.add)))

  ;; --- other frame users: i32 locals (1, 2, 3 => slot in padding / on R4) --
  (func (export "loc1") (param f32 i32) (result f32)
    (local i32)
    (local.set 2 (i32.add (local.get 1) (i32.const 3)))
    (block (result f32) (br_if 0 (local.get 0) (local.get 2)) (drop) (f32.const 7))
    (f32.convert_i32_s (local.get 2)) (f32.add))
  (func (export "loc2") (param f32 i32) (result f32)
    (local i32 i32)
    (local.set 2 (i32.add (local.get 1) (i32.const 3)))
    (local.set 3 (i32.mul (local.get 2) (i32.const 5)))
    (block (result f32) (br_if 0 (local.get 0) (local.get 2)) (drop) (f32.const 7))
    (f32.convert_i32_s (i32.add (local.get 2) (local.get 3))) (f32.add))
  (func (export "loc3") (param f32 i32) (result f32)
    (local i32 i32 i32)
    (local.set 2 (i32.add (local.get 1) (i32.const 3)))
    (local.set 3 (i32.mul (local.get 2) (i32.const 5)))
    (local.set 4 (i32.xor (local.get 3) (i32.const 9)))
    (block (result f32) (br_if 0 (local.get 0) (local.get 2)) (drop) (f32.const 7))
    (f32.convert_i32_s (i32.add (local.get 4) (i32.add (local.get 2) (local.get 3)))) (f32.add))
  (func (export "locf") (param f32 i32) (result f32)
    (local f32)
    (local.set 2 (f32.mul (local.get 0) (f32.const 0.5)))
    (block (result f32) (br_if 0 (local.get 2) (local.get 1)) (drop) (f32.const 7))
    (local.get 2) (f32.add))

  ;; --- a CALL in the same function (param-backing + VFP call-spill area) ---
  (func (export "call_brif") (param f32 i32) (result f32)
    (block (result f32) (br_if 0 (call $h (local.get 0)) (local.get 1)) (drop) (f32.const 7))
    (f32.convert_i32_s (local.get 1)) (f32.add))
  (func (export "call_after") (param f32 i32) (result f32)
    (block (result f32) (br_if 0 (local.get 0) (local.get 1)) (drop) (f32.const 7))
    (call $h) (f32.convert_i32_s (local.get 1)) (f32.add))

  ;; --- CONTROLS -------------------------------------------------------------
  ;; the pool is already reserved (an i64 op), so the slot is in the frame.
  (func (export "i64op_brif") (param f32 i32) (result f32)
    (local i64)
    (local.set 2 (i64.extend_i32_s (local.get 1)))
    (block (result f32) (br_if 0 (local.get 0) (local.get 1)) (drop) (f32.const 7))
    (f32.convert_i32_s (i32.wrap_i64 (i64.add (local.get 2) (i64.const 9)))) (f32.add))
  ;; the integer twin: carried in a register, no slot at all.
  (func (export "brif_i32") (param i32 i32) (result i32)
    (block (result i32) (br_if 0 (local.get 0) (local.get 1)) (drop) (i32.const 3))))
