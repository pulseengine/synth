;; #676 — HETEROGENEOUS funcref table: mixed signatures in one table are
;; valid wasm; a call_indirect selecting a wrong-typed entry is a RUNTIME
;; trap (WASM Core §4.4.8, wasmtime: "indirect call type mismatch"), not a
;; validation error. The closed-world verifier can never verify such a
;; table (every expected type sees a mismatching slot), so the sound
;; lowering is the runtime type check itself: compare the indexed slot's
;; structural class id — from the type-id sidecar — against the expected
;; type's class id, and UDF on mismatch.
;;
;; Layout contract (#650/#664/#676): the runtime/harness links the table as
;; raw 4-byte code pointers at R11 (null slots as ZERO words) and copies
;; the object's `.synth.table_type_ids` section VERBATIM to
;; `R11 + sum(all table sizes) * 4` — here R11+20 (5 slots). Class ids are
;; structural (the $bin2 duplicate shares $bin's id — the meld
;; 31-decls/25-distinct shape); id 0 is reserved for null slots, so the
;; type compare subsumes the #664 null trap.
;;
;; Table image (5 slots): [$add(bin)=1, $neg(un)=2, $sub(bin2≡bin)=1, null=0,
;; null=0] — two signature classes INTERLEAVED, plus nulls, plus OOB past 5.
(module
  (type $bin (func (param i32 i32) (result i32)))
  (type $un (func (param i32) (result i32)))
  (type $bin2 (func (param i32 i32) (result i32))) ;; structural dup of $bin
  (table 5 5 funcref)
  (func $add (type $bin) (i32.add (local.get 0) (local.get 1)))
  (func $neg (type $un) (i32.sub (i32.const 0) (local.get 0)))
  (func $sub (type $bin2) (i32.sub (local.get 0) (local.get 1)))
  (elem (i32.const 0) func $add $neg $sub)
  ;; Expects class 1 (bin): slots 0/2 succeed, slot 1 type-traps,
  ;; slots 3/4 null-trap, >= 5 OOB-traps.
  (func (export "via2") (param $x i32) (param $sel i32) (result i32)
    (call_indirect (type $bin) (local.get $x) (i32.const 3) (local.get $sel)))
  ;; Expects class 2 (un): slot 1 succeeds, slots 0/2 type-trap.
  (func (export "via1") (param $x i32) (param $sel i32) (result i32)
    (call_indirect (type $un) (local.get $x) (local.get $sel))))
