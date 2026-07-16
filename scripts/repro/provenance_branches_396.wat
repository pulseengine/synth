;; VCR-DEC-003 (#396) provenance reconciliation fixture.
;;
;; Exercises all three covered branch transformations in one function so the
;; synth-provenance-v1 reconciliation gate is non-vacuous:
;;   - br_if      -> preserved (a real object conditional branch)
;;   - select     -> folded-predication (cmp->select fuse -> IT-block move, no branch)
;;   - br_table   -> split-into-object-branches (one WASM branch -> N object branches)
(module
  (func (export "decide") (param $x i32) (param $y i32) (result i32)
    (local $acc i32)
    ;; --- br_if: preserved ---
    (block $done
      (br_if $done (i32.lt_s (local.get $x) (i32.const 0)))
      (local.set $acc (i32.const 10)))

    ;; --- select: folded-predication ---
    ;; acc = (y > 100) ? acc+1 : acc-1
    (local.set $acc
      (select
        (i32.add (local.get $acc) (i32.const 1))
        (i32.sub (local.get $acc) (i32.const 1))
        (i32.gt_s (local.get $y) (i32.const 100))))

    ;; --- br_table: split-into-object-branches ---
    (block $b2
      (block $b1
        (block $b0
          (br_table $b0 $b1 $b2 (local.get $x)))
        ;; b0 target
        (local.set $acc (i32.add (local.get $acc) (i32.const 100)))
        (br $b2))
      ;; b1 target
      (local.set $acc (i32.add (local.get $acc) (i32.const 200))))
    ;; b2 target (fallthrough)
    (local.get $acc))
)
