(module
  (memory 1)
  (export "memory" (memory 0))

  ;; #500 shape A — an if/else DESUGARED as nested block + br_if + br (the
  ;; issue's repro A). The br_if targets the INNER block's end while an
  ;; unconditional br to the OUTER end sits between the br_if and that end.
  ;; c==0 -> store 200 at addr 4; c!=0 -> store 100 at addr 4.
  (func (export "ifelse") (param $c i32)
    (block $end
      (block $else
        (br_if $else (i32.eqz (local.get $c)))
        (i32.store (i32.const 4) (i32.const 100))
        (br $end))
      (i32.store (i32.const 4) (i32.const 200))))

  ;; #500 shape B — two sequential (sibling) blocks, each exited by a br_if.
  ;; The first block is followed by more top-level content (the second block),
  ;; the trigger the issue isolates. a==0 -> skip store 11; b==0 -> skip
  ;; store16 22.
  (func (export "seqblocks") (param $a i32) (param $b i32)
    (block $b1
      (br_if $b1 (i32.eqz (local.get $a)))
      (i32.store (i32.const 8) (i32.const 11)))
    (block $b2
      (br_if $b2 (i32.eqz (local.get $b)))
      (i32.store16 (i32.const 12) (i32.const 22))))

  ;; #500 shape C — a REAL `if`/`else` construct (decodes to WasmOp::If/Else,
  ;; not the block+br_if desugaring). c!=0 -> store 300; c==0 -> store 400.
  (func (export "real_ifelse") (param $c i32)
    (if (local.get $c)
      (then (i32.store (i32.const 16) (i32.const 300)))
      (else (i32.store (i32.const 16) (i32.const 400)))))

  ;; #500 shape C' — `if` with no else. c!=0 -> store 55 at 20; always store
  ;; 66 at 24 afterwards (the join must be reached in both directions).
  (func (export "real_if") (param $c i32)
    (if (local.get $c)
      (then (i32.store (i32.const 20) (i32.const 55))))
    (i32.store (i32.const 24) (i32.const 66)))

  ;; #500 shape D — function-level `br` (depth reaches the implicit function
  ;; body). c!=0 -> store 77 then RETURN (88 must NOT run); c==0 -> skip to
  ;; block end, store 88 only.
  (func (export "br_func") (param $c i32)
    (block $b
      (br_if $b (i32.eqz (local.get $c)))
      (i32.store (i32.const 28) (i32.const 77))
      (br 1))
    (i32.store (i32.const 32) (i32.const 88)))

  ;; #500 shape E — early (non-tail) `return`. c!=0 -> store 99 then RETURN
  ;; (111 must NOT run); c==0 -> store 111 only.
  (func (export "early_ret") (param $c i32)
    (block $b
      (br_if $b (i32.eqz (local.get $c)))
      (i32.store (i32.const 36) (i32.const 99))
      (return))
    (i32.store (i32.const 40) (i32.const 111)))
)
