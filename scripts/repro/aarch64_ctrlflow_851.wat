;; #851 aarch64 FULL control flow — if/else, loop (back-edge), return.
;;
;; Every function is a shape the void-block-only #538 increment DECLINED and the
;; #851 increment must lower bit-identically to wasmtime. The observable
;; taken/not-taken (or trap-vs-return) difference makes a wrong branch offset
;; loud (see aarch64_ctrlflow_851_differential.py).

(module
  ;; --- if / else (void bodies, both arms reachable) ---
  ;; if cond != 0 -> store a into local; else store b. Return the local.
  ;; Exercises: cbz to else, unconditional b over else, join at end.
  (func (export "if_else_pick") (param i32 i32 i32) (result i32)
    (local i32)
    local.get 0
    (if
      (then
        local.get 1
        local.set 3)
      (else
        local.get 2
        local.set 3))
    local.get 3)

  ;; if WITHOUT else (void). cond -> guard a trap. cond 0 -> fall through.
  (func (export "if_noelse_guard") (param i32) (result i32)
    local.get 0
    (if
      (then
        unreachable))
    local.get 0)

  ;; nested if/else -> classic max(a,b) via compare + branch.
  (func (export "if_max") (param i32 i32) (result i32)
    (local i32)
    local.get 0
    local.get 1
    i32.gt_s
    (if
      (then
        local.get 0
        local.set 2)
      (else
        local.get 1
        local.set 2))
    local.get 2)

  ;; --- loop with back-edge (br to loop label = BACKWARD) ---
  ;; Sum 0..n-1 into an accumulator; classic counting loop.
  ;; Counter + accumulator live in NON-PARAM LOCALS (memory slots), which is
  ;; what makes the void loop sound: the value stack is empty at the back-edge.
  (func (export "count_sum") (param i32) (result i32)
    (local i32) ;; local 1: i (counter)
    (local i32) ;; local 2: acc
    (block
      (loop
        ;; if i >= n, exit the block
        local.get 1
        local.get 0
        i32.ge_s
        br_if 1
        ;; acc += i
        local.get 2
        local.get 1
        i32.add
        local.set 2
        ;; i += 1
        local.get 1
        i32.const 1
        i32.add
        local.set 1
        ;; back-edge to loop
        br 0))
    local.get 2)

  ;; countdown loop: while n != 0 { n-- ; iters++ } ; return iters.
  (func (export "countdown") (param i32) (result i32)
    (local i32) ;; iters
    (block
      (loop
        local.get 0
        i32.eqz
        br_if 1
        local.get 0
        i32.const 1
        i32.sub
        local.set 0
        local.get 1
        i32.const 1
        i32.add
        local.set 1
        br 0))
    local.get 1)

  ;; --- early return ---
  ;; if a < 0 return -1 early; else return a*2.
  (func (export "early_ret") (param i32) (result i32)
    local.get 0
    i32.const 0
    i32.lt_s
    (if
      (then
        i32.const -1
        return))
    local.get 0
    i32.const 2
    i32.mul
    return)

  ;; return inside a loop: return first i where i*i >= n.
  (func (export "isqrt_ceil") (param i32) (result i32)
    (local i32) ;; i
    (loop
      local.get 1
      local.get 1
      i32.mul
      local.get 0
      i32.ge_s
      (if
        (then
          local.get 1
          return))
      local.get 1
      i32.const 1
      i32.add
      local.set 1
      br 0)
    ;; unreachable fall-through (loop is infinite until return); keep validator happy
    i32.const -1)
)
