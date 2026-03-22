;; Large function test for Synth pre-release validation
;; Contains 50+ operations: nested loops, many locals, arithmetic chains
;; Purpose: verify no register allocator panic and compilation succeeds

(module
  ;; Large function with nested loops, conditionals, arithmetic chains
  ;; Computes a hash-like value from the input using various operations
  (func (export "large_compute") (param $n i32) (result i32)
    (local $acc i32)
    (local $tmp i32)
    (local $i i32)
    (local $j i32)
    (local $flag i32)

    ;; Initialize accumulator
    local.get $n
    local.set $acc

    ;; Outer loop: iterate $n times
    local.get $n
    local.set $i
    (block $outer_exit
      (loop $outer_loop
        ;; Check if i > 0
        local.get $i
        i32.const 0
        i32.le_s
        br_if $outer_exit

        ;; Inner loop: 3 iterations of bit mixing
        i32.const 3
        local.set $j
        (block $inner_exit
          (loop $inner_loop
            local.get $j
            i32.const 0
            i32.le_s
            br_if $inner_exit

            ;; Arithmetic chain: acc = ((acc * 31) + i) ^ (j << 3)
            local.get $acc
            i32.const 31
            i32.mul
            local.get $i
            i32.add
            local.set $tmp

            local.get $j
            i32.const 3
            i32.shl
            local.get $tmp
            i32.xor
            local.set $acc

            ;; Conditional: if acc is negative, negate it
            local.get $acc
            i32.const 0
            i32.lt_s
            (if
              (then
                i32.const 0
                local.get $acc
                i32.sub
                local.set $acc
              )
            )

            ;; More bit manipulation
            local.get $acc
            i32.const 0xFF
            i32.and
            local.get $acc
            i32.const 8
            i32.shr_u
            i32.or
            local.set $acc

            ;; Decrement j
            local.get $j
            i32.const 1
            i32.sub
            local.set $j

            br $inner_loop
          )
        )

        ;; Apply final mixing per outer iteration
        local.get $acc
        i32.const 17
        i32.rotl
        local.get $i
        i32.xor
        local.set $acc

        ;; Decrement i
        local.get $i
        i32.const 1
        i32.sub
        local.set $i

        br $outer_loop
      )
    )

    ;; Final result: mask to positive i32
    local.get $acc
    i32.const 0x7FFFFFFF
    i32.and
  )

  ;; Second large function: multi-way branch dispatch
  (func (export "dispatch") (param $cmd i32) (param $val i32) (result i32)
    (local $result i32)

    local.get $val
    local.set $result

    (block $default
      (block $case3
        (block $case2
          (block $case1
            (block $case0
              local.get $cmd
              br_table $case0 $case1 $case2 $case3 $default
            )
            ;; case 0: double
            local.get $result
            i32.const 2
            i32.mul
            local.set $result
            br $default
          )
          ;; case 1: negate
          i32.const 0
          local.get $result
          i32.sub
          local.set $result
          br $default
        )
        ;; case 2: count leading zeros
        local.get $result
        i32.clz
        local.set $result
        br $default
      )
      ;; case 3: rotate right by 7
      local.get $result
      i32.const 7
      i32.rotr
      local.set $result
    )

    local.get $result
  )
)

;; Assertions for large_compute
(assert_return (invoke "large_compute" (i32.const 1)) (i32.const 287))
(assert_return (invoke "large_compute" (i32.const 0)) (i32.const 0))

;; Assertions for dispatch
(assert_return (invoke "dispatch" (i32.const 0) (i32.const 5)) (i32.const 10))
(assert_return (invoke "dispatch" (i32.const 1) (i32.const 5)) (i32.const -5))
(assert_return (invoke "dispatch" (i32.const 2) (i32.const 256)) (i32.const 23))
