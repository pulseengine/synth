;; #1635 (cpetig) — a register-homed param (r0, an sret out-pointer) read only
;; AFTER a forward block join is clobbered by `movw r0, #0`, so the trailing
;; `i32.store`s through it land at linear-memory 0/4 instead of the pointer.
;;
;; $bump is the reporter's rustc output VERBATIM (bump.wasm from the issue's
;; bump.zip, sha256 6364d2105d0ef90272f9c877fd3fcea4d8e65cbc3d8a70d6767aba21b86bf3fb,
;; `rustc 1.99.1 --target wasm32-unknown-unknown -O -C panic=abort`), printed
;; by `wasm-tools print`, with only an export added. $min is the reporter's
;; greedy-reduced min.wat function (its dead code is a reduction artefact).
(module
  (memory (export "memory") 17)
  (func $bump (export "bump") (param i32 i32 i32)
    (local i32 i32 i32)
    i32.const 0
    local.set 3
    block ;; label = @1
      block ;; label = @2
        local.get 2
        i32.const 16
        i32.le_u
        br_if 0 (;@2;)
        br 1 (;@1;)
      end
      local.get 2
      i32.popcnt
      i32.const 1
      i32.ne
      br_if 0 (;@1;)
      i32.const 0
      local.set 3
      block ;; label = @2
        local.get 2
        i32.const -1
        i32.add
        local.tee 4
        i32.const 0
        i32.load offset=1048576
        i32.add
        local.tee 5
        local.get 4
        i32.ge_u
        br_if 0 (;@2;)
        br 1 (;@1;)
      end
      i32.const 0
      local.set 3
      block ;; label = @2
        local.get 5
        i32.const 0
        local.get 2
        i32.sub
        i32.and
        local.tee 4
        local.get 1
        i32.add
        local.tee 2
        local.get 4
        i32.ge_u
        br_if 0 (;@2;)
        br 1 (;@1;)
      end
      local.get 2
      i32.const 8192
      i32.gt_u
      br_if 0 (;@1;)
      i32.const 0
      local.get 2
      i32.store offset=1048576
      i32.const 1
      local.set 3
    end
    local.get 0
    local.get 4
    i32.store offset=4
    local.get 0
    local.get 3
    i32.store
  )
  (func $min (export "min") (param $out i32) (param $size i32) (param $align i32)
    (local $r i32) (local $a i32) (local $c i32)
    i32.const 0
    local.set $r
    block
      i32.const 0
      local.set $r
      block
        i32.const -1
        i32.const 0
        local.get $a
        i32.ge_u
        br 1
      end
      i32.const 0
      local.set $r
      local.get $c
      i32.const 0
      local.get $align
      i32.sub
      i32.and
      local.get $size
      i32.add
      local.get $a
      i32.ge_u
      br_if 0
      i32.const 1
      local.set $r
    end
    local.get $out
    local.get $a
    i32.store offset=4
    local.get $out
    local.get $r
    i32.store)
)
