(module
  ;; #740 minimal shape: a `br_if` at a loop head exiting an OUTER block.
  ;;
  ;;   block ;; @1
  ;;     block ;; @2
  ;;       loop ;; @3
  ;;         br_if 1 (;@2;)   <- empty-budget style head exit (x1 == 0)
  ;;         br_if 2 (;@1;)   <- bounds-style exit crossing two levels
  ;;         <24 stores of >16-bit constants (movw+movt) so both exits
  ;;          span > 254 bytes and must encode as 32-bit B<cond>.W (T3)>
  ;;         br_if 0 (;@3;)   <- back edge while the counter is nonzero
  ;;       end
  ;;     end
  ;;     <@2 join: marker store + NON-TAIL return  -> optimized path declines
  ;;      (#500), the function compiles on the DIRECT selector like gust_poll>
  ;;   end
  ;;   <@1 join: distinct marker store + distinct result>
  ;;
  ;; Correct execution with x1 == 0 lands at the @2 join: exactly ONE store
  ;; (mem[64] = 0x1111), result x0. The pre-fix encoder halved every wide
  ;; conditional-branch displacement, landing the head exit mid-padding —
  ;; spurious stores wasmtime never performs.
  (memory (export "memory") 1)
  (func (export "poll") (param i32 i32) (result i32)
    block ;; label = @1
      block ;; label = @2
        loop ;; label = @3
          local.get 1
          i32.eqz
          br_if 1 (;@2;)
          local.get 0
          i32.const 100
          i32.ge_u
          br_if 2 (;@1;)
          ;; ---- padding body: must NOT execute when the head exit is taken.
          ;; Distinct addresses/values so any mid-shape landing is visible in
          ;; the compared memory window.
          i32.const 128
          i32.const 10551297
          i32.store
          i32.const 132
          i32.const 10551298
          i32.store
          i32.const 136
          local.get 0
          i32.store
          i32.const 140
          i32.const 10551300
          i32.store
          i32.const 144
          i32.const 10551301
          i32.store
          i32.const 148
          i32.const 10551302
          i32.store
          i32.const 152
          i32.const 10551303
          i32.store
          i32.const 156
          i32.const 10551304
          i32.store
          i32.const 160
          local.get 1
          i32.store
          i32.const 164
          i32.const 10551306
          i32.store
          i32.const 168
          i32.const 10551307
          i32.store
          i32.const 172
          i32.const 10551308
          i32.store
          i32.const 176
          i32.const 10551309
          i32.store
          i32.const 180
          i32.const 10551310
          i32.store
          i32.const 184
          local.get 0
          i32.store
          i32.const 188
          i32.const 10551312
          i32.store
          i32.const 192
          i32.const 10551313
          i32.store
          i32.const 196
          i32.const 10551314
          i32.store
          i32.const 200
          i32.const 10551315
          i32.store
          i32.const 204
          i32.const 10551316
          i32.store
          i32.const 208
          local.get 1
          i32.store
          i32.const 212
          i32.const 10551318
          i32.store
          i32.const 216
          i32.const 10551319
          i32.store
          i32.const 220
          i32.const 10551320
          i32.store
          ;; ---- back edge: continue while the decremented counter is nonzero
          local.get 1
          i32.const 1
          i32.sub
          local.tee 1
          br_if 0 (;@3;)
        end
      end
      ;; @2 join — the loop-head exit and the loop fall-through both land here.
      i32.const 64
      i32.const 4369 ;; 0x1111
      i32.store
      local.get 0
      return
    end
    ;; @1 join — the bounds-style exit lands here.
    i32.const 68
    i32.const 8738 ;; 0x2222
    i32.store
    local.get 0
    i32.const 1
    i32.add
  )
)
