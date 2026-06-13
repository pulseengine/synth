(module $mtx.wasm
  (type (;0;) (func (param i32) (result i32)))
  (type (;1;) (func (result i32)))
  (type (;2;) (func (param i32 i32)))
  (type (;3;) (func (param i32)))
  (type (;4;) (func (param i32 i32) (result i32)))
  (type (;5;) (func))
  (type (;6;) (func (param i32 i32 i32 i32)))
  (import "env" "k_spin_lock" (func $k_spin_lock (;0;) (type 0)))
  (import "env" "gale_w_current" (func $gale_w_current (;1;) (type 1)))
  (import "env" "k_spin_unlock" (func $k_spin_unlock (;2;) (type 2)))
  (import "env" "z_unpend_first_thread" (func $z_unpend_first_thread (;3;) (type 0)))
  (import "env" "arch_thread_return_value_set" (func $arch_thread_return_value_set (;4;) (type 2)))
  (import "env" "z_ready_thread" (func $z_ready_thread (;5;) (type 3)))
  (import "env" "z_reschedule" (func $z_reschedule (;6;) (type 4)))
  (table (;0;) 1 1 funcref)
  (memory (;0;) 2)
  (global $__stack_pointer (;0;) (mut i32) i32.const 65536)
  (export "memory" (memory 0))
  (export "gale_k_mutex_unlock_decide" (func $gale_k_mutex_unlock_decide))
  (export "z_impl_k_mutex_unlock" (func $z_impl_k_mutex_unlock))
  (func $core::panicking::panic_const::panic_const_add_overflow::hacec966df230a78f (;7;) (type 5)
    call $core::panicking::panic_fmt::h6651313c3e2c6c2f
    unreachable
  )
  (func $gale_k_mutex_unlock_decide (;8;) (type 6) (param i32 i32 i32 i32)
    (local i32 i32 i32)
    i32.const 2
    local.set 4
    i32.const -22
    local.set 5
    block ;; label = @1
      block ;; label = @2
        block ;; label = @3
          block ;; label = @4
            local.get 2
            i32.eqz
            local.tee 6
            i32.const 2
            i32.const 3
            local.get 1
            i32.const 1
            i32.gt_u
            select
            local.get 6
            local.get 3
            select
            local.get 2
            select
            local.tee 2
            br_table 3 (;@1;) 0 (;@4;) 2 (;@2;) 1 (;@3;) 3 (;@1;)
          end
          i32.const -1
          local.set 5
          local.get 1
          local.set 2
          br 2 (;@1;)
        end
        i32.const 0
        local.set 5
        i32.const 1
        local.set 4
        i32.const 0
        local.set 2
        br 1 (;@1;)
      end
      block ;; label = @2
        local.get 1
        i32.eqz
        br_if 0 (;@2;)
        local.get 1
        i32.const -1
        i32.add
        local.set 2
        i32.const 0
        local.set 5
        i32.const 0
        local.set 4
        br 1 (;@1;)
      end
      call $core::panicking::panic_const::panic_const_add_overflow::hacec966df230a78f
      unreachable
    end
    local.get 0
    local.get 2
    i32.store offset=8
    local.get 0
    local.get 4
    i32.store8 offset=4
    local.get 0
    local.get 5
    i32.store
  )
  (func $core::panicking::panic_fmt::h6651313c3e2c6c2f (;9;) (type 5)
    loop ;; label = @1
      br 0 (;@1;)
    end
  )
  (func $z_impl_k_mutex_unlock (;10;) (type 0) (param i32) (result i32)
    (local i32 i32 i32 i32)
    global.get $__stack_pointer
    i32.const 16
    i32.sub
    local.tee 1
    global.set $__stack_pointer
    i32.const 65536
    call $k_spin_lock
    local.set 2
    call $gale_w_current
    local.set 3
    local.get 1
    i32.const 4
    i32.add
    local.get 0
    i32.load offset=12
    local.get 0
    i32.load offset=8
    local.tee 4
    i32.eqz
    local.get 4
    local.get 3
    i32.eq
    call $gale_k_mutex_unlock_decide
    block ;; label = @1
      block ;; label = @2
        block ;; label = @3
          block ;; label = @4
            local.get 1
            i32.load8_u offset=8
            br_table 1 (;@3;) 2 (;@2;) 0 (;@4;) 2 (;@2;)
          end
          i32.const 65536
          local.get 2
          call $k_spin_unlock
          local.get 1
          i32.load offset=4
          local.set 3
          br 2 (;@1;)
        end
        local.get 0
        local.get 1
        i32.load offset=12
        i32.store offset=12
        i32.const 65536
        local.get 2
        call $k_spin_unlock
        i32.const 0
        local.set 3
        br 1 (;@1;)
      end
      local.get 0
      local.get 0
      call $z_unpend_first_thread
      local.tee 4
      i32.store offset=8
      block ;; label = @2
        local.get 4
        i32.eqz
        br_if 0 (;@2;)
        local.get 0
        i32.const 1
        i32.store offset=12
        i32.const 0
        local.set 3
        local.get 4
        i32.const 0
        call $arch_thread_return_value_set
        local.get 4
        call $z_ready_thread
        i32.const 65536
        local.get 2
        call $z_reschedule
        drop
        br 1 (;@1;)
      end
      i32.const 0
      local.set 3
      local.get 0
      i32.const 0
      i32.store offset=12
      i32.const 65536
      local.get 2
      call $k_spin_unlock
    end
    local.get 1
    i32.const 16
    i32.add
    global.set $__stack_pointer
    local.get 3
  )
  (@custom ".debug_abbrev" (after code) "\01\11\01%\0e\13\05\03\0e\10\17\1b\0e\11\01\12\06\00\00\029\01\03\0e\00\00\03.\01\11\01\12\06@\18\03\0e:\0b;\05?\19\00\00\04\1d\011\10\11\01\12\06X\0bY\05W\0b\00\00\05\1d\011\10\11\01\12\06X\0bY\0bW\0b\00\00\06\1d\001\10\11\01\12\06X\0bY\0bW\0b\00\00\07\1d\011\10U\17X\0bY\0bW\0b\00\00\08\1d\001\10U\17X\0bY\0bW\0b\00\00\09\11\01%\0e\13\05\03\0e\10\17\1b\0e\00\00\0a.\00n\0e\03\0e:\0b;\0b \0b\00\00\0b.\00n\0e\03\0e:\0b;\05?\19 \0b\00\00\0c.\00n\0e\03\0e:\0b;\05 \0b\00\00\00\01\11\01%\0e\13\05\03\0e\10\17\1b\0e\11\01U\17\00\00\029\01\03\0e\00\00\03.\00\11\01\12\06@\18n\0e\03\0e:\0b;\0b6\0b?\19\87\01\19\00\00\00")
  (@custom ".debug_info" (after code) "\c8\01\00\00\04\00\00\00\00\00\04\01\ae\07\00\00\1c\00\e7\05\00\00\00\00\00\00\18\07\00\00\ff\ff\ff\ffn\00\00\00\02\96\00\00\00\02p\00\00\00\02\d5\00\00\00\02{\06\00\00\03\ff\ff\ff\ffn\00\00\00\07\ed\03\00\00\00\00\9f{\06\00\00\01\de\01\04A\02\00\00\ff\ff\ff\ff`\00\00\00\01\e0\01)\054\02\00\00\ff\ff\ff\ff`\00\00\00\05m\0b\05\0a\02\00\00\ff\ff\ff\ff\15\00\00\00\05\10!\06\fe\01\00\00\ff\ff\ff\ff\0b\00\00\00\02L8\06\fe\01\00\00\ff\ff\ff\ff\01\00\00\00\02L\1a\06\9c\02\00\00\ff\ff\ff\ff\09\00\00\00\02L'\00\06\1c\02\00\00\ff\ff\ff\ff\01\00\00\00\05\117\05\0a\02\00\00\ff\ff\ff\ff\0d\00\00\00\05\11!\06\9c\02\00\00\ff\ff\ff\ff\0d\00\00\00\02L'\00\06\1c\02\00\00\ff\ff\ff\ff\01\00\00\00\05\12\1c\05\0a\02\00\00\ff\ff\ff\ff\03\00\00\00\05\12!\06\9c\02\00\00\ff\ff\ff\ff\03\00\00\00\02L'\00\07i\02\00\00\00\00\00\00\05\17\0e\08\bc\02\00\00\00\00\00\00\06\8c\0d\00\07$\03\00\00\18\00\00\00\05\15\13\08\ff\02\00\00\18\00\00\00\02\13\09\00\07i\02\00\000\00\00\00\05\1a\0e\08\bc\02\00\000\00\00\00\06\8c\0d\00\05{\02\00\00\ff\ff\ff\ff\05\00\00\00\05\19!\06\a9\02\00\00\ff\ff\ff\ff\05\00\00\00\06\90\0d\00\05{\02\00\00\ff\ff\ff\ff\05\00\00\00\05\1a%\06\a9\02\00\00\ff\ff\ff\ff\05\00\00\00\06\90\0d\00\05\0a\02\00\00\ff\ff\ff\ff\07\00\00\00\05\13!\06\9c\02\00\00\ff\ff\ff\ff\07\00\00\00\02L'\00\00\00\00\00\00\00\00\00\fd\00\00\00\04\00\00\00\00\00\04\09\ae\07\00\00\1c\00S\05\00\00\cf\01\00\00\18\07\00\00\02\96\00\00\00\02p\00\00\00\02\8b\00\00\00\02\13\00\00\00\0a\84\02\00\00\ae\00\00\00\01H\01\0a\8c\04\00\00\bd\00\00\00\01K\01\00\02\00\00\00\00\0a\e6\02\00\00\dd\00\00\00\017\01\00\00\02\d5\00\00\00\02\d9\00\00\00\0a\02\02\00\008\05\00\00\02\07\01\00\0b\d4\03\00\00{\06\00\00\03\d5\01\01\00\00\02\e5\00\00\00\02\e0\00\00\00\02h\00\00\00\02\87\00\00\00\02\09\00\00\00\0a\85\01\00\00\f9\00\00\00\05\8b\01\00\029\00\00\00\0a\10\04\00\00\cc\00\00\00\05\8f\01\00\00\00\00\00\00\02\f4\00\00\00\02\b9\00\00\00\02&\00\00\00\0c\f2\04\00\00\cc\00\00\00\04|\08\01\0c\f2\04\00\00\cc\00\00\00\04|\08\01\00\02\1d\00\00\00\0c=\02\00\00\f9\00\00\00\044\08\01\00\00\00\00d\00\00\00\04\00\00\00\00\00\04\09\ae\07\00\00\1c\00\84\06\00\00\00\03\00\00\18\07\00\00\02\f4\00\00\00\02\92\00\00\00\02\83\00\00\00\02/\00\00\00\0c?\03\00\00\a8\00\00\00\01\1a\01\01\00\00\00\00\02\96\00\00\00\02p\00\00\00\02\8b\00\00\00\02t\00\00\00\0a\8d\03\00\00B\05\00\00\02\12\01\00\00\00\00\00m\00\00\00\04\00\bd\00\00\00\04\01\ae\07\00\00\1c\00H\07\00\00~\03\00\00\18\07\00\00\00\00\00\00H\00\00\00\02\f4\00\00\00\02\ea\00\00\00\03\93\00\00\00\07\00\00\00\07\ed\03\00\00\00\00\9fT\01\00\00y\00\00\00\01<\03\02\5c\00\00\00\03\02\00\00\00\09\00\00\00\07\ed\03\00\00\00\00\9f\06\01\00\00C\00\00\00\01\ad\03\00\00\00\00")
  (@custom ".debug_ranges" (after code) "4\00\00\00:\00\00\00G\00\00\00V\00\00\00\00\00\00\00\00\00\00\00:\00\00\00;\00\00\00V\00\00\00^\00\00\00\00\00\00\00\00\00\00\00;\00\00\00@\00\00\00h\00\00\00m\00\00\00\00\00\00\00\00\00\00\00\93\00\00\00\9a\00\00\00\02\00\00\00\0b\00\00\00\00\00\00\00\00\00\00\00")
  (@custom ".debug_str" (after code) "{impl#6}\00{impl#24}\00{impl#14}\00{impl#4}\00{impl#3}\00{impl#91}\00{impl#20}\00panic_const_add_overflow\00panic_const\00support\00int\00DInt\00panic_fmt\00bit\00int_traits\00ops\00compiler_builtins\00bitor\00zero_widen\00num\00zero_widen_mul\00wrapping_mul\00Mul\00hi\00libm_math\00panicking\00core\00wrapping_add\00_ZN4core9panicking11panic_const24panic_const_add_overflow17hacec966df230a78fE\00_ZN4core9panicking9panic_fmt17h6651313c3e2c6c2fE\00_ZN85_$LT$i128$u20$as$u20$compiler_builtins..math..libm_math..support..int_traits..Int$GT$12wrapping_add17h6eae8ffc8a2a972fE\00_ZN17compiler_builtins3int3mul3Mul3mul17hb247b9926c818d3eE\00_ZN4core3num22_$LT$impl$u20$i128$GT$12wrapping_add17h39e0ed2ac59ea66dE\00_ZN60_$LT$i32$u20$as$u20$compiler_builtins..int..traits..HInt$GT$10zero_widen17ha40e207025490d4dE\00_ZN60_$LT$i64$u20$as$u20$compiler_builtins..int..traits..DInt$GT$2hi17hdd13204634fff05cE\00_ZN46_$LT$i128$u20$as$u20$core..ops..bit..BitOr$GT$5bitor17ha390e964dde414a8E\00_ZN17compiler_builtins3int6traits4DInt10from_lo_hi17he37c0ae81528c3c7E\00_ZN17compiler_builtins3int3mul8__multi317h70ffed272459f9b6E\00_ZN84_$LT$i64$u20$as$u20$compiler_builtins..math..libm_math..support..int_traits..Int$GT$12wrapping_mul17heca3e3ff5cb24af3E\00_ZN60_$LT$i32$u20$as$u20$compiler_builtins..int..traits..HInt$GT$14zero_widen_mul17h180751bf0237bd33E\00_ZN4core3num21_$LT$impl$u20$i64$GT$12wrapping_mul17h27113786ec65a562E\00mul<i128>\00from_lo_hi<i128>\00/rustc/e408947bfd200af42db322daf0fadfe7e26d3bd1/library/compiler-builtins/compiler-builtins/src/lib.rs/@/compiler_builtins.c79d60bea8bd3895-cgu.019\00/rustc/e408947bfd200af42db322daf0fadfe7e26d3bd1/library/compiler-builtins/compiler-builtins/src/lib.rs/@/compiler_builtins.c79d60bea8bd3895-cgu.176\00__multi3\00/rustc/e408947bfd200af42db322daf0fadfe7e26d3bd1/library/compiler-builtins/compiler-builtins/src/lib.rs/@/compiler_builtins.c79d60bea8bd3895-cgu.073\00/rustc/e408947bfd200af42db322daf0fadfe7e26d3bd1\00/rustc/e408947bfd200af42db322daf0fadfe7e26d3bd1/library/core/src/lib.rs/@/core.66cb4454208e2057-cgu.0\00clang LLVM (rustc version 1.94.1 (e408947bf 2026-03-25))\00")
  (@custom ".debug_line" (after code) "\cb\01\00\00\04\00F\01\00\00\01\01\01\fb\0e\0d\00\01\01\01\01\00\00\00\01\00\00\01library/compiler-builtins/compiler-builtins/src\00library/compiler-builtins/compiler-builtins/src/int\00library/core/src/num\00library/core/src/ops\00library/compiler-builtins/compiler-builtins/src/math/../../../libm/src/math/support\00\00macros.rs\00\01\00\00traits.rs\00\02\00\00int_macros.rs\00\03\00\00bit.rs\00\04\00\00mul.rs\00\02\00\00int_traits.rs\00\05\00\00\00\00\05\02\ff\ff\ff\ff\03\dd\03\01\04\02\05\15\0a\03\eb|\c8\06\ac\04\03\05\0d\06\03\b4\10 \04\02\05\15\03\bbo\90\04\03\05\0d\03\c5\10 \04\02\05\15\03\bbo\c8\04\03\05\0d\03\c5\10 \03\b8\7f<\04\04\05-\03\e5qf\04\03\05\0d\03\9b\0e \03\c8\00X\03\b8\7ft\04\04\05-\03\e5q\e4\04\03\05\0d\03\e3\0e\82\06X\06\03\b8\7fX\04\01\05\0e\03\acsX\02\01\00\01\01-\01\00\00\04\00'\01\00\00\01\01\01\fb\0e\0d\00\01\01\01\01\00\00\00\01\00\00\01library/compiler-builtins/compiler-builtins/src/int\00library/compiler-builtins/compiler-builtins/src\00library/core/src/num\00library/compiler-builtins/compiler-builtins/src/math/../../../libm/src/math/support\00\00traits.rs\00\01\00\00mul.rs\00\01\00\00macros.rs\00\02\00\00int_macros.rs\00\03\00\00int_traits.rs\00\04\00\00\00z\00\00\00\04\00t\00\00\00\01\01\01\fb\0e\0d\00\01\01\01\01\00\00\00\01\00\00\01library/core/src/ops\00library/compiler-builtins/compiler-builtins/src/int\00\00bit.rs\00\01\00\00traits.rs\00\02\00\00\00f\00\00\00\04\005\00\00\00\01\01\01\fb\0e\0d\00\01\01\01\01\00\00\00\01\00\00\01library/core/src\00\00panicking.rs\00\01\00\00\00\05\0e\0a\00\05\02\94\00\00\00\03\cf\00\01\06\03\b0\7fJ\02\02\00\01\01\05\11\0a\00\05\02\03\00\00\00\03\ae\01\01\02\08\00\01\01")
  (@custom "target_features" (after code) "\08+\0bbulk-memory+\0fbulk-memory-opt+\16call-indirect-overlong+\0amultivalue+\0fmutable-globals+\13nontrapping-fptoint+\0freference-types+\08sign-ext")
)
