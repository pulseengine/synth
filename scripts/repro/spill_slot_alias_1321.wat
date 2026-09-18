;; RQ-70-ALIAS (#1321) — a 54-line reduction of cpetig's falcon-cascade `step`
;; that reproduces the VCR-RA-003 `SpillSlotAliased` FALSE POSITIVE.
;;
;; WHY THIS FILE EXISTS. The reporter's module (#1318) is a third party's build
;; output, attached to an issue and not in this repository, so the verdict it
;; triggers was not re-derivable by anyone reading the tree. Measured: the
;; pattern occurs in ZERO of 772 corpus compiles (193 modules x 4 ARM configs,
;; 649 rc=0) — it existed only outside the repo, so no fix could be red-first.
;; This fixture is the smallest input found that emits the same stream shape.
;;
;; THE SHAPE, instruction-for-instruction the same as the 11k-instruction
;; original (offsets differ, sequence does not):
;;
;;    Str  Rn -> [sp,#N]        ; an ADDRESS (base + 8704)
;;    Mov  Rm, Rn              ; <- CONSUMED HERE, via a register copy
;;    Ldr  Rk, [R11 + Rm]      ; used as a memory address
;;    F32ReinterpretI32 ...
;;    ...
;;    Str  Rj -> [sp,#N]       ; a DIFFERENT value (reinterpreted f32)
;;    Cmp  Rj, #0              ; consumed from the register again
;;    ...
;;    Ldr  Ri <- [sp,#N]       ; reads the SECOND store's value — which is what
;;                             ; the code wants; the sign-bit mask that follows
;;                             ; is an f32.abs
;;
;; WHY IT IS A FALSE POSITIVE. `validate_final_allocation` flips its
;; `owner_reloaded` flag only on an `Ldr` FROM THE SLOT, so a value consumed
;; from a REGISTER looks permanently live to it. The first store is in fact a
;; DEAD STORE: nothing reads the slot before the second store overwrites it.
;; The checker is right that "a value was stored and overwritten unreloaded",
;; and wrong to call that aliasing, because nothing needed the slot copy.
;;
;; RED-FIRST BY CONSTRUCTION. Today this module DECLINES (#952, export `f`
;; skipped) and carries an EXPECTED_DECLINES entry in arm_corpus_sweep_973.py.
;; When #1321 is fixed it will COMPILE, the entry goes STALE, and the sweep
;; says so — the pin moving is the fix's own evidence.
(module
  (memory 1)
  (func $h (param i32) (result i32) local.get 0)
  (func (export "f") (param i32) (result i32) (local i32 f32 i32)
    local.get 0
    local.set 1
    local.get 0
    i32.const 8704
    i32.add
    local.tee 3
    local.get 3
    f32.load
    local.get 1
    i32.const 104
    i32.add
    local.get 0
    i32.add
    f32.load
    local.tee 2
    f32.abs
    f32.const 0x0p+0
    local.get 2
    i32.reinterpret_f32
    i32.const 2147483647
    i32.and
    i32.const 2139095040
    i32.lt_s
    select
    f32.add
    i32.const 0
    f32.load offset=8724
    f32.sub
    local.tee 2
    f32.const 0x0p+0
    local.get 2
    local.get 2
    i32.reinterpret_f32
    local.tee 3
    i32.const 0
    i32.lt_s
    select
    f32.const 0x0p+0
    local.get 3
    i32.const 2147483647
    i32.and
    i32.const -8388608
    i32.add
    i32.const 2130706432
    i32.lt_u
    select
    drop
    local.get 3
    call $h)
)
