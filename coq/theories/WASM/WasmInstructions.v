(** * WebAssembly Instructions

    This file defines the WebAssembly instruction set.
    Based on synth-synthesis/src/lib.rs WasmOp enum.
*)

Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.WASM.WasmValues.

(** ** WebAssembly Instructions *)

Inductive wasm_instr : Type :=
  (* Constants *)
  | I32Const : I32.int -> wasm_instr
  | I64Const : I64.int -> wasm_instr

  (* i32 arithmetic operations *)
  | I32Add : wasm_instr
  | I32Sub : wasm_instr
  | I32Mul : wasm_instr
  | I32DivS : wasm_instr
  | I32DivU : wasm_instr
  | I32RemS : wasm_instr
  | I32RemU : wasm_instr

  (* i32 bitwise operations *)
  | I32And : wasm_instr
  | I32Or : wasm_instr
  | I32Xor : wasm_instr
  | I32Shl : wasm_instr
  | I32ShrS : wasm_instr
  | I32ShrU : wasm_instr
  | I32Rotl : wasm_instr
  | I32Rotr : wasm_instr

  (* i32 comparison operations *)
  | I32Eqz : wasm_instr
  | I32Eq : wasm_instr
  | I32Ne : wasm_instr
  | I32LtS : wasm_instr
  | I32LtU : wasm_instr
  | I32GtS : wasm_instr
  | I32GtU : wasm_instr
  | I32LeS : wasm_instr
  | I32LeU : wasm_instr
  | I32GeS : wasm_instr
  | I32GeU : wasm_instr

  (* i32 bit manipulation *)
  | I32Clz : wasm_instr
  | I32Ctz : wasm_instr
  | I32Popcnt : wasm_instr

  (* i64 arithmetic operations *)
  | I64Add : wasm_instr
  | I64Sub : wasm_instr
  | I64Mul : wasm_instr
  | I64DivS : wasm_instr
  | I64DivU : wasm_instr
  | I64RemS : wasm_instr
  | I64RemU : wasm_instr

  (* i64 bitwise operations *)
  | I64And : wasm_instr
  | I64Or : wasm_instr
  | I64Xor : wasm_instr
  | I64Shl : wasm_instr
  | I64ShrS : wasm_instr
  | I64ShrU : wasm_instr
  | I64Rotl : wasm_instr
  | I64Rotr : wasm_instr

  (* i64 comparison operations *)
  | I64Eqz : wasm_instr
  | I64Eq : wasm_instr
  | I64Ne : wasm_instr
  | I64LtS : wasm_instr
  | I64LtU : wasm_instr
  | I64GtS : wasm_instr
  | I64GtU : wasm_instr
  | I64LeS : wasm_instr
  | I64LeU : wasm_instr
  | I64GeS : wasm_instr
  | I64GeU : wasm_instr

  (* i64 bit manipulation *)
  | I64Clz : wasm_instr
  | I64Ctz : wasm_instr
  | I64Popcnt : wasm_instr

  (* f32 arithmetic operations *)
  | F32Add : wasm_instr
  | F32Sub : wasm_instr
  | F32Mul : wasm_instr
  | F32Div : wasm_instr
  | F32Sqrt : wasm_instr
  | F32Min : wasm_instr
  | F32Max : wasm_instr
  | F32Abs : wasm_instr
  | F32Neg : wasm_instr
  | F32Copysign : wasm_instr
  | F32Ceil : wasm_instr
  | F32Floor : wasm_instr
  | F32Trunc : wasm_instr
  | F32Nearest : wasm_instr

  (* f32 comparison operations *)
  | F32Eq : wasm_instr
  | F32Ne : wasm_instr
  | F32Lt : wasm_instr
  | F32Gt : wasm_instr
  | F32Le : wasm_instr
  | F32Ge : wasm_instr

  (* f64 arithmetic operations *)
  | F64Add : wasm_instr
  | F64Sub : wasm_instr
  | F64Mul : wasm_instr
  | F64Div : wasm_instr
  | F64Sqrt : wasm_instr
  | F64Min : wasm_instr
  | F64Max : wasm_instr
  | F64Abs : wasm_instr
  | F64Neg : wasm_instr
  | F64Copysign : wasm_instr
  | F64Ceil : wasm_instr
  | F64Floor : wasm_instr
  | F64Trunc : wasm_instr
  | F64Nearest : wasm_instr

  (* f64 comparison operations *)
  | F64Eq : wasm_instr
  | F64Ne : wasm_instr
  | F64Lt : wasm_instr
  | F64Gt : wasm_instr
  | F64Le : wasm_instr
  | F64Ge : wasm_instr

  (* Conversion operations *)
  | I32WrapI64 : wasm_instr
  | I64ExtendI32S : wasm_instr
  | I64ExtendI32U : wasm_instr
  | I32TruncF32S : wasm_instr
  | I32TruncF32U : wasm_instr
  | I32TruncF64S : wasm_instr
  | I32TruncF64U : wasm_instr
  | I64TruncF32S : wasm_instr
  | I64TruncF32U : wasm_instr
  | I64TruncF64S : wasm_instr
  | I64TruncF64U : wasm_instr
  | F32ConvertI32S : wasm_instr
  | F32ConvertI32U : wasm_instr
  | F32ConvertI64S : wasm_instr
  | F32ConvertI64U : wasm_instr
  | F32DemoteF64 : wasm_instr
  | F64ConvertI32S : wasm_instr
  | F64ConvertI32U : wasm_instr
  | F64ConvertI64S : wasm_instr
  | F64ConvertI64U : wasm_instr
  | F64PromoteF32 : wasm_instr

  (* Memory operations *)
  | I32Load : nat -> wasm_instr  (* offset *)
  | I64Load : nat -> wasm_instr
  | F32Load : nat -> wasm_instr
  | F64Load : nat -> wasm_instr
  | I32Store : nat -> wasm_instr
  | I64Store : nat -> wasm_instr
  | F32Store : nat -> wasm_instr
  | F64Store : nat -> wasm_instr

  (* Local/Global variable operations *)
  | LocalGet : nat -> wasm_instr
  | LocalSet : nat -> wasm_instr
  | LocalTee : nat -> wasm_instr
  | GlobalGet : nat -> wasm_instr
  | GlobalSet : nat -> wasm_instr

  (* Control flow *)
  | Drop : wasm_instr
  | Select : wasm_instr
  | Nop : wasm_instr.

(** ** WebAssembly Programs *)

Definition wasm_program := list wasm_instr.

(** ** Examples *)

(** i32.add *)
Definition ex_i32_add : wasm_program :=
  [I32Const (I32.repr 5); I32Const (I32.repr 3); I32Add].

(** i32.mul *)
Definition ex_i32_mul : wasm_program :=
  [I32Const (I32.repr 4); I32Const (I32.repr 7); I32Mul].

(** local.get 0; i32.const 1; i32.add; local.set 0 *)
Definition ex_increment_local_0 : wasm_program :=
  [LocalGet 0; I32Const I32.one; I32Add; LocalSet 0].
