open Integers

type wasm_instr =
| I32Const of int
| I64Const of int
| I32Add
| I32Sub
| I32Mul
| I32DivS
| I32DivU
| I32RemS
| I32RemU
| I32And
| I32Or
| I32Xor
| I32Shl
| I32ShrS
| I32ShrU
| I32Rotl
| I32Rotr
| I32Eqz
| I32Eq
| I32Ne
| I32LtS
| I32LtU
| I32GtS
| I32GtU
| I32LeS
| I32LeU
| I32GeS
| I32GeU
| I32Clz
| I32Ctz
| I32Popcnt
| I64Add
| I64Sub
| I64Mul
| I64DivS
| I64DivU
| I64RemS
| I64RemU
| I64And
| I64Or
| I64Xor
| I64Shl
| I64ShrS
| I64ShrU
| I64Rotl
| I64Rotr
| I64Eqz
| I64Eq
| I64Ne
| I64LtS
| I64LtU
| I64GtS
| I64GtU
| I64LeS
| I64LeU
| I64GeS
| I64GeU
| I64Clz
| I64Ctz
| I64Popcnt
| F32Add
| F32Sub
| F32Mul
| F32Div
| F32Sqrt
| F32Min
| F32Max
| F32Abs
| F32Neg
| F32Copysign
| F32Ceil
| F32Floor
| F32Trunc
| F32Nearest
| F32Eq
| F32Ne
| F32Lt
| F32Gt
| F32Le
| F32Ge
| F64Add
| F64Sub
| F64Mul
| F64Div
| F64Sqrt
| F64Min
| F64Max
| F64Abs
| F64Neg
| F64Copysign
| F64Ceil
| F64Floor
| F64Trunc
| F64Nearest
| F64Eq
| F64Ne
| F64Lt
| F64Gt
| F64Le
| F64Ge
| I32WrapI64
| I64ExtendI32S
| I64ExtendI32U
| I32TruncF32S
| I32TruncF32U
| I32TruncF64S
| I32TruncF64U
| I64TruncF32S
| I64TruncF32U
| I64TruncF64S
| I64TruncF64U
| F32ConvertI32S
| F32ConvertI32U
| F32ConvertI64S
| F32ConvertI64U
| F32DemoteF64
| F64ConvertI32S
| F64ConvertI32U
| F64ConvertI64S
| F64ConvertI64U
| F64PromoteF32
| I32Load of int
| I64Load of int
| F32Load of int
| F64Load of int
| I32Store of int
| I64Store of int
| F32Store of int
| F64Store of int
| LocalGet of int
| LocalSet of int
| LocalTee of int
| GlobalGet of int
| GlobalSet of int
| Drop
| Select
| Nop

type wasm_program = wasm_instr list
