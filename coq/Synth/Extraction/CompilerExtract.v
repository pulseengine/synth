(** * Extraction of Synth Compiler to OCaml

    This file extracts our formally verified WASM-to-ARM compiler
    from Coq to executable OCaml code for validation testing.
*)

From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlString.
From Stdlib Require Import ExtrOcamlIntConv.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlZInt.

(* Import our compiler modules *)
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.WASM.WasmValues.
Require Import Synth.WASM.WasmInstructions.
Require Import Synth.WASM.WasmSemantics.
Require Import Synth.ARM.ArmInstructions.
Require Import Synth.ARM.ArmState.
Require Import Synth.ARM.ArmSemantics.
Require Import Synth.Synth.Compilation.

(** ** Extraction Configuration *)

(* Extract nat to OCaml int *)
Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

(* Extract bool to OCaml bool *)
Extract Inductive bool => "bool" [ "true" "false" ].

(* Extract option to OCaml option *)
Extract Inductive option => "option" [ "Some" "None" ].

(* Extract list to OCaml list *)
Extract Inductive list => "list" [ "[]" "(::)" ].

(* Extract unit *)
Extract Inductive unit => "unit" [ "()" ].

(* Extract pairs *)
Extract Inductive prod => "(*)"  [ "(,)" ].

(* Extract sumbool to bool *)
Extract Inductive sumbool => "bool" [ "true" "false" ].

(* Extract integers - use Zarith library *)
(* I32.int and I64.int are defined in terms of Z *)
Extraction Blacklist String List.

(** ** Main Extraction *)

(* Extract the compiler and key functions *)
Extraction Language OCaml.

(* Create a validation module *)
Separate Extraction
  (* Compiler *)
  compile_wasm_to_arm
  compile_wasm_program

  (* WASM Semantics *)
  exec_wasm_instr
  exec_wasm_program

  (* ARM Semantics *)
  exec_instr
  exec_program

  (* State constructors *)
  mkWasmState
  mkArmState

  (* Integer operations *)
  I32.add I32.sub I32.mul
  I64.add I64.sub I64.mul

  (* Utilities *)
  get_reg set_reg
  get_local set_local
  load_mem store_mem.

(** Extraction complete. This will generate OCaml files:
    - Compilation.ml - The compiler
    - WasmSemantics.ml - WASM execution
    - ArmSemantics.ml - ARM execution
    - Supporting modules

    These can be compiled with OCaml and linked into a test harness
    for validation against Sail ARM emulator.
*)
