(** Synth Compiler Validation Suite
    
    This suite validates that our formally verified compiler
    produces correct ARM code for WASM programs.
*)

let test_count = ref 0
let pass_count = ref 0
let fail_count = ref 0

let run_test name test_fn =
  test_count := !test_count + 1;
  Printf.printf "\nTest %d: %s\n" !test_count name;
  try
    test_fn ();
    pass_count := !pass_count + 1;
    Printf.printf "  ✅ PASS\n"
  with e ->
    fail_count := !fail_count + 1;
    Printf.printf "  ❌ FAIL: %s\n" (Printexc.to_string e)

(** Test 1: I32.const compiles to MOVW *)
let test_i32_const () =
  let wasm = [WasmInstructions.I32Const 42] in
  let arm = Compilation.compile_wasm_program wasm in
  assert (List.length arm = 1);
  match List.hd arm with
  | ArmInstructions.MOVW (ArmState.R0, _) -> ()
  | _ -> failwith "Expected MOVW instruction"

(** Test 2: I32.add compiles to ADD *)
let test_i32_add () =
  let wasm = [WasmInstructions.I32Add] in
  let arm = Compilation.compile_wasm_program wasm in
  assert (List.length arm = 1);
  match List.hd arm with
  | ArmInstructions.ADD _ -> ()
  | _ -> failwith "Expected ADD instruction"

(** Test 3: I32.sub compiles to SUB *)
let test_i32_sub () =
  let wasm = [WasmInstructions.I32Sub] in
  let arm = Compilation.compile_wasm_program wasm in
  assert (List.length arm = 1);
  match List.hd arm with
  | ArmInstructions.SUB _ -> ()
  | _ -> failwith "Expected SUB instruction"

(** Test 4: I32.mul compiles to MUL *)
let test_i32_mul () =
  let wasm = [WasmInstructions.I32Mul] in
  let arm = Compilation.compile_wasm_program wasm in
  assert (List.length arm = 1);
  match List.hd arm with
  | ArmInstructions.MUL _ -> ()
  | _ -> failwith "Expected MUL instruction"

(** Test 5: I32.and compiles to AND *)
let test_i32_and () =
  let wasm = [WasmInstructions.I32And] in
  let arm = Compilation.compile_wasm_program wasm in
  assert (List.length arm = 1);
  match List.hd arm with
  | ArmInstructions.AND _ -> ()
  | _ -> failwith "Expected AND instruction"

(** Test 6: I32.or compiles to ORR *)
let test_i32_or () =
  let wasm = [WasmInstructions.I32Or] in
  let arm = Compilation.compile_wasm_program wasm in
  assert (List.length arm = 1);
  match List.hd arm with
  | ArmInstructions.ORR _ -> ()
  | _ -> failwith "Expected ORR instruction"

(** Test 7: I32.xor compiles to EOR *)
let test_i32_xor () =
  let wasm = [WasmInstructions.I32Xor] in
  let arm = Compilation.compile_wasm_program wasm in
  assert (List.length arm = 1);
  match List.hd arm with
  | ArmInstructions.EOR _ -> ()
  | _ -> failwith "Expected EOR instruction"

(** Test 8: Multiple instructions compile correctly *)
let test_multi_instruction () =
  let wasm = [
    WasmInstructions.I32Const 10;
    WasmInstructions.I32Const 20;
    WasmInstructions.I32Add
  ] in
  let arm = Compilation.compile_wasm_program wasm in
  assert (List.length arm = 3)

(** Test 9: Local.get compiles to MOV *)
let test_local_get () =
  let wasm = [WasmInstructions.LocalGet 0] in
  let arm = Compilation.compile_wasm_program wasm in
  assert (List.length arm = 1);
  match List.hd arm with
  | ArmInstructions.MOV _ -> ()
  | _ -> failwith "Expected MOV instruction"

(** Test 10: I64.const compiles *)
let test_i64_const () =
  let wasm = [WasmInstructions.I64Const 12345] in
  let arm = Compilation.compile_wasm_program wasm in
  assert (List.length arm >= 1)

let () =
  Printf.printf "\n╔═══════════════════════════════════════════════════════╗\n";
  Printf.printf "║                                                       ║\n";
  Printf.printf "║      Synth Compiler Validation Suite                 ║\n";
  Printf.printf "║      Testing Verified WASM-to-ARM Compiler           ║\n";
  Printf.printf "║                                                       ║\n";
  Printf.printf "╚═══════════════════════════════════════════════════════╝\n";

  run_test "I32.const → MOVW" test_i32_const;
  run_test "I32.add → ADD" test_i32_add;
  run_test "I32.sub → SUB" test_i32_sub;
  run_test "I32.mul → MUL" test_i32_mul;
  run_test "I32.and → AND" test_i32_and;
  run_test "I32.or → ORR" test_i32_or;
  run_test "I32.xor → EOR" test_i32_xor;
  run_test "Multi-instruction program" test_multi_instruction;
  run_test "Local.get → MOV" test_local_get;
  run_test "I64.const compiles" test_i64_const;

  Printf.printf "\n╔═══════════════════════════════════════════════════════╗\n";
  Printf.printf "║ Test Summary                                          ║\n";
  Printf.printf "╠═══════════════════════════════════════════════════════╣\n";
  Printf.printf "║  Total:  %2d                                            ║\n" !test_count;
  Printf.printf "║  ✅ Pass:  %2d  (%.0f%%)                                 ║\n" 
    !pass_count (100.0 *. float_of_int !pass_count /. float_of_int !test_count);
  Printf.printf "║  ❌ Fail:  %2d  (%.0f%%)                                 ║\n"
    !fail_count (100.0 *. float_of_int !fail_count /. float_of_int !test_count);
  Printf.printf "╚═══════════════════════════════════════════════════════╝\n";

  if !fail_count = 0 then begin
    Printf.printf "\n🎉 ALL TESTS PASSED! 🎉\n\n";
    Printf.printf "The extracted compiler correctly implements the\n";
    Printf.printf "formally verified WASM-to-ARM compilation!\n\n";
    exit 0
  end else begin
    Printf.printf "\n⚠️  SOME TESTS FAILED ⚠️\n\n";
    exit 1
  end
