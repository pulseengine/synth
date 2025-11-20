(** Synth Compiler Validation Test Driver

    This driver validates our formally verified WASM-to-ARM compiler by:
    1. Creating WASM test programs
    2. Compiling them using our extracted verified compiler
    3. Executing the ARM code using our extracted verified semantics
    4. Validating results match expected behavior
*)



(** Test result type *)
type test_result =
  | Pass of string
  | Fail of string * string  (* expected, actual *)
  | Error of string

(** Test case type *)
type test_case = {
  name: string;
  wasm: WasmInstructions.wasm_instr list;
  setup: ArmState.arm_state -> ArmState.arm_state;
  check: ArmState.arm_state -> test_result;
}

(** Create initial ARM state *)
let initial_state () : ArmState.arm_state =
  let zero = Integers.I32.zero in
  let zero_flags = {
    ArmState.flag_n = false;
    ArmState.flag_z = false;
    ArmState.flag_c = false;
    ArmState.flag_v = false;
  } in
  { ArmState.regs =
fun _ -> zero; ArmState.flags =
zero_flags; ArmState.vfp_regs =
fun _ -> zero; ArmState.mem =
fun _ -> zero; ArmState.locals =
fun _ -> zero; ArmState.globals =
fun _ -> zero }

(** Get register value as int *)
let get_reg_int (state : ArmState.arm_state) (reg : ArmInstructions.arm_reg) : int =
  let i32_val = ArmState.get_reg state reg in
  Z.to_int (Integers.I32.unsigned i32_val)

(** Run a single test case *)
let run_test (tc : test_case) : test_result =
  try
    (* 1. Setup initial state *)
    let init_state = initial_state () in
    let setup_state = tc.setup init_state in

    (* 2. Compile WASM to ARM *)
    let arm_code = Compilation.compile_wasm_program tc.wasm in

    (* 3. Execute ARM code *)
    let final_state_opt = ArmSemantics.exec_program arm_code setup_state in

    match final_state_opt with
    | None -> Error "Execution failed (None)"
    | Some final_state ->
        (* 4. Check result *)
        tc.check final_state
  with
  | e -> Error (Printexc.to_string e)

(** Print test result *)
let print_result (tc : test_case) (result : test_result) : unit =
  match result with
  | Pass msg ->
      Printf.printf "✅ PASS: %s - %s\n" tc.name msg
  | Fail (expected, actual) ->
      Printf.printf "❌ FAIL: %s\n" tc.name;
      Printf.printf "   Expected: %s\n" expected;
      Printf.printf "   Actual:   %s\n" actual
  | Error msg ->
      Printf.printf "💥 ERROR: %s - %s\n" tc.name msg

(** Test suite *)
let test_suite : test_case list = [
  (* Test 1: i32.const loads constant into R0 *)
  {
    name = "i32.const 42";
    wasm = [WasmInstructions.I32Const (Integers.I32.repr (Z.of_int 42))];
    setup = (fun s -> s);
    check = (fun state ->
      let r0 = get_reg_int state ArmInstructions.R0 in
      if r0 = 42 then
        Pass "R0 = 42"
      else
        Fail ("R0 = 42", Printf.sprintf "R0 = %d" r0)
    );
  };

  (* Test 2: i32.const with different value *)
  {
    name = "i32.const 100";
    wasm = [WasmInstructions.I32Const (Integers.I32.repr (Z.of_int 100))];
    setup = (fun s -> s);
    check = (fun state ->
      let r0 = get_reg_int state ArmInstructions.R0 in
      if r0 = 100 then
        Pass "R0 = 100"
      else
        Fail ("R0 = 100", Printf.sprintf "R0 = %d" r0)
    );
  };

  (* Test 3: i32.const 0 *)
  {
    name = "i32.const 0";
    wasm = [WasmInstructions.I32Const (Integers.I32.zero)];
    setup = (fun s -> s);
    check = (fun state ->
      let r0 = get_reg_int state ArmInstructions.R0 in
      if r0 = 0 then
        Pass "R0 = 0"
      else
        Fail ("R0 = 0", Printf.sprintf "R0 = %d" r0)
    );
  };

  (* Test 4: i32.add (requires stack handling) *)
  {
    name = "i32.add (R0 + R1)";
    wasm = [WasmInstructions.I32Add];
    setup = (fun s ->
      (* Setup: R0 = 10, R1 = 20 *)
      let s1 = ArmState.set_reg s ArmInstructions.R0 (Integers.I32.repr (Z.of_int 10)) in
      ArmState.set_reg s1 ArmInstructions.R1 (Integers.I32.repr (Z.of_int 20))
    );
    check = (fun state ->
      let r0 = get_reg_int state ArmInstructions.R0 in
      if r0 = 30 then
        Pass "R0 = 10 + 20 = 30"
      else
        Fail ("R0 = 30", Printf.sprintf "R0 = %d" r0)
    );
  };

  (* Test 5: i32.sub *)
  {
    name = "i32.sub (R0 - R1)";
    wasm = [WasmInstructions.I32Sub];
    setup = (fun s ->
      let s1 = ArmState.set_reg s ArmInstructions.R0 (Integers.I32.repr (Z.of_int 50)) in
      ArmState.set_reg s1 ArmInstructions.R1 (Integers.I32.repr (Z.of_int 13))
    );
    check = (fun state ->
      let r0 = get_reg_int state ArmInstructions.R0 in
      if r0 = 37 then
        Pass "R0 = 50 - 13 = 37"
      else
        Fail ("R0 = 37", Printf.sprintf "R0 = %d" r0)
    );
  };

  (* Test 6: i32.mul *)
  {
    name = "i32.mul (R0 * R1)";
    wasm = [WasmInstructions.I32Mul];
    setup = (fun s ->
      let s1 = ArmState.set_reg s ArmInstructions.R0 (Integers.I32.repr (Z.of_int 7)) in
      ArmState.set_reg s1 ArmInstructions.R1 (Integers.I32.repr (Z.of_int 6))
    );
    check = (fun state ->
      let r0 = get_reg_int state ArmInstructions.R0 in
      if r0 = 42 then
        Pass "R0 = 7 * 6 = 42"
      else
        Fail ("R0 = 42", Printf.sprintf "R0 = %d" r0)
    );
  };

  (* Test 7: i32.and *)
  {
    name = "i32.and (bitwise)";
    wasm = [WasmInstructions.I32And];
    setup = (fun s ->
      let s1 = ArmState.set_reg s ArmInstructions.R0 (Integers.I32.repr (Z.of_int 0b1111)) in
      ArmState.set_reg s1 ArmInstructions.R1 (Integers.I32.repr (Z.of_int 0b1010))
    );
    check = (fun state ->
      let r0 = get_reg_int state ArmInstructions.R0 in
      if r0 = 0b1010 then
        Pass "R0 = 0b1111 & 0b1010 = 0b1010"
      else
        Fail ("R0 = 10", Printf.sprintf "R0 = %d" r0)
    );
  };

  (* Test 8: i32.or *)
  {
    name = "i32.or (bitwise)";
    wasm = [WasmInstructions.I32Or];
    setup = (fun s ->
      let s1 = ArmState.set_reg s ArmInstructions.R0 (Integers.I32.repr (Z.of_int 0b1100)) in
      ArmState.set_reg s1 ArmInstructions.R1 (Integers.I32.repr (Z.of_int 0b0011))
    );
    check = (fun state ->
      let r0 = get_reg_int state ArmInstructions.R0 in
      if r0 = 0b1111 then
        Pass "R0 = 0b1100 | 0b0011 = 0b1111"
      else
        Fail ("R0 = 15", Printf.sprintf "R0 = %d" r0)
    );
  };

  (* Test 9: i32.xor *)
  {
    name = "i32.xor (bitwise)";
    wasm = [WasmInstructions.I32Xor];
    setup = (fun s ->
      let s1 = ArmState.set_reg s ArmInstructions.R0 (Integers.I32.repr (Z.of_int 0b1010)) in
      ArmState.set_reg s1 ArmInstructions.R1 (Integers.I32.repr (Z.of_int 0b0110))
    );
    check = (fun state ->
      let r0 = get_reg_int state ArmInstructions.R0 in
      if r0 = 0b1100 then
        Pass "R0 = 0b1010 ^ 0b0110 = 0b1100"
      else
        Fail ("R0 = 12", Printf.sprintf "R0 = %d" r0)
    );
  };

  (* Test 10: local.get index 0 *)
  {
    name = "local.get 0";
    wasm = [WasmInstructions.LocalGet 0];
    setup = (fun s ->
      (* Set local[0] via R4 which maps to local 0 *)
      ArmState.set_reg s ArmInstructions.R4 (Integers.I32.repr (Z.of_int 99))
    );
    check = (fun state ->
      let r0 = get_reg_int state ArmInstructions.R0 in
      if r0 = 99 then
        Pass "R0 = local[0] = 99"
      else
        Fail ("R0 = 99", Printf.sprintf "R0 = %d" r0)
    );
  };
]

(** Run all tests and report summary *)
let run_all_tests () : unit =
  Printf.printf "\n╔══════════════════════════════════════════════════════════╗\n";
  Printf.printf "║  Synth Compiler Validation Test Suite                   ║\n";
  Printf.printf "║  Testing: Verified WASM-to-ARM Compiler                 ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════╝\n\n";

  let total = List.length test_suite in
  let results = List.map (fun tc -> (tc, run_test tc)) test_suite in

  (* Print individual results *)
  Printf.printf "Individual Test Results:\n";
  Printf.printf "═══════════════════════════════════════════════════════════\n";
  List.iter (fun (tc, result) -> print_result tc result) results;

  (* Count pass/fail/error *)
  let count_result r = match r with
    | Pass _ -> (1, 0, 0)
    | Fail _ -> (0, 1, 0)
    | Error _ -> (0, 0, 1)
  in
  let (passes, failures, errors) =
    List.fold_left (fun (p, f, e) (_, result) ->
      let (dp, df, de) = count_result result in
      (p + dp, f + df, e + de)
    ) (0, 0, 0) results
  in

  (* Print summary *)
  Printf.printf "\n═══════════════════════════════════════════════════════════\n";
  Printf.printf "Test Summary:\n";
  Printf.printf "  Total Tests:  %d\n" total;
  Printf.printf "  ✅ Passed:    %d (%.1f%%)\n" passes (100.0 *. float_of_int passes /. float_of_int total);
  Printf.printf "  ❌ Failed:    %d (%.1f%%)\n" failures (100.0 *. float_of_int failures /. float_of_int total);
  Printf.printf "  💥 Errors:    %d (%.1f%%)\n" errors (100.0 *. float_of_int errors /. float_of_int total);
  Printf.printf "═══════════════════════════════════════════════════════════\n";

  if failures = 0 && errors = 0 then begin
    Printf.printf "\n🎉 ALL TESTS PASSED! 🎉\n";
    Printf.printf "The verified compiler behaves as mathematically proven!\n\n"
  end else begin
    Printf.printf "\n⚠️  ISSUES DETECTED ⚠️\n";
    Printf.printf "Review failed tests to identify discrepancies.\n\n"
  end

(** Main entry point *)
let () = run_all_tests ()
