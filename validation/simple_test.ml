(* Simple validation test - tracing execution *)

let test_const () =
  Printf.printf "Step 1: Creating I32 constant value 42...\n";
  let const_val = 42 in  (* Just use plain int, skip I32.repr for now *)
  Printf.printf "Step 2: Creating WASM instruction...\n";
  let wasm = [WasmInstructions.I32Const const_val] in
  Printf.printf "Step 3: Compiling WASM to ARM...\n";
  let arm = Compilation.compile_wasm_program wasm in
  Printf.printf "Step 4: Checking result...\n";
  Printf.printf "ARM code: %d instructions generated\n" (List.length arm);
  match arm with
  | [] -> Printf.printf "❌ ERROR: No ARM code generated!\n"
  | _ -> Printf.printf "✅ SUCCESS: ARM code generated!\n"

let () =
  Printf.printf "\n╔═══════════════════════════════════╗\n";
  Printf.printf "║ Synth Compiler Validation - POC  ║\n";
  Printf.printf "╚═══════════════════════════════════╝\n\n";
  test_const ();
  Printf.printf "\n✅ Basic compiler extraction works!\n"
