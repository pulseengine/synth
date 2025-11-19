/* Minimal ARM ADD instruction in Sail
 *
 * This demonstrates Sail's ability to express ARM instruction semantics
 * concisely and generate Coq definitions automatically.
 *
 * Reference: ARM Architecture Reference Manual
 * Instruction: ADD Rd, Rn, Rm
 * Semantics: Rd = Rn + Rm (32-bit wrapping addition)
 */

default Order dec

/* Register type: 5-bit register number */
type regno = bits(5)

/* Word type: 32-bit value */
type word = bits(32)

/* Register read effect */
val X : regno -> word effect {rreg}

/* Register write effect */
val wX : (regno, word) -> unit effect {wreg}

/* ADD instruction semantics
 *
 * Parameters:
 *   rd: Destination register
 *   rn: First source register
 *   rm: Second source register
 *
 * Effect: Rd = Rn + Rm
 */
val execute_add : (regno, regno, regno) -> unit

function execute_add(rd, rn, rm) = {
  /* Read source registers */
  let operand1 : word = X(rn);
  let operand2 : word = X(rm);

  /* Perform 32-bit addition (wrapping on overflow) */
  let result : word = operand1 + operand2;

  /* Write result to destination register */
  wX(rd, result)
}

/* Sail compiler will generate:
 * 1. Coq definition for execute_add
 * 2. Monadic semantics for register effects
 * 3. Bitvector operations
 * 4. Type-safe register access
 *
 * Command to generate Coq:
 *   sail -coq test_arm_add.sail -o test_arm_add_generated.v
 */
