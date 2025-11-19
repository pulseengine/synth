/* Minimal ARM AND instruction in Sail
 *
 * Demonstrates bitwise operations in Sail and automatic Coq generation.
 *
 * Reference: ARM Architecture Reference Manual
 * Instruction: AND Rd, Rn, Rm
 * Semantics: Rd = Rn & Rm (bitwise AND)
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

/* AND instruction semantics
 *
 * Parameters:
 *   rd: Destination register
 *   rn: First source register
 *   rm: Second source register
 *
 * Effect: Rd = Rn & Rm
 */
val execute_and : (regno, regno, regno) -> unit

function execute_and(rd, rn, rm) = {
  /* Read source registers */
  let operand1 : word = X(rn);
  let operand2 : word = X(rm);

  /* Perform bitwise AND */
  let result : word = operand1 & operand2;

  /* Write result to destination register */
  wX(rd, result)
}

/* Note: Sail's bitwise operators map directly to Coq bitvector operations
 *
 * Sail:  operand1 & operand2
 * Coq:   bvand operand1 operand2
 *
 * This automatic translation is a key benefit of using Sail!
 */
