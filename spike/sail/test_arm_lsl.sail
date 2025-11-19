/* Minimal ARM LSL (Logical Shift Left) instruction in Sail
 *
 * Demonstrates shift operations and shows how Sail handles
 * different operand types (shift amount vs data).
 *
 * Reference: ARM Architecture Reference Manual
 * Instruction: LSL Rd, Rn, #shift
 * Semantics: Rd = Rn << shift (logical shift left)
 */

default Order dec

/* Register type: 5-bit register number */
type regno = bits(5)

/* Word type: 32-bit value */
type word = bits(32)

/* Shift amount: 5 bits (0-31) */
type shiftamt = bits(5)

/* Register read effect */
val X : regno -> word effect {rreg}

/* Register write effect */
val wX : (regno, word) -> unit effect {wreg}

/* LSL instruction semantics
 *
 * Parameters:
 *   rd: Destination register
 *   rn: Source register
 *   shift: Shift amount (immediate, 0-31)
 *
 * Effect: Rd = Rn << shift
 */
val execute_lsl : (regno, regno, shiftamt) -> unit

function execute_lsl(rd, rn, shift) = {
  /* Read source register */
  let operand : word = X(rn);

  /* Perform logical shift left
   * Note: Sail automatically handles shift amount modulo 32
   * as per ARM specification
   */
  let result : word = operand << shift;

  /* Write result to destination register */
  wX(rd, result)
}

/* Key Observations:
 *
 * 1. Type Safety: shift is typed as bits(5), ensuring 0-31 range
 * 2. Operator Overloading: << works on bitvectors
 * 3. Implicit Modulo: Shift semantics match ARM spec exactly
 * 4. Concise: Only 3 lines of actual semantics!
 *
 * Compare with manual encoding in Rust (~7 lines) + manual Coq (~15 lines)
 * Sail: 3 lines → generates everything automatically!
 */
