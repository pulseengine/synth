# I64 Codegen Survey — what `instruction_selector.rs` actually emits

**Purpose.** Inventory the exact `ArmOp` sequence emitted by the Rust compiler
(`crates/synth-synthesis/src/instruction_selector.rs`) for every WASM i64 op.
Drives the v0.8.0 alignment of `coq/Synth/Synth/Compilation.v`.

**Method.** Read `instruction_selector.rs:1390–1786` (the i64 selection block)
and `arm_encoder.rs:79–114, 4645–...` (to confirm `Adds/Adc/Subs/Sbc` are
*real* ARM instructions and that `I64*` pseudo-ops are *high-level* opcodes that
the encoder expands to multi-instruction sequences).

**Register-pair convention** (Rust, in selection — confirmed at lines 1392–1786):

| Slot          | Lo  | Hi  |
|---------------|-----|-----|
| i64 operand 1 | R0  | R1  |
| i64 operand 2 | R2  | R3  |
| i64 result    | R0  | R1  |

This is the convention the Rust compiler hard-codes. It is the same convention
this PR adopts in `Compilation.v`.

**Critical correction.** The pre-PR `Compilation.v` modeled all i64 ops as
operating on a **single** 32-bit register (`R0`, `R1`) and even compared two i64
operands as `R0` vs. `R1` — discarding the high half entirely. The Rust
compiler does no such thing.

---

## 1. Arithmetic (real ADD/ADC, SUB/SBC pairs)

| WASM op | Rust ArmOp sequence | Source |
|---------|---------------------|--------|
| `I64Add` | `Adds R0,R0,R2; Adc R1,R1,R3` | `instruction_selector.rs:1450–1463` |
| `I64Sub` | `Subs R0,R0,R2; Sbc R1,R1,R3` | `instruction_selector.rs:1465–1478` |

`Adds`/`Subs` set the C flag from the unsigned overflow / borrow of the low
half; `Adc`/`Sbc` read that C flag while computing the high half. Encoder
confirms these are *real* ARM instructions, not pseudo-ops
(`arm_encoder.rs:80–114`).

## 2. Bitwise (two parallel ops on lo/hi)

| WASM op | Rust ArmOp sequence | Source |
|---------|---------------------|--------|
| `I64And` | `And R0,R0,R2; And R1,R1,R3` | `instruction_selector.rs:1481–1493` |
| `I64Or`  | `Orr R0,R0,R2; Orr R1,R1,R3` | `instruction_selector.rs:1496–1508` |
| `I64Xor` | `Eor R0,R0,R2; Eor R1,R1,R3` | `instruction_selector.rs:1511–1523` |

No flag propagation needed; the lo and hi halves are independent.

## 3. Comparisons (pseudo-op `I64SetCond` / `I64SetCondZ`)

These compile to a *single* high-level `ArmOp::I64SetCond` (or `I64SetCondZ`
for the unary `I64Eqz`). The encoder expands these to a multi-instruction
sequence that does the dual-precision compare and materializes 0/1 into `R0`.

| WASM op | Rust ArmOp | Cond | Source |
|---------|------------|------|--------|
| `I64Eqz` | `I64SetCondZ {rd=R0, rn_lo=R0, rn_hi=R1}` | (unary) | `1527–1533` |
| `I64Eq`  | `I64SetCond {rd=R0, R0:R1, R2:R3, EQ}` | EQ | `1535–1544` |
| `I64Ne`  | `I64SetCond ... NE` | NE | `1546–1555` |
| `I64LtS` | `I64SetCond ... LT` | LT | `1557–1566` |
| `I64LtU` | `I64SetCond ... LO` | LO | `1568–1577` |
| `I64LeS` | `I64SetCond ... LE` | LE | `1579–1588` |
| `I64LeU` | `I64SetCond ... LS` | LS | `1590–1599` |
| `I64GtS` | `I64SetCond ... GT` | GT | `1601–1610` |
| `I64GtU` | `I64SetCond ... HI` | HI | `1612–1621` |
| `I64GeS` | `I64SetCond ... GE` | GE | `1623–1632` |
| `I64GeU` | `I64SetCond ... HS` | HS | `1634–1643` |

Because these are high-level pseudo-ops in Rust, the Coq model treats them as
opaque ARM pseudo-instructions with axiomatized result semantics — this is
exactly how VFP is modeled (`ArmSemantics.v` `f32_*_bits` axioms). See PR body
for the four axioms introduced.

## 4. Multiply (pseudo-op `I64Mul`)

| WASM op | Rust ArmOp | Source |
|---------|------------|--------|
| `I64Mul` | `I64Mul {rd_lo=R0, rd_hi=R1, rn_lo=R0, rn_hi=R1, rm_lo=R2, rm_hi=R3}` | `1646–1655` |

The encoder expands this to a UMULL + MLA cross-product sequence (line
comment at `instruction_selector.rs:1645`). Modeled as an axiomatized
high-level pseudo-op in Coq.

## 5. Shifts/Rotates (pseudo-ops)

| WASM op | Rust ArmOp | Source |
|---------|------------|--------|
| `I64Shl`  | `I64Shl  {rd_lo=R0, rd_hi=R1, rn_lo=R0, rn_hi=R1, rm_lo=R2, rm_hi=R3}` | `1658–1667` |
| `I64ShrU` | `I64ShrU {...}` | `1669–1678` |
| `I64ShrS` | `I64ShrS {...}` | `1680–1689` |
| `I64Rotl` | `I64Rotl {rdlo=R0, rdhi=R1, rnlo=R0, rnhi=R1, shift=R2}` | `1691–1699` |
| `I64Rotr` | `I64Rotr {rdlo=R0, rdhi=R1, rnlo=R0, rnhi=R1, shift=R2}` | `1701–1709` |

Note: rotates take only `R2` as the shift amount (the WASM rotate count is an
i64, but only the low 6 bits are significant; the high half of the count is
discarded by `I64.rotr`/`I64.rotl` modulo 64).

All five are high-level pseudo-ops; encoder expands them to multi-instruction
funnel shifts. Modeled as axiomatized in Coq.

## 6. Bit manipulation (pseudo-ops)

| WASM op | Rust ArmOp | Source |
|---------|------------|--------|
| `I64Clz`    | `I64Clz    {rd=R0, rnlo=R0, rnhi=R1}` | `1712–1718` |
| `I64Ctz`    | `I64Ctz    {rd=R0, rnlo=R0, rnhi=R1}` | `1720–1726` |
| `I64Popcnt` | `I64Popcnt {rd=R0, rnlo=R0, rnhi=R1}` | `1728–1734` |

All three produce a 32-bit count in `R0` (popcnt of an i64 is at most 64; clz
and ctz of an i64 are at most 64; all fit in `R0`). Modeled as axiomatized in
Coq.

## 7. Division / Remainder (pseudo-ops)

| WASM op | Rust ArmOp | Source |
|---------|------------|--------|
| `I64DivS` | `I64DivS {rdlo=R0, rdhi=R1, rnlo=R0, rnhi=R1, rmlo=R2, rmhi=R3}` | `1737–1746` |
| `I64DivU` | `I64DivU {...}` | `1748–1757` |
| `I64RemS` | `I64RemS {...}` | `1759–1768` |
| `I64RemU` | `I64RemU {...}` | `1770–1779` |

These are high-level pseudo-ops that, in the encoder, expand to **software
helper calls** (the gale runtime provides `__aeabi_ldivmod`, `__aeabi_uldivmod`,
etc., on Cortex-M which has no native i64 div). Modeled as axiomatized in Coq
with `None` semantics on division by zero / signed overflow (same trap pattern
as the i32 division case in `ArmSemantics.v`).

## 8. Conversions (pseudo-ops; size convention changes)

| WASM op | Rust ArmOp | Source |
|---------|------------|--------|
| `I64Const(val)`    | `I64Const   {rdlo=R0, rdhi=R1, value}` | `1393–1399` |
| `I64ExtendI32S`    | `I64ExtendI32S {rdlo=R0, rdhi=R1, rn=R0}` | `1401–1407` |
| `I64ExtendI32U`    | `I64ExtendI32U {rdlo=R0, rdhi=R1, rn=R0}` | `1409–1415` |
| `I32WrapI64`       | `I32WrapI64 {rd=R0, rnlo=R0}` — keeps R0 (low), drops R1 (high) | `1417–1423` |
| `I64Extend8S`      | `I64Extend8S  {rdlo=R0, rdhi=R1, rnlo=R0}` | `1425–1431` |
| `I64Extend16S`     | `I64Extend16S {rdlo=R0, rdhi=R1, rnlo=R0}` | `1433–1439` |
| `I64Extend32S`     | `I64Extend32S {rdlo=R0, rdhi=R1, rnlo=R0}` | `1441–1447` |

The previous `Compilation.v` modeled `I32WrapI64` and the `I64ExtendI32{S,U}` as
**empty programs** (`[]`). That's silently wrong: `I64ExtendI32S` must
sign-extend `R0` into `R1`, and `I64ExtendI32U` must zero `R1`. `I32WrapI64`
*can* be a no-op (the low half is already in `R0`) but the high register `R1`
becomes undefined / abandoned. We model these explicitly as pseudo-ops.

Also: previous `Compilation.v` modeled `I64Const` as a single MOVW into `R0`,
truncating to the low 16 bits. The Rust compiler uses a full
`I64Const` pseudo-op that loads both halves.

## 9. Memory (8-byte, bounds-checked)

| WASM op | Rust dispatch | Source |
|---------|---------------|--------|
| `I64Load`  | `self.generate_i64_load_with_bounds_check(rn, offset)` | `1782` |
| `I64Store` | `self.generate_i64_store_with_bounds_check(rn, offset)` | `1784–1786` |

The bounds-check helpers emit a multi-instruction sequence (bounds check + two
LDR/STR for low and high halves). The previous `Compilation.v` modeled both as
a single LDR/STR of the low half only. Modeled as pseudo-ops in this PR.

---

## Summary of new Coq pseudo-ops introduced

To stay parallel with the Rust ArmOp design, this PR adds the following to
`coq/Synth/ARM/ArmInstructions.v`:

| Coq pseudo-op | Mirrors Rust ArmOp | Lo/hi convention |
|---------------|--------------------|-----------------|
| `ADDS`, `ADC` | `Adds`, `Adc`         | real ARM instr — sets/reads C |
| `SUBS`, `SBC` | `Subs`, `Sbc`         | real ARM instr — sets/reads C |
| `I64MulPseudo`    | `I64Mul`     | rdlo/rdhi from rnlo:rnhi * rmlo:rmhi |
| `I64ShlPseudo` / `I64ShrUPseudo` / `I64ShrSPseudo` | `I64Shl/ShrU/ShrS` | dual-reg result |
| `I64RotlPseudo` / `I64RotrPseudo`   | `I64Rotl/Rotr` | shift amount in single reg |
| `I64ClzPseudo` / `I64CtzPseudo` / `I64PopcntPseudo`    | `I64Clz/Ctz/Popcnt` | rd=R0, reads (rnlo, rnhi) |
| `I64SetCond` / `I64SetCondZ`        | `I64SetCond`/`SetCondZ` | rd=R0 (0/1) |
| `I64DivSPseudo` / `I64DivUPseudo` / `I64RemSPseudo` / `I64RemUPseudo` | `I64{Div,Rem}{S,U}` | trap semantics via `None` |
| `I64ConstPseudo`        | `I64Const`        | loads both halves |
| `I64ExtendI32SPseudo` / `I64ExtendI32UPseudo` | `I64ExtendI32{S,U}` | sign/zero-extend lo into hi |
| `I32WrapI64Pseudo`      | `I32WrapI64`      | keeps lo, drops hi |
| `I64LoadPseudo` / `I64StorePseudo` | dispatch helpers | 8-byte memory |

Each pseudo-op is given an axiomatized semantics in `ArmSemantics.v` that
matches the WASM operation it implements (e.g., `I64MulPseudo` reads
`(rnlo, rnhi)` and `(rmlo, rmhi)`, computes `I64.mul`, and writes the result
into `(rdlo, rdhi)`). This parallels how VFP operations are axiomatized.

The justification: the Rust compiler **also** treats these as opaque ArmOp
variants whose encoded behavior is defined by the encoder, not by any
single ARM instruction. The Coq model now faithfully reflects that.
