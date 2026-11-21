//! The embedded probe set: the one source both the kiln probe oracle
//! (`tests/kiln_probe_oracle.rs`) and the target record (`target-record`)
//! execute, so the record never runs a second, hand-copied list.

/// Every probe is call-free (no relocations), memory-free, float-free, takes
/// only i32 params and returns at most one value. i64 PARAMS are left out
/// because synth's RV32 backend declines exports that read one (#952 skip), so
/// they would not compile on the rv32imac leg; the ILP32 pair layout is
/// covered by the `aapcs_aligns_i64_pairs` unit test only, never by real code.
pub const PROBES_WAT: &str = r#"
(module
  (func (export "add") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)
  (func (export "sub") (param i32 i32) (result i32) local.get 0 local.get 1 i32.sub)
  (func (export "mul") (param i32 i32) (result i32) local.get 0 local.get 1 i32.mul)
  (func (export "and_or_xor") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.and local.get 0 local.get 1 i32.or i32.xor)
  (func (export "shr_s") (param i32 i32) (result i32) local.get 0 local.get 1 i32.shr_s)
  (func (export "shr_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.shr_u)
  (func (export "ne") (param i32 i32) (result i32) local.get 0 local.get 1 i32.ne)
  (func (export "lt_s") (param i32 i32) (result i32) local.get 0 local.get 1 i32.lt_s)
  (func (export "ge_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.ge_u)
  (func (export "eqz") (param i32 i32) (result i32) local.get 0 i32.eqz)
  (func (export "select_max") (param i32 i32) (result i32)
    local.get 0 local.get 1 local.get 0 local.get 1 i32.gt_s select)
  (func (export "if_else") (param i32 i32) (result i32)
    local.get 0 if (result i32) local.get 1 i32.const 3 i32.mul
    else local.get 1 i32.const 5 i32.sub end)
  (func (export "loop_sum") (param i32 i32) (result i32) (local i32)
    local.get 0 i32.const 15 i32.and local.set 0
    block loop
      local.get 0 i32.eqz br_if 1
      local.get 2 local.get 0 i32.add local.get 1 i32.xor local.set 2
      local.get 0 i32.const 1 i32.sub local.set 0
      br 0
    end end
    local.get 2)
  (func (export "br_table") (param i32 i32) (result i32)
    block block block
      local.get 0 br_table 0 1 2
    end local.get 1 i32.const 100 i32.add return
    end local.get 1 i32.const 200 i32.add return
    end local.get 1 i32.const 300 i32.add)
  (func (export "i64_mul_wide") (param i32 i32) (result i64)
    local.get 0 i64.extend_i32_u local.get 1 i64.extend_i32_u i64.mul)
  (func (export "i64_shl") (param i32 i32) (result i64)
    local.get 0 i64.extend_i32_s local.get 1 i64.extend_i32_u i64.shl)
  (func (export "i64_add_sub") (param i32 i32) (result i64)
    local.get 0 i64.extend_i32_u i64.const 32 i64.shl local.get 1 i64.extend_i32_s i64.add
    i64.const 0x123456789 i64.sub)
  (func (export "i64_lt_s") (param i32 i32) (result i32)
    local.get 0 i64.extend_i32_s i64.const 32 i64.shl
    local.get 1 i64.extend_i32_s i64.const 32 i64.shl i64.lt_s)
  (func (export "div_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.div_u)
  (func (export "rem_u") (param i32 i32) (result i32) local.get 0 local.get 1 i32.rem_u)
  (func (export "trap_if") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.eq if unreachable end local.get 0 local.get 1 i32.sub)
  (func (export "spin") (param i32 i32) (result i32) loop br 0 end i32.const 0)
)
"#;

/// The probes required to agree on every vector. `spin` is the budget probe
/// and is judged separately.
pub const AGREE_PROBES: &[&str] = &[
    "add",
    "sub",
    "mul",
    "and_or_xor",
    "shr_s",
    "shr_u",
    "ne",
    "lt_s",
    "ge_u",
    "eqz",
    "select_max",
    "if_else",
    "loop_sum",
    "br_table",
    "i64_mul_wide",
    "i64_shl",
    "i64_add_sub",
    "i64_lt_s",
    "div_u",
    "rem_u",
    "trap_if",
];

pub const VECTORS: &[u32] = &[
    0,
    1,
    2,
    7,
    31,
    32,
    0x7F,
    0x8000,
    0x7FFF_FFFF,
    0x8000_0000,
    0xFFFF_FFFF,
    0xDEAD_BEEF,
];
