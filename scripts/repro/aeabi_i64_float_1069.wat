(module
  (func (export "i64u_to_f32") (param i64) (result f32) local.get 0 f32.convert_i64_u)
  (func (export "i64s_to_f32") (param i64) (result f32) local.get 0 f32.convert_i64_s)
  (func (export "f32_to_i64s") (param f32) (result i64) local.get 0 i64.trunc_f32_s)
  (func (export "f32_to_i64u") (param f32) (result i64) local.get 0 i64.trunc_f32_u)
  (func (export "f32_to_i64s_sat") (param f32) (result i64) local.get 0 i64.trunc_sat_f32_s)
  (func (export "f32_to_i64u_sat") (param f32) (result i64) local.get 0 i64.trunc_sat_f32_u))
