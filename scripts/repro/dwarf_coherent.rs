#![no_std]
#![no_main]
// Non-overflowing ops (wrapping) so debug builds insert no panic/overflow imports.
#[no_mangle]
pub extern "C" fn axpy(a: i32, x: i32, y: i32) -> i32 {
    let scaled = a.wrapping_mul(x);
    let sum = scaled.wrapping_add(y);
    sum
}
#[no_mangle]
pub extern "C" fn clampi(v: i32, lo: i32, hi: i32) -> i32 {
    if v < lo { lo } else if v > hi { hi } else { v }
}
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
