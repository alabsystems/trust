#![feature(rustc_attrs)]
#![crate_type="lib"]
#[rustc_abi(debug)]
pub extern "C" fn c_i8(x:i8)->i8 {x}
#[rustc_abi(debug)]
pub extern "C" fn c_i16(x:i16)->i16 {x}
#[rustc_abi(debug)]
pub fn rust_i8(x:i8)->i8 {x}
#[rustc_abi(debug)]
pub fn rust_i16(x:i16)->i16 {x}
#[rustc_abi(debug)]
pub extern "C" fn c_u32(x:u32)->u32 {x}
