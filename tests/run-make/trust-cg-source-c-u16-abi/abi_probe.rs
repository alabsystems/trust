#![feature(rustc_attrs)]
#![crate_type = "lib"]
#[rustc_abi(debug)]
pub extern "C" fn c_u16(x: u16) -> u16 { x }
#[rustc_abi(debug)]
pub fn rust_u16(x: u16) -> u16 { x }
#[rustc_abi(debug)]
pub extern "C" fn c_i16(x: i16) -> i16 { x }
