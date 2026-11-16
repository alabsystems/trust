#![feature(rustc_attrs)]
#![crate_type = "lib"]

#[rustc_abi(debug)]
pub extern "C" fn c_u8(x: u8) -> u8 { x }
#[rustc_abi(debug)]
pub fn rust_u8(x: u8) -> u8 { x }
#[rustc_abi(debug)]
pub extern "C" fn c_i8(x: i8) -> i8 { x }
#[rustc_abi(debug)]
pub extern "C" fn c_u16(x: u16) -> u16 { x }
