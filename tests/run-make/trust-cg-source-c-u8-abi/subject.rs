#![no_std]

#[unsafe(no_mangle)]
pub extern "C" fn trust_c_u8_id(x: u8) -> u8 { x }
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn trust_c_u8_not(x: u8) -> u8 { !x }
#[unsafe(no_mangle)]
pub extern "C" fn trust_c_u8_xor(x: u8) -> u8 { x ^ 0xa5 }
#[unsafe(no_mangle)]
pub extern "C" fn trust_c_u8_constant(_: u8) -> u8 { 0xd3 }
#[unsafe(no_mangle)]
pub extern "C" fn trust_c_u8_trunc(x: u32) -> u8 { x as u8 }

#[unsafe(no_mangle)]
pub extern "C" fn trust_c_u8_rust_typed_not(x: u8) -> u8 { trust_c_u8_not(x) }
