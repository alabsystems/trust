#![no_std]

#[unsafe(no_mangle)]
pub extern "C" fn trust_c_u16_id(x: u16) -> u16 { x }
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn trust_c_u16_not(x: u16) -> u16 { !x }
#[unsafe(no_mangle)]
pub extern "C" fn trust_c_u16_xor(x: u16) -> u16 { x ^ 0xa5c3 }
#[unsafe(no_mangle)]
pub extern "C" fn trust_c_u16_constant(_: u16) -> u16 { 0x9e71 }
#[unsafe(no_mangle)]
pub extern "C" fn trust_c_u16_trunc(x: u32) -> u16 { x as u16 }

#[unsafe(no_mangle)]
pub extern "C" fn trust_c_u16_rust_typed_not(x: u16) -> u16 { trust_c_u16_not(x) }
