#![no_std]
#[unsafe(no_mangle)]
pub extern "C" fn trust_c_i8_id(x:i8)->i8 {x}
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn trust_c_i8_not(x:i8)->i8 {!x}
#[unsafe(no_mangle)]
pub extern "C" fn trust_c_i8_tail(x:i8)->i8 {trust_c_i8_not(x)}
#[unsafe(no_mangle)]
pub extern "C" fn trust_c_i16_id(x:i16)->i16 {x}
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn trust_c_i16_not(x:i16)->i16 {!x}
#[unsafe(no_mangle)]
pub extern "C" fn trust_c_i16_tail(x:i16)->i16 {trust_c_i16_not(x)}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn trust_c_i8_store(p:*mut u8,v:u64)->i8 {unsafe{*p=v as u8};-7}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn trust_c_i16_store(p:*mut u8,v:u64)->i16 {unsafe{*p=v as u8};-7}
