#![no_std]
// Compile the original supported source functions, including the callee and
// argument effects. Only the known-refused wide function has a cfg exclusion.
include!("subject.rs");

#[unsafe(no_mangle)]
pub extern "C" fn thin_same_home() -> u32 { same_home() as u32 }
#[unsafe(no_mangle)]
pub extern "C" fn thin_different_homes() -> u32 { different_homes() as u32 }
#[unsafe(no_mangle)]
pub extern "C" fn thin_effect_order() -> u32 { effect_order() }
#[unsafe(no_mangle)]
pub extern "C" fn thin_unrelated_eq() -> u32 { unrelated_eq() as u32 }
