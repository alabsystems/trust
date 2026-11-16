// The subject bodies of `rmake.rs`: an empty `noreturn` asm that is reached
// unconditionally, one reached exactly on `x == 0`, and one behind a guard no
// `u32` satisfies. `rmake.rs` finds each asm by its source line: keep exactly one per
// body, in this order.

use std::arch::asm;

pub fn diverge() -> ! {
    unsafe { asm!("", options(noreturn)) }
}

pub fn guarded(x: u32) -> u32 {
    if x == 0 {
        unsafe { asm!("", options(noreturn)) }
    }
    x
}

pub fn dead(x: u32) -> u32 {
    if x < 1 && x > 5 {
        unsafe { asm!("", options(noreturn)) }
    }
    x
}
