#![allow(dead_code)]

static mut STATE: u64 = 7;

#[cfg(not(pure))]
#[inline(never)]
fn read(_a: u64) -> u64 {
    unsafe { STATE }
}

#[cfg(pure)]
#[inline(never)]
fn read(a: u64) -> u64 {
    let local = a.wrapping_add(7);
    let reference = &local;
    let reborrow = &*reference;
    *reborrow
}

clean {
    def applyRead (a : UInt64) : UInt64 := read a
}

// The initializer is itself the owner of the reference, even without a use of
// this static from main. Do not infer this demand from the static's FnPtr type.
#[cfg(static_address)]
static FUNCTION: fn(u64) -> u64 = applyRead;

#[cfg(global_symbol)]
core::arch::global_asm!("/* {callee} */", callee = sym applyRead);

fn main() {
    #[cfg(inline_symbol)]
    unsafe {
        core::arch::asm!(
            "/* {callee} */",
            callee = sym applyRead,
            options(nomem, nostack, preserves_flags),
        );
    }
}
