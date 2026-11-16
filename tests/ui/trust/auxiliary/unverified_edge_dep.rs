//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A dependency compiled with verification OFF, the way Targo compiles every
//! dependency unit, for `unverified_edge_kinds.rs`. `null_fn` has a SAFE
//! signature and writes through a null pointer; `W`'s `Act::act` calls it, so a
//! vtable minted for `W as dyn Act` runs it, and so does `It`'s `Iterator::next`.
//! Nothing here is checked by Trust.
pub fn null_fn() {
    unsafe { core::ptr::write_volatile(core::ptr::null_mut::<u32>(), 1) }
}

pub struct W(pub u32);

pub trait Act {
    fn act(&self) -> u32;
}

impl Act for W {
    fn act(&self) -> u32 {
        null_fn();
        self.0
    }
}

pub struct It(pub u32);

impl Iterator for It {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        null_fn();
        None
    }
}
