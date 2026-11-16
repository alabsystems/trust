//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A dependency compiled with verification OFF, the way Targo compiles every
//! dependency unit, for `unverified_edge_surface_and_consts.rs`. `null_fn` has a
//! SAFE signature and writes through a null pointer; `D`'s destructor and `W`'s
//! `Act::act` call it, and `DEP_FP` / `DEP_DYN` are a function pointer and a
//! trait object minted by CONST EVALUATION, with no cast in any body of the crate
//! that uses them. Nothing here is checked by Trust.
pub fn null_fn() {
    unsafe { core::ptr::write_volatile(core::ptr::null_mut::<u32>(), 1) }
}

/// Its drop runs `null_fn`.
pub struct D(pub u32);

impl Drop for D {
    fn drop(&mut self) {
        null_fn();
    }
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

pub const DEP_FP: fn() = null_fn;
pub static DEP_DYN: &(dyn Act + Sync) = &W(1);
