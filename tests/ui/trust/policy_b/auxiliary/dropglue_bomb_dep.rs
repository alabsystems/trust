//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency compiled with verification OFF, the way Targo compiles every
//! dependency unit. `Bomb` has a user `Drop` impl that PANICS. Its `Drop::drop`
//! DefId lives in this crate (`dropglue_bomb_dep`), not std/core/alloc, so its
//! drop-glue panic-freedom is unproven. It exists so the caller fixture can prove
//! that a dependency's masked DROP GLUE stays fatal under policy B even when a
//! `println!` makes the std print backend the folded row's representative.
pub struct Bomb(pub i32);
impl Drop for Bomb {
    fn drop(&mut self) {
        panic!("BOMB dropped: {}", self.0);
    }
}
