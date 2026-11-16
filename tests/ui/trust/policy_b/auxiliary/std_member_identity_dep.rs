//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency compiled with verification OFF, the way Targo compiles every
//! dependency unit: nothing here carries a Trust verdict. `T::clone` panics on
//! `T(7)`, so a caller that reaches it through an AUTHENTIC std body instantiated
//! at `dep::T` — `<Vec<dep::T> as Clone>::clone` — can be shown to reach
//! unverified code (`std_member_identity_not_widened.rs`).
pub struct T(pub u32);

impl Clone for T {
    fn clone(&self) -> T {
        if self.0 == 7 {
            panic!("DEP CLONE PANIC (unverified crate)")
        }
        T(self.0)
    }
}
