//@ trust-ladder: verifies
//@ trust-ladder-crate-type: bin
//! THE CALLER-SIDE ROW, CLOSED 2026-09-19. `<S as Debug>::fmt` here is
//! established panic-free IN THIS COMPILATION — `TRUST_PF_REG_TRACE=1` prints
//! `established=true nrows=0` for it, BEFORE the caller is verified — and the
//! caller was refused anyway, because the gate tested whether the formatted TYPE
//! is a sysroot type and never whether the impl's verdict exists.
//! `fmt_target_is_verified_panic_free` now asks, through the SHARED bar
//! `dyn_target_is_verified_panic_free`. This row verifies only while pf2
//! (panicking impl), pf4 (type parameter), pf5 (one unvouched value among
//! several) and xcrate/user_fmt_dep (a dependency's impl) stay red.
use core::fmt;
pub struct S;
impl fmt::Debug for S {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result { Ok(()) }
}
fn main() { println!("{:?}", S); }
