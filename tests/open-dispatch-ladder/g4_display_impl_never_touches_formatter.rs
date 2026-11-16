//@ trust-ladder: verifies
//! A user `Display` impl is NOT refused as such. This one verifies because its
//! body never reaches the `Formatter`'s `dyn Write` field.
use core::fmt;
pub struct S;
impl fmt::Display for S {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result { Ok(()) }
}
