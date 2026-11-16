//@ trust-ladder: refuses
//@ trust-ladder-crate-type: bin
//! GUARD RAIL. The impl panics, so it fails its OWN verification and can never
//! be established; the caller must stay refused however the caller-side gate is
//! rewired.
use core::fmt;
pub struct S;
impl fmt::Debug for S {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result { panic!("boom") }
}
fn main() { println!("{:?}", S); }
