//@ trust-ladder: verifies
//! `Formatter::width` reads the options field, never the writer. Pairs with
//! f3: the refusal is the writer, not the `Formatter`.
use core::fmt;
pub struct S;
impl fmt::Display for S {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { let _ = f.width(); Ok(()) }
}
