//@ trust-ladder: verifies
//! THE PIVOT. `fmt::Write::write_str` at a CONCRETE receiver verifies. Compare
//! h2, which is the identical call through `&mut dyn Write` and is refused.
use core::fmt::Write;
pub fn f(buf: &mut String) -> core::fmt::Result { buf.write_str("S") }
