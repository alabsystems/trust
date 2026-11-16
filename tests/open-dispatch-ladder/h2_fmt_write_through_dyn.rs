//@ trust-ladder: refuses
//@ trust-ladder-row: <dyn core::fmt::Write as core::fmt::Write>::write_str
//! THE PIVOT'S OTHER HALF. Byte-for-byte g2's call, through `&mut dyn Write`.
//! No `fmt` impl, no derive, no `Formatter`.
use core::fmt::Write;
pub fn f(w: &mut dyn Write) -> core::fmt::Result { w.write_str("S") }
