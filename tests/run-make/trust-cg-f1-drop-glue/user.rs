//! Drops a `dep::Fd`, whose destructor is the upstream crate's: its glue needs a body from
//! another crate (trust-ir in metadata, increment 6), so the drop does not resolve.
#[inline(never)]
pub fn consume(f: dep::Fd) -> i32 {
    f.0 & 0xff
}
