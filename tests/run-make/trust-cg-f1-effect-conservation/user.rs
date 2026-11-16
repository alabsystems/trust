//! Takes ownership of a `dep::Fd`; Rust drops it (running `Fd::drop`) on return. Before the
//! effect-conservation gate the trust-ir frontend COMPLETED this function (1/1) with the drop
//! gone, and the review's linked program printed `drops observed = 0 (1 = correct)`.
#[inline(never)]
pub fn consume(f: dep::Fd) -> i32 {
    f.0 & 0xff
}
