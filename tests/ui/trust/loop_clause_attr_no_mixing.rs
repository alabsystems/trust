//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-verify=on
//! Trust: one loop, one clause surface.
//!
//! The attribute transport and the native clause position desugar into the
//! SAME `ast::LoopContract`. Accepting both on one loop would raise two
//! questions the author never answered — what the merged clause ORDER is, and
//! which surface owns the "at most one `decreases`" rule — and would give the
//! `decreases` uniqueness check two places to be wrong.
//!
//! It also cannot arise in genuinely stock-compatible source: a file containing
//! the native grammar does not parse on stock rustc at all, so a crate that
//! needs the transport has no reason to also write the native form.

pub fn both_surfaces(limit: u32) -> u32 {
    let mut n = limit;
    #[cfg_attr(trust_verify, trust::decreases(n))]
    //~^ ERROR this loop has clauses on BOTH the attribute and the native surface
    loop invariant n <= limit {
        if n == 0 {
            break;
        }
        n -= 1;
    }
    n
}

fn main() {}
