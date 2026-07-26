//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust: regression for symbolic assoc-const lowering (totality Batch C).
//! A generic body reading a param-dependent scalar associated const
//! (`B::ON`, typenum's whole `Bit`/`Unsigned` vocabulary) used to fail
//! closed with `NamedConst(eval failed)` — the value genuinely cannot be
//! evaluated before monomorphization. It now lowers SYMBOLICALLY: each
//! distinct `(const, args)` pair becomes one body-scoped EXTERN IMMUTABLE
//! global (trust-ir's "declared, value unknown" vocabulary), every read is
//! `GlobalAddr` + `Load` of that one global (read-read equality is
//! structural), and the body is marked `symbolic` — lowered for coverage,
//! excluded from the interpretation differential (a value-less load must
//! never be interpreted) and from the crate-module splice (the executable
//! module must not contain value-less globals). Both exclusions are
//! CHECKED at their seams; the batch validation asserts zero `symconst`
//! globals in the spliced module.
//!
//! Under `-Z trust-ir-lower` this must compile cleanly (check-pass): the
//! producer lane never aborts a compilation that succeeds without it.
pub trait Flag {
    const ON: bool;
}

pub trait Count {
    const N: u32;
}

// One read — the minimal symbolic body.
pub fn read_one<B: Flag>() -> bool {
    B::ON
}

// Two reads of the SAME (const, args) — must dedup to one global.
pub fn read_twice<B: Flag>() -> bool {
    B::ON & B::ON
}

// Two DISTINCT consts — two globals, still one symbolic body.
pub fn read_mixed<B: Flag, C: Count>() -> u32 {
    if B::ON { C::N } else { 0 }
}

// Param-TYPED consts stay fail-closed (the scalar gate, not this arm):
// nothing here reads one, and the concrete world is untouched:
pub struct Yes;
impl Flag for Yes {
    const ON: bool = true;
}

pub fn concrete() -> bool {
    // Fully-monomorphic read — the eager path, NOT symbolic.
    <Yes as Flag>::ON
}

fn main() {}
