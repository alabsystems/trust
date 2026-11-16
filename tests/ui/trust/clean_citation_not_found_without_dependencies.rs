//@ compile-flags: -Z trust-verify=off

//! **The negative twin for the cross-crate citation notes: a crate with no
//! Clean proof material anywhere in its graph refuses exactly as it always
//! did.**
//!
//! `clean_citation_cross_crate_options.rs` pins that a `TheoremNotFound`
//! refusal now lists the crates that transported Clean islands. This fixture
//! pins the other half — that `cross_crate_citation_notes` returns `None`, and
//! the refusal is the bare one-line diagnostic, when nothing was transported.
//! It deliberately does NOT carry `dont-check-compiler-stderr`: the blessed
//! `.stderr` beside it is the assertion, because the ABSENCE of a note cannot
//! be pinned by an inline expectation comment — only by an exact output file.
//!
//! Without this, a change that listed crates unconditionally — or that started
//! reporting `core`/`std` — would pass every other fixture in this family.

clean {
    theorem local_thm : 0 = 0 := rfl
}

pub fn f(x: u64) -> u64
    ensures 0 == 0 by nowhere
    //~^ ERROR cited theorem `nowhere` is not registered in any Clean island or the prelude
{
    x
}

fn main() {}
