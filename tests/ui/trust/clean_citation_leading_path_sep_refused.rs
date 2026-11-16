//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE

//! **Ruling R1, the leading-separator half: `by ::thm` is the same spelling
//! mistake as `by Crate::thm`, and gets the same named refusal.**
//!
//! The suffix probe that decides whether `by …` is a citation at all now
//! claims `::` (ruling R1), so `by ::local_thm` reaches the citation parser
//! instead of being swallowed into the predicate payload. Without the check
//! this fixture pins, it then fell out as the generic *"expected a theorem
//! name after `by` in the contract clause citation"* — a message that describes
//! the parse state rather than the rule, for a mistake whose rule is exactly
//! the one `clean_citation_rust_path_spelling_refused.rs` states. A refusal
//! whose wording changes with the position of the separator teaches R1 twice.
//!
//! It is a separate file because the parser does not recover past a rejected
//! contract clause (MEASURED 2026-09-19: one diagnostic, then `aborting due to
//! 1 previous error`), so a second clause in the sibling fixture would never be
//! reached.

clean {
    theorem local_thm : 0 = 0 := rfl
}

pub fn g(x: u64) -> u64
    ensures 0 == 0 by ::local_thm
    //~^ ERROR a contract clause citation is spelled with `.`, not `::`
{
    x
}

fn main() {}
