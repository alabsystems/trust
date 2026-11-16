//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE

//! **RULING R1 (decided 2026-09-19): a citation is spelled `krate.theorem`,
//! never `krate::theorem`.**
//!
//! The citation grammar has always taken a dotted CLEAN name — the segments
//! of a Clean declaration's own name. What was undecided is the spelling for a
//! DEPENDENCY's theorem, and the Rust path separator was a live candidate. It
//! is refused, and refused by name rather than by the generic "expected `.` or
//! the end of the contract clause citation" the parser used to reach: `::` is
//! what a Rust programmer reaches for first, and the reason it is not accepted
//! is a decision about the surface, not a parse accident.
//!
//! The parser's suffix probe claims `::` for exactly this diagnostic. Before
//! that, `by Crate::thm` was not recognised as a citation at all — and
//! MEASURED (2026-09-19, validated pack `ddafc55ba72`) that was worse than a
//! late refusal: under `-Ztrust-verify=off` this exact file compiled with **no
//! diagnostic at all**, silently dropping the citation its author wrote; under
//! `-Ztrust-verify=on` it fail-closed as *"unsupported contract predicate
//! expression `0 == 0 by Crate::local_thm`"*, naming the whole clause and
//! never the spelling. This fixture is the regression test for a SILENT MISS,
//! not for a worse message.
//!
//! MEASURED 2026-09-19 (integration): this fixture produces exactly ONE
//! diagnostic and then `aborting due to 1 previous error` — the parser does not
//! recover past a rejected contract clause, so there is no cascade to hide and
//! the `dont-require-annotations: ERROR` the lane added as a precaution has
//! been REMOVED. That non-recovery is also why the LEADING-`::` case lives in
//! its own fixture (`clean_citation_leading_path_sep_refused.rs`): a second
//! clause in this file would never be reached.

clean {
    theorem local_thm : 0 = 0 := rfl
}

pub fn f(x: u64) -> u64
    ensures 0 == 0 by Crate::local_thm
    //~^ ERROR a contract clause citation is spelled with `.`, not `::`
{
    x
}

fn main() {}
