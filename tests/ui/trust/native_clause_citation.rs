//@ compile-flags: -Z trust-verify=off
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! E9 `by <thm>` citation SURFACE (two-language design): the citation parses
//! as part of the clause grammar and carries a canonical dotted identity plus
//! its authored source span. Verification is off, but authored citations are
//! still validated by the Clean kernel. This verification-off fixture exercises
//! only the diagnostic sweep: a result-free exact ensures match reports a
//! kernel DISCHARGE of the postcondition statement (still no VC row authority),
//! while loop-clause matches stay advisory; only the separate bounded in-walk
//! lane (verification on) rechecks an exact ensures match and seals authority.

//~vv NOTE Clean island kernel-checked: 3 declaration(s) registered
clean {
    namespace Crate.lemmas
    theorem scale_bound : 0 = 0 := rfl
    theorem dec : 0 = 0 := rfl
    theorem acc_bound : 0 = 0 := rfl
    end Crate.lemmas
}

pub fn safe_sub(x: u64, y: u64) -> u64
    requires x >= y
    ensures 0 == 0 by Crate /* identity ignores this */ . lemmas . scale_bound
    //~^ NOTE citation `Crate.lemmas.scale_bound` kernel-discharges this postcondition statement: the cited theorem proves the clause with `result` bound to the imported definition of `safe_sub`, with a clean certification audit
{
    x - y
}

// Both depth-zero and nested `by` identifiers remain predicate vocabulary.
// In particular the final RHS `by` must not be stolen as a bare citation.
pub fn by_is_predicate(by: u32) -> u32
    requires by == by
    ensures foo(by) == by
{
    by
}

// Dotted citation paths and loop-clause citations parse too.
pub fn count(mut n: u32) -> u32 {
    let mut acc = 0u32;
    while n > 0
        decreases n
        invariant 0 == 0 by Crate /* kept */ . lemmas . acc_bound
        //~^ NOTE citation `Crate.lemmas.acc_bound` has a Clean-kernel statement match
    {
        acc = acc.saturating_add(1);
        n -= 1;
    }
    acc
}

// `by` stays an ordinary identifier everywhere else.
#[allow(dead_code)]
fn by(x: u32) -> u32 {
    x
}

fn main() {
    let mut _b = 100u64;
    let _ = safe_sub(9, 4);
    let _ = by_is_predicate(9);
    let _ = count(3);
    let _ = by(1);
}
