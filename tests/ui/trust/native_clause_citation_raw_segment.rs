// Split from native_clause_citation_grammar_errors.rs (one parse-error case per
// file; parse aborts at the first citation error).
//@ compile-flags: -Z trust-verify=off

fn raw_segment(x: u32) -> u32
    ensures result == x by r#lemma
    //~^ ERROR expected a theorem name after `by` in the contract clause citation
{
    x
}

fn main() {}
