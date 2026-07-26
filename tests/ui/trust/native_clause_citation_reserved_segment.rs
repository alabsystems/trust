// Split from native_clause_citation_grammar_errors.rs (one parse-error case per
// file; parse aborts at the first citation error).
//@ compile-flags: -Z trust-verify=off

fn reserved_segment(x: u32) -> u32
    ensures result == x by Lemma.fn
    //~^ ERROR expected a name segment after `.` in the contract clause citation
{
    x
}

fn main() {}
