// Split from native_clause_citation_grammar_errors.rs: contract-clause citation
// parse errors abort the whole-crate parse at the FIRST error, so each grammar
// case needs its own file for its annotation to be satisfiable.
//@ compile-flags: -Z trust-verify=off

fn trailing_dot(x: u32) -> u32
    ensures result == x by Lemma.
    //~^ ERROR expected a name segment after `.` in the contract clause citation
{
    x
}

fn main() {}
