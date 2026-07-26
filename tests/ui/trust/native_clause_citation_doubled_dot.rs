// Split from native_clause_citation_grammar_errors.rs (one parse-error case per
// file). A doubled dot lexes as one `..` DotDot token; the citation-suffix
// probe and parse loop must claim malformed dot runs and fail closed rather
// than silently swallowing the citation into the predicate payload
// (design §1.2-6).
//@ compile-flags: -Z trust-verify=off

fn doubled_dot(x: u32) -> u32
    ensures result == x by Lemma..part
    //~^ ERROR expected a name segment after `.` in the contract clause citation
{
    x
}

fn main() {}
