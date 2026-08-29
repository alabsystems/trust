//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! Falsification pair of `e9_definitional_call_discharge`: (1) a call-bearing
//! clause WITHOUT a citation and WITHOUT an automatic proof stays a
//! fail-closed build error; (2) a citation whose theorem does not prove the
//! clause fails closed.
//!
//! Case (2) is unchanged and still uses `ident`: a CITED clause is never
//! helper-expanded, precisely so the citation lane keeps its kernel authority
//! rather than being quietly rerouted to the solver.

pub fn ident(x: u64) -> u64 { x }

// A helper the automatic lane cannot inline: its body has a STATEMENT, so
// `inline_helper_call_reasoned` refuses it and the clause stays outside the
// solver fragment. `ident` itself is no longer usable here — a call to a
// TRANSPARENT helper in an UNCITED clause is now expanded and discharged
// automatically (see contract_inlined_call_ensures_proves), which is the
// intended capability and would make this case pass for the right reason. The
// property under test is the OTHER one: a call-bearing clause with NO proof
// available must stay a fail-closed build error, and that needs a callee the
// automatic lane genuinely cannot see through.
pub fn ident_opaque(x: u64) -> u64 { let y = x; y }

pub fn no_citation(x: u64) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete for
    //~| ERROR Trust strict verification failed for
    ensures ident_opaque(x) >= ident_opaque(x)
{ x }

clean {
    theorem triv : True := True.intro
}

pub fn wrong_theorem(x: u64) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete for
    //~| ERROR Trust strict verification failed for
    ensures ident(x) >= ident(x) by triv
    //~^ ERROR citation `triv`
{ x }

fn main() {}
