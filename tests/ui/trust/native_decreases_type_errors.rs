//@ check-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! Native E5 elaboration is an always-on frontend gate. These clauses are
//! rejected while Trust verification is disabled: an opaque parser-island
//! measure cannot defer syntax, scope, or sort errors to an optional verifier.

fn boolean_measure(flag: bool)
    decreases flag //~ ERROR invalid `decreases` clause: ill-typed source contract: decreases clause must have sort Int
{
}

fn unknown_measure(n: u32)
    decreases ghost + n //~ ERROR invalid `decreases` clause: source-contract variable `ghost` is not in scope
{
}

fn malformed_measure(n: u32)
    decreases n + //~ ERROR invalid `decreases` clause:
{
}

fn scalar_collection_accessor(n: u32)
    decreases n.len() //~ ERROR invalid `decreases` clause: ill-typed source contract: collection accessor `len` requires an Array base
{
}

fn boolean_slice_element(flags: &[bool])
    decreases flags[0] //~ ERROR invalid `decreases` clause: ill-typed source contract: decreases clause must have sort Int, found Bool
{
}

fn raw_pointer_implicit_collection(p: *const [u32])
    decreases p.len() //~ ERROR invalid `decreases` clause: source-contract variable `p` is not in scope
{
}

struct State {
    rank: u32,
}

fn unknown_datatype_field(state: State)
    decreases state.nope //~ ERROR invalid `decreases` clause: ill-typed source contract: ordinary field projection `nope` is unsupported without exact field layout
{
    let _ = state.rank;
}

fn main() {}
