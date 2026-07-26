//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Awarnings
//@ check-fail
//@ dont-check-compiler-stderr
//! E6 compiler/session integration. The citation sweep must run only after the
//! whole-body MIR walk has populated `SessionFnFacets`, while every program
//! call remains outside the kernel fragment until definitional import lands.
//! These public facet findings are diagnostic only: even four positive findings
//! cannot discharge the citation or widen proof authority without a sealed,
//! item-bound kernel admission.

clean {
    theorem placeholder : 0 = 0 := rfl
}

// Scalar locals, whitelisted operations, no calls, no back-edges, no assert:
// the structural scan establishes all four facets.
fn min2(x: u8, y: u8) -> u8 {
    if x < y { x } else { y }
}

fn cite_fully_certified() -> u8
    ensures min2(1, 2) == 1 by placeholder
    //~^ ERROR citation `placeholder` failed the strict Clean statement/certification audit
{
    1
}

// Checked addition lowers through a scalar `(value, overflowed)` temporary and
// a reachable MIR Assert. It poisons structural NoPanic while leaving the
// other three facets established, and must retain the scanner reason.
fn checked_add_one(x: u8) -> u8 {
    x + 1
}

fn cite_asserting() -> u8
    ensures checked_add_one(1) == 2 by placeholder
    //~^ ERROR NoPanic (not established: reachable assert; structural NoPanic requires an assert-free body
{
    1
}

// A known-looking external name must not receive authority by suffix or an
// implicit primitive allowlist. No local body means no diagnostic record, and
// the citation remains outside the kernel fragment.
fn cite_known_external_name() -> u8
    ensures wrapping_add(1, 2) == 3 by placeholder
    //~^ ERROR no diagnostic E6 facet record exists for `wrapping_add`
{
    3
}

fn local_leaf(x: u8) -> u8 {
    x
}

// A local function containing a program call is not a closed scalar leaf.
// The diagnostic must stay negative; it must never reuse `local_leaf`'s
// positive findings or claim that a kernel admission exists.
fn calls_local_leaf(x: u8) -> u8 {
    local_leaf(x)
}

fn cite_internal_callee() -> u8
    ensures calls_local_leaf(1) == 1 by placeholder
    //~^ ERROR at least one E6 structural facet of `calls_local_leaf` is not established
{
    1
}

// Two distinct def-paths with one bare spelling must evict the bare key. A
// citation cannot inherit either record by body-walk or HIR inventory order.
mod left {
    pub fn twin(x: u8) -> u8 {
        x
    }
}

mod right {
    pub fn twin(x: u8) -> u8 {
        x
    }
}

fn cite_ambiguous_bare_name() -> u8
    ensures twin(1) == 1 by placeholder
    //~^ ERROR no diagnostic E6 facet record exists for `twin`
{
    1
}

fn main() {
    let _ = cite_fully_certified();
    let _ = cite_asserting();
    let _ = cite_known_external_name();
    let _ = cite_internal_callee();
    let _ = cite_ambiguous_bare_name();
    let _ = (left::twin(1), right::twin(1));
}
