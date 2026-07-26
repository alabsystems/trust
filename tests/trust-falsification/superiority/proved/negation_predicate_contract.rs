#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// SUPERIORITY: a NEGATION in the postcondition predicate (`*r == -1`), combined with
// a DISJUNCTION over a branching body. The contract-predicate lowering now handles
// unary `-` (previously the whole predicate was rejected as unsupported, fail-closing
// a valid negation postcondition). The constant `-1`/`1` cannot overflow, so Trust
// statically PROVES `*r == -1 || *r == 1` across both branches. Default mode must
// fully discharge it.
#[core::contracts::ensures(move |r: &i32| *r == -1 || *r == 1)]
pub fn negation_predicate_contract(b: bool) -> i32 {
    if b {
        -1
    } else {
        1
    }
}
