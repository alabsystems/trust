#![crate_type = "lib"]
// A TWO-VARIABLE guarded unsigned subtraction (task #42's pattern — both operands
// symbolic, unlike single-variable `guarded_sub.rs` which subtracts the constant
// 10). rustc inserts a runtime underflow-panic check; Trust discharges it
// STATICALLY. The dominating guard `a > b` rules out the underflow disjunct of the
// `a - b` overflow obligation (`a - b < 0` shifts to `a < b`, contradicting the
// guard), and the u32 upper bound rules out the vacuous overflow branch. Proves
// panic-free under the default strict policy via the dominating-guard enrichment.
// Pairs with mutant/guarded_two_var_sub.rs (the one-token `>` -> `<` flip).
pub fn guarded_two_var_sub(a: u32, b: u32) -> u32 {
    if a > b { a - b } else { 0 }
}
