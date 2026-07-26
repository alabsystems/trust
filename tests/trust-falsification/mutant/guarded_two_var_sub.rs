#![crate_type = "lib"]
// MUTANT + DISCRIMINATING guard of proved/guarded_two_var_sub.rs: the ONLY change
// is the guard direction `a > b` -> `a < b`. Now the guarded branch runs `a - b`
// exactly when `a < b`, i.e. precisely when the unsigned subtraction UNDERFLOWS.
// The underflow disjunct `a - b < 0` is SAT under the (wrong) guard, so it cannot
// be closed; the verifier MUST fail closed (`[overflow] FAILED`, exit 1). Guards
// that the dominating-guard enrichment uses the guard's DIRECTION soundly — a model
// that ignored the comparison sense would falsely prove this real underflow.
pub fn guarded_two_var_sub(a: u32, b: u32) -> u32 {
    if a < b { a - b } else { 0 }
}
