#![crate_type = "lib"]
// A constant index into a symbolic-length slice under a length guard. rustc keeps
// the runtime bounds-check; Trust discharges it STATICALLY. The bounds obligation
// is the MULTI-VARIABLE transitive chain `5 < len <= _5 <= _4 <= 3` (index `3`
// constant, `len` symbolic, guard `len > 5`): index 3 < 6 <= len. ay's Farkas
// can't close it (symbolic endpoints) and the single-var path can't (multiple
// vars), so the clean CIC kernel certifies it via the transitive-chain
// refutation (chained `Int.le_trans`/`Int.lt_of_lt_of_le` into the closed false
// `5 < 3`, then `Int.lt_irrefl`). -full kernel-Certified (task #37 generalization).
pub fn slen_guard_index(s: &[i32]) -> i32 {
    if s.len() > 5 { s[3] } else { 0 }
}
