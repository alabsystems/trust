#![crate_type = "lib"]
// A guarded unsigned subtraction. rustc inserts a runtime underflow-panic check;
// Trust discharges it STATICALLY. The overflow obligation is the disjunctive
// violation `x > 10 ∧ x <= u32::MAX ∧ Or([x-10 < 0, x-10 > u32::MAX])`: the guard
// `x > 10` rules out underflow (branch `x-10 < 0` shifts to `x < 10`, contradicting
// the guard) and the u32 bound rules out the (vacuous) overflow branch
// (`x-10 > MAX` shifts to `x > MAX+10`, contradicting `x <= MAX`). The clean CIC
// kernel certifies it by `Or.rec` case-split, shifting each `x-10` bound back onto
// `x` via `Int.lt_of_add_lt_add_right` and closing each case by transitive chain.
// -full kernel-Certified (task #38 — superior to rustc).
pub fn guarded_sub(x: u32) -> u32 {
    if x > 10 { x - 10 } else { 0 }
}
