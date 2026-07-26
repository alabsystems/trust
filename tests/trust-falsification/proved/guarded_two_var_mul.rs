#![crate_type = "lib"]
// A two-variable guarded NONLINEAR multiplication. rustc inserts a runtime
// mul-overflow-panic check; Trust discharges it STATICALLY: the conjunctive guard
// `a < 1000 && b < 1000` bounds the product `a * b <= 999 * 999 = 998001 < u32::MAX`,
// so the overflow obligation is UNSAT and the check is eliminated. Strictly superior
// to rustc, which keeps the check — and unlike the linear add/sub guards
// (guarded_two_var_add/sub), this is a BITVECTOR multiply (nonlinear), exercising the
// bounded-multiply discharge. Pairs with mutant/guarded_two_var_mul.rs (the bound
// widened past the overflow threshold).
pub fn guarded_two_var_mul(a: u32, b: u32) -> u32 {
    if a < 1000 && b < 1000 {
        a * b
    } else {
        0
    }
}
