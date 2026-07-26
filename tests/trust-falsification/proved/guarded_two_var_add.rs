#![crate_type = "lib"]
// A two-variable guarded addition. rustc inserts a runtime overflow-panic check;
// Trust discharges it STATICALLY. For `u32`, `a + b` overflow is a pure-Int check
// (unlike fixed-width MUL, which is bitvector). The violation
// `a<1000 ∧ b<1000 ∧ 0<=a ∧ 0<=b ∧ Or([a+b<0, a+b>u32::MAX])` is closed by the
// TWO-VARIABLE additive lift: `a<=999 ∧ b<=999 ⟹ a+b<=1998` (composing
// `Int.add_le_add_right`/`_left` + `Int.le_trans`) contradicts `a+b>MAX`, and
// `0<=a ∧ 0<=b ⟹ 0<=a+b` contradicts `a+b<0`. -full kernel-Certified (task #38).
pub fn guarded_two_var_add(a: u32, b: u32) -> u32 {
    if a < 1000 {
        if b < 1000 { a + b } else { 0 }
    } else {
        0
    }
}
