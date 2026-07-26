#![crate_type = "lib"]
// A constant-divisor signed division. rustc inserts a runtime div-by-zero panic
// and a runtime overflow check; Trust discharges both STATICALLY: the divisor `2`
// is a compile-time constant, so the div-by-zero obligation is the closed false
// equality `2 = 0` and the division-overflow obligation reduces to the closed
// false equality `2 = -1` (the only overflowing signed divisor). The clean CIC
// kernel certifies these closed equality contradictions IN-PROCESS (zero-trust,
// via `Eq.subst`/`Int.lt_irrefl` over the `Int.NonNeg.mk` witness) and the native
// trust-mc runner proves them under -full. -full reports kernel-Certified (#36).
pub fn const_divisor(x: i32) -> i32 {
    x / 2
}
