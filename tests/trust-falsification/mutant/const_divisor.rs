#![crate_type = "lib"]
// MUTANT of `proved/const_divisor.rs`: the divisor is now a runtime `i32` with no
// `!= 0` (and no `!(x==MIN && y==-1)`) guard, so `x / y` can divide by zero AND
// can overflow (`i32::MIN / -1`). The divisor conjuncts are now SAT obligations
// (`y = 0`, `y = -1`) the kernel cannot refute and the native CHC/PDR runner
// cannot prove; the verifier MUST fail closed (`[divzero] FAILED` with a verified
// counterexample), never certify.
pub fn const_divisor(x: i32, y: i32) -> i32 {
    x / y
}
