// Rust `main` calls a Clean-origin def with verification ON (default policy),
// and the assert on the returned value is DISCHARGED by the Clean-origin call
// grounding in the assert-refutation lane (the definitional projection summary
// `result == arg0` grounds `v`, so `v == 41` is refuted-unreachable and the
// panic-freedom aggregate is kernel re-checked). The assert carries no message:
// a formatted panic message routes through std's fmt::write / arbitrary-Display
// path, a separate frontier (see r09), not the Clean-origin call this row tests.
mod m {
    clean {
        def pick (a : UInt64) (b : UInt64) : UInt64 := a
    }
}
fn main() {
    let v = m::pick(41, 7);
    assert!(v == 41);
}
