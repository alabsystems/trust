#![crate_type = "lib"]
// MUTANT of proved/async_zero_await_widen.rs. The widen is dropped: `x + 1` on a
// `u8` OVERFLOWS at x = 255 (255 + 1 wraps). The frame read of `x` is havoc'd
// (unconstrained u8), so ay finds the counterexample x = 255 and REFUTES the
// overflow obligation. MUST fail-closed (exit 1) under the default strict policy —
// if it verifies, the coroutine body was vacuously proved (a false proof).
pub async fn f(x: u8) -> u8 {
    x + 1
}
