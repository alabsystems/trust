#![crate_type = "lib"]
// Trust: piece #13 step-2 (safe-async native lowering). A SAFE ZERO-AWAIT
// `async fn`: the coroutine RESUME body reads the captured arg `x` back from the
// opaque frame (havoc'd u8), widens it and adds 1. `(x as u16) + 1` cannot
// overflow for any u8 x (max 255+1 = 256 < 65536), so the body's real overflow
// obligation is PROVED by ay. The native trust-ir-bridge lane now lowers the
// coroutine frame (opaque Undef), the state discriminant (havoc'd), and the
// resume-state protocol asserts (`ResumedAfter*` → executor-protocol Assume, a
// non-fatal Termination gap) — so this VERIFIES (exit 0) under strict `-full`.
// A regression that fails to lower the coroutine, or refutes the protocol
// asserts as data safety, or false-fails the termination self-loops, re-reddens
// this. NON-VACUOUS: the mutant sibling (async_zero_await_widen) overflows and
// MUST refute.
pub async fn f(x: u8) -> u16 {
    (x as u16) + 1
}
