//@ needs-trust-verify
//@ edition: 2024
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=strict --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Trust (r15, 2026-10-07): the by-move body rustc synthesizes for an async closure
//! (`DefKind::SyntheticCoroutineBody`, `…::{closure#0}::{synthetic#0}`) is a runtime
//! body the TrustVerify pass verifies, but it was outside the coverage universe
//! (`trust_coverage_eligible_body` admitted only fn, assoc fn and closure kinds), so
//! the eager walk never demanded it:
//!
//! * on a fail-closed lane whose walk found any refusal (here: every other async
//!   body), the compile aborts at the end of the walk, before anything demands the
//!   by-move body, so it is NEVER VERIFIED: MEASURED on stage 1 of `2a12d26fea` (this
//!   change's base), `-Ztrust-policy=strict --emit=metadata`: 19 errors, none for a
//!   `{synthetic#0}` body (this fixture's errors below are absent);
//! * otherwise it was demanded later (by `check_crate` or codegen), AFTER the coverage
//!   row and the crate summary were published, so its row (a FAILED one included) was
//!   missing from both. MEASURED on stage-1 `ae0494648a`, `-Ztrust-policy=advisory
//!   -Ztrust-verify-output=both`, the four shapes of
//!   `async_closure_by_move_body_no_ice.rs`: 23 `function_result` rows, the 4
//!   `{synthetic#0}` rows after `crate_summary`, which said `functions_analyzed: 19`
//!   and `total_failed: 6` against row sums of 7.
//!
//! AFTER: eligible and demanded inside the walk, so each by-move body is verified and
//! refused on its own row here. Measured on stage 1 of this change: the advisory build
//! above publishes all 23 rows before the summary, `functions_analyzed: 23`, every
//! summary total equal to the row sums. That half is not pinned here: with
//! `-Ztrust-verify-output` the compiler's output (over 1 MB even for one async
//! closure) exceeds compiletest's 512 KiB capture, which drops the summary. This pin
//! is the by-move bodies' own refusals, which exist only if the walk verified them.

async fn consume<F: AsyncFnOnce() -> u32>(function: F) -> u32 {
    function().await
}

pub async fn scalar_capture(value: u32) -> u32 {
    let closure = async move || value;
    //~^ ERROR for `async_closure_synthetic_body_in_eager_walk::scalar_capture::{closure#0}::{closure#0}::{synthetic#0}`
    consume(closure).await
}

pub async fn real_call(value: u32) -> u32 {
    let closure = async move || value.wrapping_add(1);
    //~^ ERROR for `async_closure_synthetic_body_in_eager_walk::real_call::{closure#0}::{closure#0}::{synthetic#0}`
    consume(closure).await
}
