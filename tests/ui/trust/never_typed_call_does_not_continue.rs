//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@ edition: 2021
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! Control never continues past a call whose result type is `!`. The verifier
//! MODELS that fact; it does not only charge it.
//!
//! `inc` is the subject. Its obligations are the add, guarded by the `x == MAX`
//! branch, and the call to `stop`. `stop` is a bundled `-> !` function whose only
//! act is a bodyless, non-unwinding `extern "C"` import that never returns. That
//! call is ABI-total: it cannot unwind into Rust, and it has no Rust body to
//! panic in. So it carries no may-panic charge. `inc` cannot panic. Its
//! panic-freedom aggregate is PROVED, and the tally note below pins that.
//!
//! Measured on stage-1 98725f8d7d and again on f84c4d63c4, before the fix: the
//! aggregate was `runtime_checked` (`1 proved, ... 1 runtime-checked out of 2`,
//! plus two warnings; "fail-closed lowering reachable"), for two reasons.
//!   * trust-mc's call-summary interpreter declined EVERY bundled callee with no
//!     return path (`returns_not_combinable`). The call site then took the
//!     unconditional may-panic error rule (`UnsupportedDirectCallSummary`).
//!   * the lowering ended each never-typed call site with a bare `Unreachable`.
//!     Every engine encodes that as a charge (`Reachable ∧ path → ERROR`), and
//!     nothing before it said control stops at the call. `stop` lowered to the
//!     one-instruction body `[Unreachable]`, an error on its only path.
//! The fix states the type fact as `Assume(false)` after the call, and it
//! summarizes a callee with no return path and no declared result. The summary
//! half is trust-mc b5b7149e9, already in trust's pin. Re-measured on
//! origin/main 6797687314, which had that half and not the bridge's: `inc` was
//! still not proved (`1 proved, ... 1 runtime-checked, 1 skipped out of 3`, two
//! warnings), now as a counterexample: `stop`'s summary carries the error of
//! its bare `Unreachable` into the call site.
//!
//! Every tally below counts one `skipped` row more than it has obligations of its
//! own: trust-mc's default-function request, which that adapter declines for
//! every function (main's fixtures pin it the same way).
//!
//! The controls below must NOT prove. They are the proof that the fact is scoped
//! to the point after a `!` call and to nothing else:
//!   * `inc_after_return`: the callee RETURNS, so the add after it is reachable
//!     with `x == MAX` and overflows.
//!   * `pick`: a diverging call in ONE branch leaves the OTHER branch's
//!     unguarded add refuted.
//!   * `inc_after_panicking_stop`: the `-> !` callee panics on one path. Its
//!     summary now succeeds, and its panic is a real error condition in the
//!     caller.
//!   * `inc_after_absent_may_unwind`: an ABSENT `-> !` import that may unwind
//!     (`extern "C-unwind"`, so not ABI-total). Its may-panic
//!     `Assert(false)` marker sits in the SAME block as the `Assume(false)`,
//!     before it. The aggregate is solved, and it must stay a counterexample
//!     through the marker, exactly as before the fix. An engine that read the
//!     `Assume` as a block-wide or whole-path fact, rather than positionally,
//!     would prove it; this row is what catches that.
//! `memory_safe/reject_diverging_call_gap.rs` is the adversarial twin under the
//! memory-safe policy. The `std::process::exit` marker comes BEFORE the
//! `Assume`. Its aggregate is refused as CHC input before any solve, so it pins
//! the verdict, not the ordering; the row above pins the ordering.
//!
//! G3-MANDATE-L1-ONLY-1 (2026-10-27): `stop` and `carry_on` get the strict-gate
//! ERROR, not the advisory WARN first pinned here. Each body is one bodyless
//! `extern "C"` call with no FFI summary: an L0 `hardened_ffi_boundary` row and a
//! `hardened_unsafe_operation` row (the `structural-unsafe-demand-finding`), each a
//! literal `Bool(true)` modelling-gap fail-close. The compiler used to call any
//! hardened `Bool(true)` row a design mandate and skip it in the default policy's
//! tolerance; a mandate is now an L1 profile rule only
//! (`VcKind::is_hardened_design_mandate`). The Level 0 ERRORs, every tally NOTE and
//! `inc`'s PROVED aggregate are unchanged.

unsafe extern "C" {
    fn trust_never_call_exit(code: i32) -> !;
    fn trust_never_call_returns(code: i32);
}

unsafe extern "C-unwind" {
    fn trust_never_call_may_unwind(code: i32) -> !;
}

fn stop() -> ! {
    //~^ ERROR Trust Level 0 safety verification incomplete for `never_typed_call_does_not_continue::stop`
    //~| ERROR Trust strict verification failed for `never_typed_call_does_not_continue::stop`
    unsafe { trust_never_call_exit(1) }
}

pub fn inc(x: u32) -> u32 {
    //~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 skipped out of 3 obligation(s)
    if x == u32::MAX {
        stop();
    }
    x + 1
}

fn carry_on() {
    //~^ ERROR Trust Level 0 safety verification incomplete for `never_typed_call_does_not_continue::carry_on`
    //~| ERROR Trust strict verification failed for `never_typed_call_does_not_continue::carry_on`
    unsafe { trust_never_call_returns(1) }
}

pub fn inc_after_return(x: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `never_typed_call_does_not_continue::inc_after_return`
    //~| ERROR Trust strict verification failed for `never_typed_call_does_not_continue::inc_after_return`
    //~| NOTE 0 proved, 1 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    if x == u32::MAX {
        carry_on();
    }
    x + 1
}

pub fn pick(c: bool, x: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `never_typed_call_does_not_continue::pick`
    //~| ERROR Trust strict verification failed for `never_typed_call_does_not_continue::pick`
    //~| NOTE 0 proved, 1 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    if c { stop() } else { x + 1 }
}

fn stop_if(c: bool) -> ! {
    //~^ ERROR Trust Level 0 safety verification incomplete for `never_typed_call_does_not_continue::stop_if`
    //~| ERROR Trust strict verification failed for `never_typed_call_does_not_continue::stop_if`
    if c {
        panic!()
    }
    unsafe { trust_never_call_exit(1) }
}

pub fn inc_after_panicking_stop(c: bool, x: u32) -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete for `never_typed_call_does_not_continue::inc_after_panicking_stop`
    //~| WARN Trust verification advisory for `never_typed_call_does_not_continue::inc_after_panicking_stop`
    //~| NOTE 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    if x == u32::MAX {
        stop_if(c);
    }
    x + 1
}

pub fn inc_after_absent_may_unwind(x: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `never_typed_call_does_not_continue::inc_after_absent_may_unwind`
    //~| ERROR Trust strict verification failed for `never_typed_call_does_not_continue::inc_after_absent_may_unwind`
    //~| NOTE 1 proved, 1 failed, 1 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 5 obligation(s)
    if x == u32::MAX {
        unsafe { trust_never_call_may_unwind(1) }
    }
    x + 1
}
