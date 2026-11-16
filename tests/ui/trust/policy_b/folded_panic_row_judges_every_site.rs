//@ needs-trust-verify
//@ revisions: fatal tolerated certify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[fatal] check-fail
//@[tolerated] check-pass
//@[certify] check-fail
//! TRUST_NO_SYSROOT_CENSUS (2026-09-26): this file needs TOLERATED absent-callee
//! sites to fold, and its examples (`checked_add`, `saturating_add`, `checked_sub`)
//! reach no panic site, so the sysroot panic census discharges them outright
//! (docs/design/trust-std-design.md, amendment 2026-09-26) — they would no longer
//! be tolerated gaps, and the `certify` refusals below would stop measuring the
//! fold. The census is off here; it only ever withholds grants.
//!
//! THE FOLD HOLE (measured 2026-09-23, stage-1 `96f2019566`): a false accept.
//!
//! The bridge folds every marked panic site of a bundle into ONE whole-function
//! panic-freedom row, and that row's description names only the FIRST marked
//! site. The default policy's row gate judged the row by that name alone. So a
//! TOLERATED site written first (`checked_add`, a `println!`) vouched for a FATAL
//! one written after it:
//!
//!     pub fn g(a: i32, b: i32, c: u32, d: u32) -> u32 {
//!         let _ = a.checked_add(b);
//!         c.wrapping_div(d)
//!     }
//!
//! built rc=0 with one `runtime-checked` row and two warnings, and a binary
//! calling `g(1, 2, 10, 0)` panicked `attempt to divide by zero` (exit 101).
//! Swapping the two statements was correctly refused, which is what located it:
//! the verdict depended on statement ORDER, not on what the function can do.
//! Same result with `println!("hi")` in front of the `wrapping_div`.
//!
//! THE FIX judges EVERY folded site, so one fatal site anywhere in the fold is
//! fatal for the row.
//!
//! What each revision pins:
//!
//!   * `fatal` — every function is refused, in BOTH statement orders. On the
//!     baseline compiler the four marked FALSE ACCEPT built clean, so this
//!     revision is red before the fix through its missing annotations; the two
//!     marked CONTROL were already refused and prove the site itself was never
//!     the difficulty.
//!   * `tolerated` — a fold whose sites are ALL tolerated still builds under the
//!     default policy. A fix that refuses any function with more than one site
//!     would close the hole by over-refusing; this revision is what forbids that.
//!   * `certify` — the same tolerated functions are still REFUSED under
//!     `-Ztrust-policy=certify`, so `tolerated` passing means "reported, not
//!     proved", never that some site quietly became proved.
//!
//! AMENDED 2026-10-07 (L2a, docs/DECISION_QUEUE.md "L2a"; landed independently
//! on the local line 2026-09-28 via `signed_checked_arithmetic_is_total.rs`): a
//! site DID become proved, deliberately. `iN::checked_add` / `checked_sub` /
//! `checked_mul` carry the TyCtxt-authenticated
//! `@trust-rustc-checked-primitive-method::` stamp, and the native bridge now
//! lowers that call as total (Trusted, panic-freedom only; docs/TCB.md), as its
//! unstamped spelling already was. So `a.checked_add(b)` is no longer a folded
//! site at all: `checked_then_saturating` and `two_checked` have no unproved row
//! and certify ACCEPTS them (they cannot panic, and that is correct), and the
//! `fatal` functions that put it first now fold only their fatal site (still
//! refused). The fold coverage those functions carried is kept by `println!`
//! twins, whose `_print` site is still a tolerated absent callee:
//! `fatal_between_prints` (a fatal site neither first nor last), `two_prints`
//! (an all-tolerated fold: built under default, refused under certify, against
//! over-refusal) and `print_then_checked` (refused under certify).

// ---- fatal: one fatal site in the fold, anywhere, refuses the function ----

/// FALSE ACCEPT on the baseline: the measured reproducer, tolerated site first.
#[cfg(fatal)]
pub fn checked_then_wrapping_div(a: i32, b: i32, c: u32, d: u32) -> u32 {
    //[fatal]~^ ERROR Trust strict verification failed for `folded_panic_row_judges_every_site::checked_then_wrapping_div`
    let _ = a.checked_add(b);
    c.wrapping_div(d)
}

/// CONTROL: the same two statements swapped. Refused on the baseline too.
#[cfg(fatal)]
pub fn wrapping_div_then_checked(a: i32, b: i32, c: u32, d: u32) -> u32 {
    //[fatal]~^ ERROR Trust strict verification failed for `folded_panic_row_judges_every_site::wrapping_div_then_checked`
    let q = c.wrapping_div(d);
    let _ = a.checked_add(b);
    q
}

/// FALSE ACCEPT on the baseline: the remainder spelling of the same panic.
#[cfg(fatal)]
pub fn checked_then_wrapping_rem(a: i32, b: i32, c: u32, d: u32) -> u32 {
    //[fatal]~^ ERROR Trust strict verification failed for `folded_panic_row_judges_every_site::checked_then_wrapping_rem`
    let _ = a.checked_add(b);
    c.wrapping_rem(d)
}

/// FALSE ACCEPT on the baseline: the fatal site is neither first nor last, so a
/// fix that also judged only the LAST site would still let this through.
/// L2a twin of `fatal_between_tolerated`: the tolerated sites are `_print`.
#[cfg(fatal)]
pub fn fatal_between_prints(c: u32, d: u32) -> u32 {
    //[fatal]~^ ERROR Trust strict verification failed for `folded_panic_row_judges_every_site::fatal_between_prints`
    println!("a");
    let q = c.wrapping_div(d);
    println!("b");
    q
}

#[cfg(fatal)]
pub fn fatal_between_tolerated(a: i32, b: i32, c: u32, d: u32) -> u32 {
    //[fatal]~^ ERROR Trust strict verification failed for `folded_panic_row_judges_every_site::fatal_between_tolerated`
    let _ = a.checked_add(b);
    let q = c.wrapping_div(d);
    let _ = a.checked_sub(b);
    q
}

/// FALSE ACCEPT on the baseline: a tolerated std print backend first.
#[cfg(fatal)]
pub fn print_then_wrapping_div(c: u32, d: u32) -> u32 {
    //[fatal]~^ ERROR Trust strict verification failed for `folded_panic_row_judges_every_site::print_then_wrapping_div`
    println!("hi");
    c.wrapping_div(d)
}

/// CONTROL: the print after the division. Refused on the baseline too.
#[cfg(fatal)]
pub fn wrapping_div_then_print(c: u32, d: u32) -> u32 {
    //[fatal]~^ ERROR Trust strict verification failed for `folded_panic_row_judges_every_site::wrapping_div_then_print`
    let q = c.wrapping_div(d);
    println!("hi");
    q
}

// ---- tolerated / certify: every folded site is tolerated ----

#[cfg(any(tolerated, certify))]
/// Since L2a: no unproved row (the stamped `checked_add` is total, `saturating_add`
/// is total), so certify accepts it.
pub fn checked_then_saturating(a: i32, b: i32, c: u32, d: u32) -> u32 {
    let _ = a.checked_add(b);
    c.saturating_add(d)
}

#[cfg(any(tolerated, certify))]
/// Since L2a: no unproved row, so certify accepts it (see the header). Only the
/// `i32::checked_add` site is L2a's: `u32::checked_sub` is unsigned, which the
/// stamp never covers, and is discharged by the pre-existing bare
/// `core::num::<impl uN>::checked_*` total admission, as it was before L2a.
pub fn two_checked(a: i32, b: i32, c: u32, d: u32) -> Option<u32> {
    let _ = a.checked_add(b);
    c.checked_sub(d)
}

/// L2a twin: an all-tolerated fold of two `_print` sites. Built under the
/// default policy, refused under certify.
#[cfg(any(tolerated, certify))]
pub fn two_prints(c: u32, d: u32) -> u32 {
    //[certify]~^ ERROR Trust strict verification failed for `folded_panic_row_judges_every_site::two_prints`
    println!("a");
    println!("b");
    c.saturating_add(d)
}

#[cfg(any(tolerated, certify))]
pub fn print_then_checked(a: i32, b: i32) -> Option<i32> {
    //[certify]~^ ERROR Trust strict verification failed for `folded_panic_row_judges_every_site::print_then_checked`
    println!("hi");
    a.checked_add(b)
}
