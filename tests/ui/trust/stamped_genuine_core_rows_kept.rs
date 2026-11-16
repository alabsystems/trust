//@ needs-trust-verify
//@ edition: 2021
// `aux-crate`, not `aux-build`: the aux's crate name is `core`, so only an explicit
// `--extern fakecore=<path>` puts it in the graph under another name.
//@ aux-crate: fakecore=stamped_genuine_core/core.rs
//@ revisions: unguarded guarded family guarded_family time_point_cost
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[unguarded] check-fail
//@[guarded] check-pass
//@[family] check-fail
//@[guarded_family] check-pass
//@[time_point_cost] check-fail
//! A STAMPED GENUINE CORE KEEPS ITS `abs`, `pow` AND `unchecked_*` ROWS (wave-19
//! review, 2026-10-09). The extractor stamps the REAL core's paths
//! (`__trust_crate@<id>::core::num::<impl i32>::abs`) when a second crate named `core`
//! is in the graph (here `auxiliary/stamped_genuine_core/core.rs`), and under
//! `-Zbuild-std`. ABS-NAME-1 and UNCHECKED-NAME-1 (and before them POW-SYMEXP-1)
//! anchored the minting arms on an authenticated root, which refuses every stamp, so
//! these genuine calls lost their rows. MEASURED (each revision's flags plus
//! `--cfg <revision>`, the aux built verify-off as `--crate-name core`):
//!
//!   * the stage 1 of `f39efe05ca` (before wave 19): `abs_unguarded` is refused (the
//!     `negation` row is refuted at `x = i32::MIN`); `pow_unguarded` builds (an
//!     absent-callee `runtime_checked` row only);
//!   * the stage 1 of `46e9afaf95` (wave 19 before this fix): BOTH build with
//!     warnings only, and a verify-off binary of `abs_unguarded` panics "attempt to
//!     negate with overflow" on `i32::MIN`; `unchecked_add`'s `unchecked_overflow`
//!     row is gone too (the function is refused on its `[unsafe:unmodeled-call]` row
//!     either way, so it is not a witness here; the row is pinned by
//!     `crates/trust-vcgen/tests/stamped_genuine_core_realmir.rs`).
//!
//! After the fix (`numeric_panic::int_inherent_minting`) both unguarded functions are
//! refused under the default policy, and the guarded twins build.
//!
//! THE NUMERIC FAMILY (wave 23, STAMPED-CORE-MINT-1 residual, 2026-10-11). The same
//! stamp emptied `numeric_panic::numeric_value_panic_row` and
//! `numeric_panic::numeric_overflow_call`, which authenticated the callee through
//! `int_inherent` or an authenticated trait half and so refused every stamped
//! spelling: `ilog2`, `strict_add`, `clamp` (rendered
//! `__trust_crate@<id>::<i32 as core::cmp::Ord>::clamp`, the stamp in front of the
//! whole qualified path), `next_power_of_two` and `strict_neg` minted no row. Each
//! function kept only a `runtime_checked` row, which the default policy accepts, and a
//! verify-on binary panicked on the caller's value. MEASURED on the stage 1 of
//! `5911b1325f` with this file's flags plus `--cfg family` / `--cfg guarded_family`
//! (`--emit=metadata`, the aux built as compiletest builds it): `family` exits 0 with
//! warnings only and no error, so this check-fail revision fails before the fix;
//! `guarded_family` exits 0. Without the second `core` (no `extern crate fakecore`),
//! the same `family` source is refused for all five functions and the guarded twins
//! prove their rows: the stage 1 of `999b006b87` measured that AFTER here. Both functions now
//! read past ONE well-formed leading stamp (`numeric_panic::after_one_identity_stamp`)
//! and re-authenticate the rest. The forged-`core` side is pinned by
//! `stamped_forged_core_numeric_family_refused.rs`.
//!
//! THE COST, PINNED (revision `time_point_cost`; wave-23 review, 2026-10-11). The
//! literal grants (`literal_duration_nanos`, `is_clock_reading_callee`) stay
//! authenticated, so they refuse the stamped `core::time::Duration::from_*`. Reading
//! past the stamp lets the time-point and `Duration` operator arms reach a stamped
//! callee (`<std::time::Instant as core::ops::Add<core::time::Duration>>::add` is a
//! trait method of core, so it carries core's stamp even though `Instant` is std's),
//! and they then charge the fail-closed `time-point-duration-overflow` /
//! `duration-arith-overflow-unmodeled` row the grant would have decided. So in THIS
//! graph (a second `core`, no `-Zbuild-std`, one `std`) each function below is
//! refused: a false red, the cost DECISION_QUEUE STAMPED-CORE-MINT-2 takes. MEASURED
//! with this file's flags plus `--cfg time_point_cost` (`--emit=metadata`):
//! the stage 1 of `5911b1325f` (before STAMPED-CORE-MINT-2) exits 0 with no error, so
//! this check-fail revision fails there; the stage 1 of `999b006b87` exits 1 with all
//! five refused. Without the second `core` all five build on both. If the grants
//! ever authenticate the genuine core some other way, this revision is the one to
//! flip to check-pass.

extern crate fakecore as _;

#[cfg(unguarded)]
pub fn abs_unguarded(x: i32) -> i32 {
    //[unguarded]~^ ERROR `stamped_genuine_core_rows_kept::abs_unguarded`
    x.abs()
}

#[cfg(unguarded)]
pub fn pow_unguarded(a: u32, e: u32) -> u32 {
    //[unguarded]~^ ERROR `stamped_genuine_core_rows_kept::pow_unguarded`
    a.pow(e)
}

#[cfg(guarded)]
pub fn abs_guarded(x: i32) -> i32 {
    if x != i32::MIN { x.abs() } else { 0 }
}

#[cfg(guarded)]
pub fn pow_guarded(a: u32, e: u32) -> u32 {
    if a < 16 && e < 8 { a.pow(e) } else { 0 }
}

// `ilog2: argument of integer logarithm must be positive` at `x = 0`.
#[cfg(family)]
pub fn ilog2_unguarded(x: u32) -> u32 {
    //[family]~^ ERROR Level 0 safety verification incomplete for `stamped_genuine_core_rows_kept::ilog2_unguarded`
    x.ilog2()
}

// The overflow-call lane's `Add` row (`numeric_overflow_call`), refuted at `u32::MAX + 1`.
#[cfg(family)]
pub fn strict_add_unguarded(a: u32, b: u32) -> u32 {
    //[family]~^ ERROR Level 0 safety verification incomplete for `stamped_genuine_core_rows_kept::strict_add_unguarded`
    a.strict_add(b)
}

// `Ord::clamp: min > max`, through the qualified spelling behind the stamp.
#[cfg(family)]
pub fn clamp_unguarded(x: i32, lo: i32, hi: i32) -> i32 {
    //[family]~^ ERROR Level 0 safety verification incomplete for `stamped_genuine_core_rows_kept::clamp_unguarded`
    x.clamp(lo, hi)
}

// `next_power_of_two: attempt to add with overflow` above `2^31`.
#[cfg(family)]
pub fn next_power_of_two_unguarded(x: u32) -> u32 {
    //[family]~^ ERROR Level 0 safety verification incomplete for `stamped_genuine_core_rows_kept::next_power_of_two_unguarded`
    x.next_power_of_two()
}

// `strict_neg: attempt to negate with overflow` at `i32::MIN`.
#[cfg(family)]
pub fn strict_neg_unguarded(x: i32) -> i32 {
    //[family]~^ ERROR Level 0 safety verification incomplete for `stamped_genuine_core_rows_kept::strict_neg_unguarded`
    x.strict_neg()
}

#[cfg(guarded_family)]
pub fn ilog2_guarded(x: u32) -> u32 {
    if x > 0 { x.ilog2() } else { 0 }
}

#[cfg(guarded_family)]
pub fn strict_add_guarded(a: u32, b: u32) -> u32 {
    if a < 1000 && b < 1000 { a.strict_add(b) } else { 0 }
}

#[cfg(guarded_family)]
pub fn clamp_guarded(x: i32, lo: i32, hi: i32) -> i32 {
    if lo <= hi { x.clamp(lo, hi) } else { lo }
}

#[cfg(guarded_family)]
pub fn next_power_of_two_guarded(x: u32) -> u32 {
    if x <= 1024 { x.next_power_of_two() } else { 0 }
}

#[cfg(guarded_family)]
pub fn strict_neg_guarded(x: i32) -> i32 {
    if x != i32::MIN { x.strict_neg() } else { 0 }
}

#[cfg(time_point_cost)]
use std::time::{Duration, Instant, SystemTime};

#[cfg(time_point_cost)]
pub fn instant_plus_literal() -> Instant {
    //[time_point_cost]~^ ERROR Level 0 safety verification incomplete for `stamped_genuine_core_rows_kept::instant_plus_literal`
    Instant::now() + Duration::from_secs(5)
}

#[cfg(time_point_cost)]
pub fn instant_minus_literal() -> Instant {
    //[time_point_cost]~^ ERROR Level 0 safety verification incomplete for `stamped_genuine_core_rows_kept::instant_minus_literal`
    Instant::now() - Duration::from_millis(500)
}

#[cfg(time_point_cost)]
pub fn system_time_plus_literal() -> SystemTime {
    //[time_point_cost]~^ ERROR Level 0 safety verification incomplete for `stamped_genuine_core_rows_kept::system_time_plus_literal`
    SystemTime::now() + Duration::from_secs(1)
}

#[cfg(time_point_cost)]
pub fn duration_literal_sum() -> Duration {
    //[time_point_cost]~^ ERROR Level 0 safety verification incomplete for `stamped_genuine_core_rows_kept::duration_literal_sum`
    Duration::from_secs(1) + Duration::from_secs(2)
}

#[cfg(time_point_cost)]
pub fn duration_literal_scaled() -> Duration {
    //[time_point_cost]~^ ERROR Level 0 safety verification incomplete for `stamped_genuine_core_rows_kept::duration_literal_scaled`
    Duration::from_secs(1) * 2
}
