//@ needs-trust-verify
//@ edition: 2021
//@ revisions: nightly guarded
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[nightly] check-fail
//@[guarded] check-pass
//! THE NIGHTLY STD NUMERIC METHODS THAT PANIC ON AN ARGUMENT VALUE
//! (NUM-NIGHTLY-UNCHARGED-1, 2026-10-06): the nightly half of
//! `std_numeric_value_panics_charged.rs`, whose 2026-09-25 audit covered stable
//! methods only. The same FALSE ACCEPT class: each function in the `nightly`
//! revision panics on the caller's own value inside core, the caller's MIR has no
//! `Assert` for it, and no call-site row charged it:
//!
//!   * signed `next_multiple_of` (`int_roundings`) — a zero divisor ("attempt to
//!     calculate the remainder with a divisor of zero"), or overflow under
//!     overflow checks ("attempt to add with overflow"); the unsigned twin was
//!     already charged;
//!   * `funnel_shl` / `funnel_shr` (`funnel_shifts`) — `n >= BITS` ("attempt to
//!     funnel shift left/right with overflow");
//!   * `strict_cast::<T>` / `strict_cast_signed` / `strict_cast_unsigned`
//!     (`integer_casts`, `integer_cast_extras`) — a value outside the target's
//!     range ("attempt to cast integer with overflow"), also handed over as a fn
//!     item;
//!   * `Duration::from_days` / `from_weeks` (`duration_constructors`) — "overflow
//!     in Duration::from_days/from_weeks".
//!
//! BEFORE (the stage 1 of `9e11546767`, `scratchpad/stage1-w17`, 2026-10-06, each
//! revision's flags plus `--cfg <revision>` and `--emit=metadata`): the `nightly`
//! revision builds with exit 0. Every function in it gets warnings only — one
//! `runtime_checked` row for the bundled member's internal check (signed
//! `next_multiple_of`), for the absent `core::intrinsics::unchecked_funnel_shl/shr`
//! callee (the funnel shifts), or the panic-freedom row (`strict_cast*`,
//! `from_days`/`from_weeks`) — and the fn item is admitted with no row at all. The
//! run twin `std_numeric_value_panics_charged_nightly_run.rs` exits 101 on each
//! panicking value. The `guarded` revision also builds with exit 0.
//!
//! AFTER (`generate::numeric_panic`; predicted, not yet built): each call carries a
//! call-site `Assertion` row — the precise failure condition over the caller's
//! argument, read at the block, so a dominating guard proves it — and an
//! unguarded call refutes it, so the default policy refuses each function in the
//! `nightly` revision. `guarded` pins the other direction: the guarded twins, the
//! literal arguments that cannot panic (a widening `strict_cast`, `funnel_shl(b,
//! 7)`, `next_multiple_of(-1)`, `from_weeks(4)`), the total siblings and the user
//! methods that merely share a name. The row-level twin is
//! `crates/trust-vcgen/tests/std_numeric_family_realmir.rs`, which also pins the
//! fail-closed `strict-cast-target-unmodeled` row of a generic `strict_cast::<T>`
//! (refused today already, as a generic absent callee, so it is not a witness
//! here).
//!
//! THE TRAIT SPELLING (wave-19 review, 2026-10-09): `strict_cast` delegates to
//! `CheckedCastFromInt::strict_cast_from` (`integer_casts`, publicly re-exported as
//! `core::convert::CheckedCastFromInt`), which panics on the same values. The fix
//! above matched only the inherent `strict_cast*` spellings, so on the stage 1 of
//! `46e9afaf95` `strict_cast_from_ufcs` and `strict_cast_from_assoc` built with exit 0
//! (one `runtime_checked` panic-freedom row each) and `strict_cast_from_fn_item` was
//! admitted with a `native-verification-gap` row only; a verify-off driver exited 101
//! on 300 for each. Their run witnesses are the `cast_from*` revisions of the run
//! twin. The `guarded` revision carries their guarded and widening twins.

#![allow(unused)]
// `funnel_shifts` stabilized in 1.101; naming it in the feature list now warns.
#![feature(int_roundings, integer_casts, integer_cast_extras)]
#![feature(duration_constructors)]
use std::time::Duration;

// ---- nightly: signed next_multiple_of ----

#[cfg(nightly)]
pub fn next_mult_i32(a: i32, b: i32) -> i32 {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::next_mult_i32`
    a.next_multiple_of(b)
}

// `b > 0` alone leaves `i32::MAX.next_multiple_of(2)`.
#[cfg(nightly)]
pub fn next_mult_i32_pos_only(a: i32, b: i32) -> i32 {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::next_mult_i32_pos_only`
    if b > 0 { a.next_multiple_of(b) } else { 0 }
}

// A literal divisor still overflows near `MAX`: `121i8.next_multiple_of(8)` is 128.
#[cfg(nightly)]
pub fn next_mult_i8_lit(a: i8) -> i8 {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::next_mult_i8_lit`
    a.next_multiple_of(8)
}

// ---- nightly: funnel shifts ----

#[cfg(nightly)]
pub fn funnel_shl_u32(a: u32, b: u32, n: u32) -> u32 {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::funnel_shl_u32`
    a.funnel_shl(b, n)
}

#[cfg(nightly)]
pub fn funnel_shr_u64(a: u64, b: u64, n: u32) -> u64 {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::funnel_shr_u64`
    a.funnel_shr(b, n)
}

#[cfg(nightly)]
pub fn funnel_shl_lit_bad(a: u32, b: u32) -> u32 {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::funnel_shl_lit_bad`
    a.funnel_shl(b, 32)
}

// A guard on the wrong operand.
#[cfg(nightly)]
pub fn funnel_shl_wrong_var(a: u32, b: u32, n: u32) -> u32 {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::funnel_shl_wrong_var`
    if b < 32 { a.funnel_shl(b, n) } else { 0 }
}

// An off-by-one guard.
#[cfg(nightly)]
pub fn funnel_shl_off_by_one(a: u32, b: u32, n: u32) -> u32 {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::funnel_shl_off_by_one`
    if n <= 32 { a.funnel_shl(b, n) } else { 0 }
}

// ---- nightly: strict casts ----

#[cfg(nightly)]
pub fn strict_cast_u32_u8(a: u32) -> u8 {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::strict_cast_u32_u8`
    a.strict_cast::<u8>()
}

#[cfg(nightly)]
pub fn strict_cast_i64_i8(a: i64) -> i8 {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::strict_cast_i64_i8`
    a.strict_cast::<i8>()
}

// A negative never fits an unsigned target, however wide.
#[cfg(nightly)]
pub fn strict_cast_i32_u64(a: i32) -> u64 {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::strict_cast_i32_u64`
    a.strict_cast::<u64>()
}

#[cfg(nightly)]
pub fn strict_cast_signed_u32(a: u32) -> i32 {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::strict_cast_signed_u32`
    a.strict_cast_signed()
}

#[cfg(nightly)]
pub fn strict_cast_unsigned_i32(a: i32) -> u32 {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::strict_cast_unsigned_i32`
    a.strict_cast_unsigned()
}

// Handed over as a fn item: no call-site row can be minted, so the vanilla
// admission of the item is withheld (`callee_has_call_site_panic_family`).
#[cfg(nightly)]
pub fn strict_cast_signed_fn_item(o: Option<u32>) -> Option<i32> {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::strict_cast_signed_fn_item`
    o.map(u32::strict_cast_signed)
}

// ---- nightly: the trait spelling of strict_cast ----

#[cfg(nightly)]
use core::convert::CheckedCastFromInt;

#[cfg(nightly)]
pub fn strict_cast_from_ufcs(a: u32) -> u8 {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::strict_cast_from_ufcs`
    <u8 as CheckedCastFromInt<u32>>::strict_cast_from(a)
}

#[cfg(nightly)]
pub fn strict_cast_from_assoc(a: i64) -> i8 {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::strict_cast_from_assoc`
    i8::strict_cast_from(a)
}

#[cfg(nightly)]
pub fn strict_cast_from_fn_item(o: Option<u32>) -> Option<u8> {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::strict_cast_from_fn_item`
    o.map(<u8 as CheckedCastFromInt<u32>>::strict_cast_from)
}

// ---- nightly: Duration ----

#[cfg(nightly)]
pub fn dur_from_days(d: u64) -> Duration {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::dur_from_days`
    Duration::from_days(d)
}

#[cfg(nightly)]
pub fn dur_from_weeks(w: u64) -> Duration {
    //[nightly]~^ ERROR `std_numeric_value_panics_charged_nightly::dur_from_weeks`
    Duration::from_weeks(w)
}

// ---- guarded ----

#[cfg(guarded)]
pub fn next_mult_i32_guarded(a: i32, b: i32) -> i32 {
    if b > 0 && b < 100 && a > -1000 && a < 1000 { a.next_multiple_of(b) } else { 0 }
}

#[cfg(guarded)]
pub fn next_mult_i32_negative_guarded(a: i32, b: i32) -> i32 {
    if b < -1 && b > -100 && a > -1000 && a < 1000 { a.next_multiple_of(b) } else { 0 }
}

// core returns `self` at once on `rhs == -1`.
#[cfg(guarded)]
pub fn next_mult_i32_minus_one(a: i32) -> i32 {
    a.next_multiple_of(-1)
}

#[cfg(guarded)]
pub fn funnel_shl_guarded(a: u32, b: u32, n: u32) -> u32 {
    if n < 32 { a.funnel_shl(b, n) } else { a }
}

#[cfg(guarded)]
pub fn funnel_shr_guarded(a: u64, b: u64, n: u32) -> u64 {
    if n < 64 { a.funnel_shr(b, n) } else { a }
}

#[cfg(guarded)]
pub fn funnel_shl_literal(a: u32, b: u32) -> u32 {
    a.funnel_shl(b, 7)
}

#[cfg(guarded)]
pub fn strict_cast_guarded(a: u32) -> u8 {
    if a <= 255 { a.strict_cast::<u8>() } else { 0 }
}

#[cfg(guarded)]
pub fn strict_cast_signed_target_guarded(a: i64) -> i8 {
    if a >= -128 && a <= 127 { a.strict_cast::<i8>() } else { 0 }
}

// A widening cast always fits.
#[cfg(guarded)]
pub fn strict_cast_widening(a: u8) -> u32 {
    a.strict_cast::<u32>()
}

#[cfg(guarded)]
pub fn strict_cast_signed_guarded(a: u32) -> i32 {
    if a <= 2147483647 { a.strict_cast_signed() } else { 0 }
}

#[cfg(guarded)]
pub fn strict_cast_unsigned_guarded(a: i32) -> u32 {
    if a >= 0 { a.strict_cast_unsigned() } else { 0 }
}

#[cfg(guarded)]
pub fn strict_cast_from_guarded(a: u32) -> u8 {
    if a <= 255 { <u8 as core::convert::CheckedCastFromInt<u32>>::strict_cast_from(a) } else { 0 }
}

#[cfg(guarded)]
pub fn strict_cast_from_signed_target_guarded(a: i64) -> i8 {
    if a >= -128 && a <= 127 { <i8 as core::convert::CheckedCastFromInt<i64>>::strict_cast_from(a) } else { 0 }
}

// A widening cast always fits.
#[cfg(guarded)]
pub fn strict_cast_from_widening(a: u8) -> u32 {
    <u32 as core::convert::CheckedCastFromInt<u8>>::strict_cast_from(a)
}

#[cfg(guarded)]
pub fn dur_from_days_guarded(d: u64) -> Duration {
    if d <= 1000 { Duration::from_days(d) } else { Duration::ZERO }
}

#[cfg(guarded)]
pub fn dur_from_weeks_literal() -> Duration {
    Duration::from_weeks(4)
}

// The total siblings.
#[cfg(guarded)]
pub fn total_siblings(a: u32, b: i32, c: i32) -> (Option<u8>, u8, u8, Option<i32>, i32) {
    (
        a.checked_cast::<u8>(),
        a.saturating_cast::<u8>(),
        a.wrapping_cast::<u8>(),
        b.checked_next_multiple_of(c),
        a.cast_signed(),
    )
}

// User methods that merely share a name.
#[cfg(guarded)]
pub struct W(pub u32);

#[cfg(guarded)]
impl W {
    pub fn funnel_shl(self, _rhs: u32, _n: u32) -> u32 {
        self.0
    }
    pub fn strict_cast_signed(self) -> u32 {
        self.0
    }
}

#[cfg(guarded)]
pub fn user_namesakes(n: u32) -> u32 {
    W(n).funnel_shl(1, n) ^ W(n).strict_cast_signed()
}
