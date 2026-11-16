//@ revisions: fnptr_foreign fold_fnitem map_unwrap sort split map_some local_item reify_local
//@ revisions: trim_numeric map_abs
//@ revisions: fold_div_ceil reduce_pow fold_signed_pow try_fold_checked_pow fold_wrapping_pow
//@ revisions: fold_div_operator fold_rem_operator_ref fold_wrapping_div_operator
//@ revisions: fold_nonzero_div_operator fold_float_div_operator
//@ revisions: map_sum_item_last map_sum_ref_item_collect option_map_sum_item
//@ revisions: map_float_sum_item_last map_count_item_collect
//@ revisions: fold_add_operator_ref fold_add_operator_ref_certify fold_shl_operator_ref
//@ revisions: map_neg_operator_ref_collect fold_wrapping_add_operator_ref
//@ revisions: fold_float_add_operator_ref fold_bitand_operator_ref
//@ revisions: map_uninit_slice_item_collect map_zeroed_slice_item_collect
//@ revisions: map_rc_uninit_slice_item_len_collect map_uninit_slice_item_count
//@ revisions: option_map_uninit_slice_item closure_uninit_slice_collect
//@ revisions: local_item_uninit_slice_collect guarded_uninit_slice_direct
//@ revisions: map_panic_any_item_collect map_panic_any_item_count option_map_panic_any_item
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[fold_add_operator_ref_certify] compile-flags: -Ztrust-policy=certify
//@[fnptr_foreign] check-fail
//@[fold_fnitem] check-fail
//@[map_unwrap] check-fail
//@[trim_numeric] check-pass
//@[map_abs] check-fail
//@[sort] check-pass
//@[split] check-pass
//@[map_some] check-pass
//@[local_item] check-pass
//@[reify_local] check-fail
//@[fold_div_ceil] check-fail
//@[reduce_pow] check-fail
//@[fold_signed_pow] check-fail
//@[try_fold_checked_pow] check-pass
//@[fold_wrapping_pow] check-pass
//@[fold_div_operator] check-fail
//@[fold_rem_operator_ref] check-fail
//@[fold_wrapping_div_operator] check-fail
//@[fold_nonzero_div_operator] check-pass
//@[fold_float_div_operator] check-pass
//@[map_sum_item_last] check-fail
//@[map_sum_ref_item_collect] check-fail
//@[option_map_sum_item] check-fail
//@[map_float_sum_item_last] check-pass
//@[map_count_item_collect] check-pass
//@[fold_add_operator_ref] check-fail
//@[fold_add_operator_ref_certify] check-fail
//@[fold_shl_operator_ref] check-fail
//@[map_neg_operator_ref_collect] check-fail
//@[fold_wrapping_add_operator_ref] check-pass
//@[fold_float_add_operator_ref] check-pass
//@[fold_bitand_operator_ref] check-pass
//@[map_uninit_slice_item_collect] check-fail
//@[map_zeroed_slice_item_collect] check-fail
//@[map_rc_uninit_slice_item_len_collect] check-fail
//@[map_uninit_slice_item_count] check-fail
//@[option_map_uninit_slice_item] check-fail
//@[closure_uninit_slice_collect] check-fail
//@[local_item_uninit_slice_collect] check-fail
//@[guarded_uninit_slice_direct] check-pass
//@[map_panic_any_item_collect] check-fail
//@[map_panic_any_item_count] check-fail
//@[option_map_panic_any_item] check-fail
//@ dont-check-compiler-stderr
//@[fnptr_foreign] dont-require-annotations: ERROR
//@[fold_fnitem] dont-require-annotations: ERROR
//@[map_unwrap] dont-require-annotations: ERROR
//@[sort] dont-require-annotations: ERROR
//@[split] dont-require-annotations: ERROR
//@[map_some] dont-require-annotations: ERROR
//@[trim_numeric] dont-require-annotations: ERROR
//@[map_abs] dont-require-annotations: ERROR
//@[fold_div_ceil] dont-require-annotations: ERROR
//@[reduce_pow] dont-require-annotations: ERROR
//@[fold_signed_pow] dont-require-annotations: ERROR
//@[fold_div_operator] dont-require-annotations: ERROR
//@[fold_rem_operator_ref] dont-require-annotations: ERROR
//@[fold_wrapping_div_operator] dont-require-annotations: ERROR
//@[fold_nonzero_div_operator] dont-require-annotations: ERROR
//@[fold_float_div_operator] dont-require-annotations: ERROR
//@[map_sum_item_last] dont-require-annotations: ERROR
//@[map_sum_ref_item_collect] dont-require-annotations: ERROR
//@[option_map_sum_item] dont-require-annotations: ERROR
//@[map_float_sum_item_last] dont-require-annotations: ERROR
//@[map_count_item_collect] dont-require-annotations: ERROR
//@[fold_add_operator_ref] dont-require-annotations: ERROR
//@[fold_add_operator_ref_certify] dont-require-annotations: ERROR
//@[fold_shl_operator_ref] dont-require-annotations: ERROR
//@[map_neg_operator_ref_collect] dont-require-annotations: ERROR
//@[fold_wrapping_add_operator_ref] dont-require-annotations: ERROR
//@[fold_float_add_operator_ref] dont-require-annotations: ERROR
//@[fold_bitand_operator_ref] dont-require-annotations: ERROR
//@[map_uninit_slice_item_collect] dont-require-annotations: ERROR
//@[map_zeroed_slice_item_collect] dont-require-annotations: ERROR
//@[map_rc_uninit_slice_item_len_collect] dont-require-annotations: ERROR
//@[map_uninit_slice_item_count] dont-require-annotations: ERROR
//@[option_map_uninit_slice_item] dont-require-annotations: ERROR
//@[closure_uninit_slice_collect] dont-require-annotations: ERROR
//@[local_item_uninit_slice_collect] dont-require-annotations: ERROR
//@[guarded_uninit_slice_direct] dont-require-annotations: ERROR
//@[map_panic_any_item_collect] dont-require-annotations: ERROR
//@[map_panic_any_item_count] dont-require-annotations: ERROR
//@[option_map_panic_any_item] dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A callable that NOBODY in this compilation verified must not be called for
//! free. Two silent false accepts, measured on stage 1 (`43b8fe6ab`) by the
//! wave-3 assert-gate adversarial review — each built rc=0 with NO row for the
//! call, and the binary panicked (exit 101):
//!
//! * `fnptr_foreign`: `let p: fn(u32, u32) -> u32 = u32::div_euclid; p(100, b)`.
//!   The reified-constant carve-out of the indirect-call gate assumed the target
//!   "is verified as its own root"; a SYSROOT item is verified by nobody here.
//!   The carve-out now requires a LOCAL target.
//! * `fold_fnitem`: `v.iter().copied().fold(100, u32::div_euclid)` — a DIRECT
//!   call to core's `fold` whose `F` is a sysroot item type; `div_euclid` runs
//!   inside `fold`, where no row and no family recognizer looks. A foreign item
//!   type argument (or a bare `fn` pointer type) now counts as an unresolved
//!   call, unless the item is ACCOUNTED FOR (`foreign_fn_item_type_arg_is_accounted`):
//!   a constructor, or a sysroot item that either cannot panic by its own MIR
//!   (`sysroot_fn_item_cannot_panic`) or would be charged nothing as a DIRECT
//!   call — vanilla-sysroot and in none of vcgen's call-site panic families.
//! * `map_unwrap`: `map(Option::unwrap)`, the same shape through `unwrap`.
//! * `map_abs` (check-fail, and NOT silent): `map(i32::abs)` over `[i32::MIN]`
//!   panics at runtime. It was an ADVISORY (policy B) only because the `sum`'s
//!   own fold-overflow row was never minted: the fn-item callable's `->` broke
//!   vcgen's callee parse (review round 29, 2026-10-01; main's W4 ITER-HOF
//!   repaired the same arrow misparse independently, see below). With the row
//!   charged, an `i32` sum over an unbounded slice is the `iterator-fold-overflow`
//!   refusal, which has no runtime fallback. Pinned so a change that made it
//!   SILENT would show.
//!
//! Trust (2026-09-29): `map_abs` and `split` are now REFUSED (`check-fail`), by
//! the bundled std-member fix. Each was admitted through the lowering-failure
//! tolerance, on a bundle DISCARDED because `sum()`/`count()` bundles a core member
//! whose inherited `Overflow(Add)` Assert the admission lane refuses. The bundle is
//! now kept (that Assert is a `runtime_checked` row), and the kept bundle carries a
//! fail-closed row the discarded one hid: for `map_abs` "an unresolved indirect
//! call" (the `i32::abs` item called inside core's `Map::fold`) — the row the
//! success path already refuses for `v.iter().copied().map(i32::abs).max()` and
//! `.last()`, which bundle no refused member (measured on origin/main
//! `f6773df328e`, release-like std: rc=1, same row); for `split` "a generic absent
//! callee" (`<Split<'_, fn(char) -> bool {is_whitespace}> as Iterator>::fold::<usize,
//! {count's closure}>`, a core member evicted from the kept bundle whose
//! instantiation at core's own closure the vanilla ledger does not classify).
//! Capability losses, recorded in docs/KNOWN_HAZARDS.md ("CLOSED 2026-09-29 — the
//! bundled std-member tolerance …"); `split(char::is_whitespace)` itself stays
//! vanilla (`vanilla_sysroot_fn_item_type_argument.rs#last`).
//!
//! Trust (W4 ITER-HOF, 2026-10-01): `split` is ADMITTED again (`check-pass`), with
//! the same advisory `map_abs` used to carry. Core's `Split::fold::<usize, {count's
//! closure}>` is no longer an absent callee: the bridge's closure-consumer classifier
//! (`closure_driving_consumer_call`) now reads the `->` of the receiver's
//! `fn(char) -> bool {is_whitespace}` as text (`arrow_neutral`), so the call takes
//! the closure-consumer arm that the same `fold` over an arrow-free receiver
//! (`Split<'_, char>`) always took, not the fatal absent-callee arm; core's count closure is a
//! bundled member whose inherited `Overflow(Add)` Assert is the `runtime_checked`
//! row, and `is_whitespace` is a sysroot item the root's `split::<..>` call already
//! classifies vanilla. Nothing user-written runs inside that fold. `map_abs` stays
//! refused and now carries a SECOND row: W4 repaired the same arrow misparse in
//! vcgen's spelling parsers (`vc_qualifier_group`, `vc_strip_generics`), so F4's
//! integer-fold recognizer now matches `<Map<.., fn(i32) -> i32 {abs}> as
//! Iterator>::sum` and charges its `iterator-fold-overflow` row (`[i32::MAX, 1]`
//! overflows the sum), beside the unresolved indirect call (2 obligations, was 1).
//!
//! The check-pass revisions are the shapes the sysroot-item admission of
//! 2026-09-18 exists for, and they must stay admitted: `sort` (its comparator is
//! `<u32 as PartialOrd>::lt`), `split(char::is_whitespace)` (see the 2026-09-29
//! note above for its `count()`), `map(Some)` (a
//! constructor), a LOCAL item handed to `any` (verified as its own root), and a
//! reified LOCAL pointer. Both local items are `requires`-free: since 2026-09-29 a
//! local item that owes its callers a `requires` is refused on both routes
//! (`requires_callee_handed_to_generic_code.rs`,
//! `requires_callee_reified_to_fn_pointer.rs`).
//!
//! Trust (W4 ITER-HOF fix round 4, 2026-10-02): `fold_div_ceil`, `reduce_pow` and
//! `fold_signed_pow` are the same hole as `fold_fnitem`, through the two numeric
//! call-site families the name-only union `callee_has_call_site_panic_family` had
//! left out (`divzero_call`: `div_ceil`; `overflow_arith_call`: `pow`, which
//! overflows under the caller's overflow checks). MEASURED on stage 1 of origin/main
//! `a3be88bbde` (and identically with W4, adversarial probes q07/q08 of
//! `w4-salvage/probes/T5-iterhof-fix8`): each built rc=0 with no row but a
//! `native-verification-gap`, and a verify-off driver panicked ("attempt to divide
//! by zero" for `[5, 0]`, "attempt to exponentiate with overflow" for `[40]`), while
//! the direct calls and the closure twins were refused. `try_fold_checked_pow` and
//! `fold_wrapping_pow` are the total siblings (`checked_pow`, `wrapping_pow`), which
//! must stay admitted.
//!
//! The integer division OPERATORS handed as items were the same hole:
//! `fold_div_operator` (`fold(7u32, core::ops::Div::div)`), `fold_rem_operator_ref`
//! (`v.iter().fold(7u32, core::ops::Rem::rem)`, i.e. `<u32 as Rem<&u32>>::rem`) and
//! `fold_wrapping_div_operator` (`Wrapping<u32>`, whose `Div` is `wrapping_div`) built
//! rc=0 on `a3be88bbde` (and with W4) and a driver panicked on a zero divisor, while
//! the direct `core::ops::Div::div(a, b)` is charged a precondition row. Withheld by
//! `numeric_panic::is_int_division_operator_callee`. A `NonZero` divisor
//! (`fold_nonzero_div_operator`) and a float (`fold_float_div_operator`) stay admitted.
//!
//! And the integer `sum`/`product` folds handed as items, which a direct call pays
//! as an `iterator-fold-overflow` row: `map_sum_item_last`
//! (`.map(Iterator::sum::<u32>).last()`) and `option_map_sum_item`
//! (`o.map(Vec::into_iter).map(Iterator::sum::<u32>)`) built rc=0 on `a3be88bbde` with
//! a `runtime_checked` row and panicked "attempt to add with overflow" on
//! `[u32::MAX, 1]`; `map_sum_ref_item_collect` (the same `map` collected) was refused on
//! main only for its collect count and built rc=0 with W4 ITER-HOF. Withheld by
//! `alloc_bounds::iterator_fold_item_may_overflow`. A float accumulator
//! (`map_float_sum_item_last`) and `Iterator::count` (`map_count_item_collect`, a W4
//! capability: main refused its collect count) stay admitted.
//!
//! And the integer OVERFLOW-checked operators handed as items BY REFERENCE, which the
//! call-site family leaves to the ruled foundational-member class (a closure's
//! `|a, b| a + b` is charged a runtime-checked row the default policy reports and
//! `certify` refuses — not "nothing"): `fold_add_operator_ref` (`v.iter().fold(0u32,
//! core::ops::Add::add)`, i.e. `<u32 as Add<&u32>>::add`), `fold_add_operator_ref_certify`
//! (the same under `certify`) and `fold_shl_operator_ref` (`fold(1u32, Shl::shl)`) built
//! rc=0 under BOTH policies on stage 1 of `990826872e` and of the W4 branch, with no row
//! for the operator, and panicked verify-off ("attempt to add with overflow", "attempt
//! to shift left with overflow"); `map_neg_operator_ref_collect`
//! (`v.iter().map(core::ops::Neg::neg).collect()`, `<&i32 as Neg>::neg`) was refused on
//! `990826872e` only by its collect count and built rc=0 with W4, panicking "attempt to
//! negate with overflow" on `i32::MIN`. Withheld by
//! `numeric_panic::is_int_overflow_operator_callee`. The total by-reference operators —
//! `Wrapping` (`fold_wrapping_add_operator_ref`), float (`fold_float_add_operator_ref`)
//! and bitwise (`fold_bitand_operator_ref`) — stay admitted (rc=0 under both policies,
//! measured on the same two compilers).
//!
//! Trust (W4 ITER-HOF landing round, 2026-10-03): two more items the union did not
//! withhold, found by the landing review's independent probes on stage 1 of the W4
//! branch (`ba656c61b6`) against origin/main `9fc182f094`. Each panicked verify-off.
//!  * The `Box`/`Rc`/`Arc` uninitialized and zeroed SLICE constructors.
//!    `map_uninit_slice_item_collect`, `map_zeroed_slice_item_collect` and
//!    `map_rc_uninit_slice_item_len_collect` were refused on main only by the collect
//!    count and built rc=0 with W4. `map_uninit_slice_item_count` and
//!    `option_map_uninit_slice_item` built rc=0 on main too. No lane charged these
//!    constructors at all: the closure twin `closure_uninit_slice_collect` and a local
//!    `fn` wrapping the call (`local_item_uninit_slice_collect`, whose own root is
//!    charged now) built rc=0 on main. Each panics "capacity overflow" on `usize::MAX`.
//!    They are now bulk allocations counted at argument 0 (`alloc_bounds::
//!    bulk_alloc_call`, mirrored by the extractor's `is_bulk_alloc_sink_call`), so a
//!    direct call is charged like `with_capacity(n)` and the item is withheld through
//!    `callee_is_call_site_allocation_sink`. A guarded direct call
//!    (`guarded_uninit_slice_direct`) stays admitted.
//!  * A DIVERGING item, `std::panic::panic_any::<u32>`: `map_panic_any_item_collect`
//!    (W4-exposed), `map_panic_any_item_count` and `option_map_panic_any_item` (rc=0 on
//!    main). A direct call bundles the item's body, whose panic machinery is not
//!    vanilla, so the closure twin was always refused; the item spelling was admitted
//!    by name. `foreign_fn_item_type_arg_is_accounted` no longer admits a `-> !` item
//!    through the vanilla arm.

#[cfg(fnptr_foreign)]
pub fn f(b: u32) -> u32 { //[fnptr_foreign]~ ERROR Trust strict verification failed
    let p: fn(u32, u32) -> u32 = u32::div_euclid;
    p(100, b)
}

#[cfg(fold_fnitem)]
pub fn f(v: &[u32]) -> u32 { //[fold_fnitem]~ ERROR Trust strict verification failed
    v.iter().copied().fold(100, u32::div_euclid)
}

#[cfg(map_unwrap)]
pub fn f(v: Vec<Option<u32>>) -> Vec<u32> {
    v.into_iter().map(Option::unwrap).collect()
}

// `char::is_numeric`'s MIR reaches a bounds-checked table lookup, so the
// structural walk cannot clear it; it is admitted by the SAME standard as a
// direct call `c.is_numeric()` (vanilla, no call-site panic family).
#[cfg(trim_numeric)]
pub fn f(s: &str) -> &str {
    s.trim_matches(char::is_numeric)
}

#[cfg(map_abs)]
pub fn f(v: &[i32]) -> i32 {
    //[map_abs]~^ WARN a bundled std/core/alloc member's internal obligation was not statically discharged
    //[map_abs]~| ERROR Trust strict verification failed for `callable_handed_to_sysroot_is_charged::f`: 2 obligation(s) were not fully verified
    v.iter().copied().map(i32::abs).sum()
}

#[cfg(sort)]
pub fn f(v: &mut Vec<u32>) {
    v.sort();
}

#[cfg(split)]
pub fn f(s: &str) -> usize {
    // Re-pinned 2026-10-15 (the merge of 2026-10-14, DECISION_QUEUE D103(d)): no advisory.
    // `count()` over `Split<'_, fn(char) -> bool {is_whitespace}>` is now decided total by the
    // drive-only consumer lane (a counter that cannot pass the receiver's item count; a core
    // predicate as the pattern), so core's count closure is no longer a bundled member owing a
    // runtime-checked row, and the body publishes `no_obligations`.
    s.split(char::is_whitespace).count()
}

#[cfg(map_some)]
pub fn f(x: Option<u32>) -> Option<Option<u32>> {
    x.map(Some)
}

#[cfg(local_item)]
fn is_even(x: &u32) -> bool {
    *x % 2 == 0
}
#[cfg(local_item)]
// ZERO-ROW-GATE (2026-10-10) refused this zero-row body. Since 2026-10-15 (DECISION_QUEUE
// D103, VERIFIED-CALLABLE-ZERO-ROW-PARITY) the gate reads the drive-only consumer lane's
// decision for the call, which discharges it through the callable's own verdict: it builds.
pub fn f(v: &[u32]) -> bool {
    v.iter().any(is_even)
}

#[cfg(reify_local)]
fn g(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}
#[cfg(reify_local)]
// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//[reify_local]~vv ERROR Trust strict verification failed for `callable_handed_to_sysroot_is_charged::f`
//[reify_local]~v NOTE this function has no obligation of its own
pub fn f(b: u32) -> u32 {
    let p: fn(u32, u32) -> u32 = g;
    p(100, b)
}

#[cfg(fold_div_ceil)]
pub fn f(v: &[u32]) -> u32 { //[fold_div_ceil]~ ERROR Trust strict verification failed
    v.iter().copied().fold(7, u32::div_ceil)
}

#[cfg(reduce_pow)]
pub fn f(v: &[u32]) -> Option<u32> { //[reduce_pow]~ ERROR Trust strict verification failed
    v.iter().copied().reduce(u32::pow)
}

#[cfg(fold_signed_pow)]
pub fn f(v: &[u32]) -> i32 { //[fold_signed_pow]~ ERROR Trust strict verification failed
    v.iter().copied().fold(2i32, i32::pow)
}

#[cfg(try_fold_checked_pow)]
// ZERO-ROW-GATE (2026-10-10) refused this body while it published zero rows. Since the merge of
// 2026-10-14 the call carries the counted panic-freedom aggregate (the soundness line's
// carrier for a call into a bundled body), kept `runtime_checked`: `0 proved, 1
// runtime-checked`, a default-policy warning (measured on the merged stage 1, 2026-10-15).
// The gate is unchanged; the body is no longer zero-row.
pub fn f(v: &[u32]) -> Option<u32> {
    v.iter().copied().try_fold(2, u32::checked_pow)
}

#[cfg(fold_wrapping_pow)]
// ZERO-ROW-GATE (2026-10-10) refused this body while it published zero rows. Since the merge of
// 2026-10-14 the call carries the counted panic-freedom aggregate (the soundness line's
// carrier for a call into a bundled body), kept `runtime_checked`: `0 proved, 1
// runtime-checked`, a default-policy warning (measured on the merged stage 1, 2026-10-15).
// The gate is unchanged; the body is no longer zero-row.
pub fn f(v: &[u32]) -> u32 {
    v.iter().copied().fold(2, u32::wrapping_pow)
}

#[cfg(fold_div_operator)]
pub fn f(v: &[u32]) -> u32 { //[fold_div_operator]~ ERROR Trust strict verification failed
    v.iter().copied().fold(7u32, core::ops::Div::div)
}

#[cfg(fold_rem_operator_ref)]
pub fn f(v: &[u32]) -> u32 { //[fold_rem_operator_ref]~ ERROR Trust strict verification failed
    v.iter().fold(7u32, core::ops::Rem::rem)
}

#[cfg(fold_wrapping_div_operator)]
pub fn f(v: &[core::num::Wrapping<u32>]) -> core::num::Wrapping<u32> {
    //[fold_wrapping_div_operator]~^ ERROR Trust strict verification failed
    v.iter().copied().fold(core::num::Wrapping(7u32), core::ops::Div::div)
}

#[cfg(fold_nonzero_div_operator)]
pub fn f(v: &[core::num::NonZero<u32>]) -> u32 {
    v.iter().copied().fold(7u32, core::ops::Div::div)
}

#[cfg(fold_float_div_operator)]
pub fn f(v: &[f64]) -> f64 {
    v.iter().copied().fold(7.0, core::ops::Div::div)
}

#[cfg(map_sum_item_last)]
pub fn f(v: &[Vec<u32>]) -> Option<u32> {
    v.iter().map(|w| w.iter()).map(Iterator::sum::<u32>).last()
}

#[cfg(map_sum_ref_item_collect)]
pub fn f(v: &[Vec<u32>]) -> Vec<u32> {
    v.iter().map(|w| w.iter()).map(Iterator::sum::<u32>).collect()
}

#[cfg(option_map_sum_item)]
pub fn f(o: Option<Vec<u32>>) -> Option<u32> {
    o.map(Vec::into_iter).map(Iterator::sum::<u32>)
}

#[cfg(map_float_sum_item_last)]
pub fn f(v: &[Vec<f64>]) -> Option<f64> {
    v.iter().map(|w| w.iter()).map(Iterator::sum::<f64>).last()
}

#[cfg(map_count_item_collect)]
pub fn f(v: &[Vec<u32>]) -> Vec<usize> {
    v.iter().map(|w| w.iter()).map(Iterator::count).collect()
}

#[cfg(any(fold_add_operator_ref, fold_add_operator_ref_certify))]
pub fn f(v: &[u32]) -> u32 {
    //[fold_add_operator_ref,fold_add_operator_ref_certify]~^ ERROR Trust strict verification failed
    v.iter().fold(0u32, core::ops::Add::add)
}

#[cfg(fold_shl_operator_ref)]
pub fn f(v: &[u32]) -> u32 { //[fold_shl_operator_ref]~ ERROR Trust strict verification failed
    v.iter().fold(1u32, core::ops::Shl::shl)
}

#[cfg(map_neg_operator_ref_collect)]
pub fn f(v: &[i32]) -> Vec<i32> {
    //[map_neg_operator_ref_collect]~^ ERROR Trust strict verification failed
    v.iter().map(core::ops::Neg::neg).collect()
}

#[cfg(fold_wrapping_add_operator_ref)]
pub fn f(v: &[core::num::Wrapping<u32>]) -> core::num::Wrapping<u32> {
    v.iter().fold(core::num::Wrapping(0u32), core::ops::Add::add)
}

#[cfg(fold_float_add_operator_ref)]
pub fn f(v: &[f64]) -> f64 {
    v.iter().fold(0.0, core::ops::Add::add)
}

#[cfg(fold_bitand_operator_ref)]
pub fn f(v: &[u32]) -> u32 {
    v.iter().fold(u32::MAX, core::ops::BitAnd::bitand)
}

#[cfg(map_uninit_slice_item_collect)]
pub fn f(ns: &[usize]) -> usize {
    //[map_uninit_slice_item_collect]~^ ERROR Trust strict verification failed
    let v: Vec<Box<[core::mem::MaybeUninit<u64>]>> =
        ns.iter().copied().map(Box::<[u64]>::new_uninit_slice).collect();
    v.len()
}

#[cfg(map_zeroed_slice_item_collect)]
pub fn f(ns: &[usize]) -> usize {
    //[map_zeroed_slice_item_collect]~^ ERROR Trust strict verification failed
    let v: Vec<Box<[core::mem::MaybeUninit<u64>]>> =
        ns.iter().copied().map(Box::<[u64]>::new_zeroed_slice).collect();
    v.len()
}

#[cfg(map_rc_uninit_slice_item_len_collect)]
pub fn f(ns: &[usize]) -> Vec<usize> {
    //[map_rc_uninit_slice_item_len_collect]~^ ERROR Trust strict verification failed
    ns.iter().copied().map(std::rc::Rc::<[u64]>::new_uninit_slice).map(|r| r.len()).collect()
}

#[cfg(map_uninit_slice_item_count)]
pub fn f(ns: &[usize]) -> usize {
    //[map_uninit_slice_item_count]~^ ERROR Trust strict verification failed
    ns.iter().copied().map(Box::<[u64]>::new_uninit_slice).count()
}

#[cfg(option_map_uninit_slice_item)]
pub fn f(o: Option<usize>) -> bool {
    //[option_map_uninit_slice_item]~^ ERROR Trust strict verification failed
    o.map(Box::<[u64]>::new_uninit_slice).is_some()
}

#[cfg(closure_uninit_slice_collect)]
pub fn f(ns: &[usize]) -> usize {
    let v: Vec<Box<[core::mem::MaybeUninit<u64>]>> =
        ns.iter().map(|&n| Box::<[u64]>::new_uninit_slice(n)).collect();
    //[closure_uninit_slice_collect]~^ ERROR Trust strict verification failed
    v.len()
}

#[cfg(local_item_uninit_slice_collect)]
fn mk(n: usize) -> Box<[core::mem::MaybeUninit<u64>]> {
    //[local_item_uninit_slice_collect]~^ ERROR Trust strict verification failed
    Box::<[u64]>::new_uninit_slice(n)
}
#[cfg(local_item_uninit_slice_collect)]
pub fn f(ns: &[usize]) -> usize {
    let v: Vec<Box<[core::mem::MaybeUninit<u64>]>> = ns.iter().copied().map(mk).collect();
    v.len()
}

#[cfg(guarded_uninit_slice_direct)]
pub fn f(n: usize) -> Option<Box<[core::mem::MaybeUninit<u8>]>> {
    if n <= 4096 { Some(Box::<[u8]>::new_uninit_slice(n)) } else { None }
}

#[cfg(map_panic_any_item_collect)]
pub fn f(v: &[u32]) -> usize {
    //[map_panic_any_item_collect]~^ ERROR Trust strict verification failed
    let x: Vec<_> = v.iter().copied().map(std::panic::panic_any::<u32>).collect();
    x.len()
}

#[cfg(map_panic_any_item_count)]
pub fn f(v: &[u32]) -> usize {
    //[map_panic_any_item_count]~^ ERROR Trust strict verification failed
    v.iter().copied().map(std::panic::panic_any::<u32>).count()
}

#[cfg(option_map_panic_any_item)]
pub fn f(o: Option<u32>) -> bool {
    //[option_map_panic_any_item]~^ ERROR Trust strict verification failed
    o.map(std::panic::panic_any::<u32>).is_some()
}
