//@ revisions: panicking fn_ptr fn_item spoof_trait copied iter_mut ref_mut any_method drop_elem
//@ revisions: fold_drop_acc
//@ revisions: panicking_certify fn_ptr_certify user_iter_certify map_certify hash_map_certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[panicking_certify] compile-flags: -Ztrust-policy=certify
//@[fn_ptr_certify] compile-flags: -Ztrust-policy=certify
//@[user_iter_certify] compile-flags: -Ztrust-policy=certify
//@[map_certify] compile-flags: -Ztrust-policy=certify
//@[hash_map_certify] compile-flags: -Ztrust-policy=certify
//@[panicking] check-fail
//@[fn_ptr] check-fail
//@[fn_item] check-pass
//@[spoof_trait] check-fail
//@[copied] check-pass
//@[iter_mut] check-pass
//@[ref_mut] check-pass
//@[any_method] check-pass
//@[drop_elem] check-pass
//@[fold_drop_acc] check-pass
//@[panicking_certify] check-fail
//@[fn_ptr_certify] check-fail
//@[user_iter_certify] check-fail
//@[map_certify] check-fail
//@[hash_map_certify] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: HELP
//! ZERO-ROW-GATE recovery item 2, SLICE-ITER-CONSUMER: the shapes the lane must NOT
//! admit (twin of `slice_iter_consumer_local_closure_discharges.rs`). Each caller
//! below calls an `all`/`fold`/`any` that `collect_slice_iter_consumer_total_calls`
//! declines (its `TRUST_SLICE_ITER_CONSUMER_DEBUG` reason in brackets), so it keeps
//! its unproved row and the lane refuses it.
//!
//! Default lane. Each caller is a ZERO-ROW body that keeps the `unknown`
//! `native-verification-gap` row (the gate's note is required), except `fn_ptr` and
//! `spoof_trait`, whose callers carry a row of their own (the indirect call's, the
//! local `all`'s), so the lane is not what refuses them; they pin that it does not
//! admit them either. Since CALL-REACH-1 D6 (2026-10-13) `all`'s call walk opens at
//! the call through the handed pointer, so `fn_ptr_certify` also carries the Level 0
//! error of that withdrawn call's row. Except for `panicking`, `fn_ptr` and `spoof_trait`, the closure
//! itself IS registered panic-free, so only the named premise keeps the caller refused:
//! * `panicking`: a genuine slice `all` whose LOCAL closure can panic (a division by a
//!   slice element), so it never enters `panic_free_proven_funcs`
//!   [closure-not-proven-panic-free];
//! * `fn_ptr`: the "closure" is a fn-pointer argument [closure-not-a-closure];
//! * `fn_item`: a local fn ITEM, even a registered one [closure-not-a-closure];
//! * `spoof_trait`: a LOCAL trait named `Iterator` with a method `all`, implemented
//!   for `core::slice::Iter` with a panicking body: not the sysroot `Iterator`
//!   (the family test answers `None`), whatever it is called;
//! * `copied`: `Self` is `Copied<slice::Iter>` [self-not-slice-iter];
//! * `iter_mut`: `Self` is `slice::IterMut`, whose overrides were not read
//!   [self-not-slice-iter];
//! * `ref_mut`: `Self` is `&mut slice::Iter` (the blanket `impl Iterator for &mut I`,
//!   named explicitly: `(&mut it).all(..)` autorefs to `Self = Iter` and IS admitted,
//!   see the positive twin) [self-not-slice-iter];
//! * `any_method`: a method outside the admitted pair (`None`);
//! * `drop_elem`: the element type has drop glue [element-needs-drop];
//! * `fold_drop_acc`: `fold`'s accumulator has drop glue [accumulator-needs-drop].
//!
//! Certify lane: shapes whose caller carries a `runtime_checked` row (a user iterator
//! whose `next` can panic, `Map` over a panicking closure, a `HashMap` iterator), which
//! the default lane accepts as runtime-checked before and after this lane; certify
//! refuses them, and this lane must not turn them into `no_obligations`.
//!
//! Mutation-checked (DECISION_QUEUE SLICE-ITER-CONSUMER): dropping the registry test
//! flips `panicking`; dropping the `SliceIter` `Self` test (and the resolved-impl
//! drift pin) flips `copied`/`iter_mut`/`ref_mut`; dropping the drop-glue tests flips
//! `drop_elem`/`fold_drop_acc`.
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14; DECISION_QUEUE D103): `copied`,
//! `iter_mut`, `ref_mut`, `fn_item`, `any_method`, `drop_elem` and `fold_drop_acc` now
//! BUILD (`check-pass`). This lane still declines each of them, for the reason in
//! brackets above; what admits them is the soundness line's drive-only consumer lane
//! (`collect_verified_callable_consumer_total_calls`: a total std receiver, items that
//! need no drop, and a callable whose own verdict discharges it — each one here is a
//! correct program), whose decision the zero-obligation gate now reads too
//! (VERIFIED-CALLABLE-ZERO-ROW-PARITY), as it reads this lane's. `ref_mut` builds
//! through the bundled `all`'s `runtime_checked` aggregate instead. `panicking`,
//! `fn_ptr`, `spoof_trait` and the certify-lane shapes stay refused, so the mutation
//! checks above now flip only `panicking`.

#[cfg(any(panicking, panicking_certify))]
pub fn all_divides(xs: &[u32]) -> bool {
    //[panicking_certify]~^ ERROR Trust strict verification failed for `slice_iter_consumer_refusals::all_divides`
    //[panicking_certify]~| ERROR Trust Level 0 safety verification incomplete for `slice_iter_consumer_refusals::all_divides`
    // Since the merge of 2026-10-14 `all_divides` is no longer a zero-obligation body: it
    // carries the counted panic-freedom aggregate for its bundled `all`, read `1
    // runtime-checked`. `certify` refuses that row (above); `panicking` reports it as a
    // default-policy warning, and the panicking closure is refused as its own root below,
    // so neither build succeeds (measured on the merged stage 1, 2026-10-15).
    xs.iter().all(|&x| 100 / x > 1)
    //[panicking,panicking_certify]~^ ERROR Trust Level 0 safety verification incomplete for `slice_iter_consumer_refusals::all_divides::{closure#0}`
    //[panicking,panicking_certify]~| ERROR Trust strict verification failed for `slice_iter_consumer_refusals::all_divides::{closure#0}`
}

#[cfg(any(fn_ptr, fn_ptr_certify))]
pub fn all_by(xs: &[f64], f: fn(&f64) -> bool) -> bool {
    //[fn_ptr,fn_ptr_certify]~^ ERROR Trust strict verification failed for `slice_iter_consumer_refusals::all_by`
    //[fn_ptr_certify]~| ERROR Trust Level 0 safety verification incomplete for `slice_iter_consumer_refusals::all_by`
    xs.iter().all(f)
}

#[cfg(fn_item)]
fn is_fin(x: &f64) -> bool {
    x.is_finite()
}

#[cfg(fn_item)]
pub fn all_by_item(xs: &[f64]) -> bool {
    // (re-pinned 2026-10-15)
    // (re-pinned 2026-10-15)
    xs.iter().all(is_fin)
}

#[cfg(spoof_trait)]
pub trait Iterator {
    fn all<F: FnMut(&f64) -> bool>(&mut self, f: F) -> bool;
}

#[cfg(spoof_trait)]
impl<'a> Iterator for core::slice::Iter<'a, f64> {
    fn all<F: FnMut(&f64) -> bool>(&mut self, _f: F) -> bool {
        //[spoof_trait]~^ ERROR Trust Level 0 safety verification incomplete for `<core::slice::iter::Iter<'_, f64> as slice_iter_consumer_refusals::Iterator>::all`
        //[spoof_trait]~| ERROR Trust strict verification failed for `<core::slice::iter::Iter<'_, f64> as slice_iter_consumer_refusals::Iterator>::all`
        panic!("spoofed `all`")
    }
}

#[cfg(spoof_trait)]
pub fn spoofed_all(xs: &[f64]) -> bool {
    //[spoof_trait]~^ ERROR Trust strict verification failed for `slice_iter_consumer_refusals::spoofed_all`
    Iterator::all(&mut xs.iter(), |x| x.is_finite())
}

#[cfg(copied)]
pub fn copied_all(xs: &[f64]) -> bool {
    // (re-pinned 2026-10-15)
    // (re-pinned 2026-10-15)
    xs.iter().copied().all(|x| x.is_finite())
}

#[cfg(iter_mut)]
pub fn iter_mut_all(xs: &mut [f64]) -> bool {
    // (re-pinned 2026-10-15)
    // (re-pinned 2026-10-15)
    xs.iter_mut().all(|x| x.is_finite())
}

#[cfg(ref_mut)]
pub fn ref_mut_all(xs: &[f64]) -> bool {
    // Refused by ZERO-ROW-GATE while it was a zero-obligation body (this lane does not
    // credit a `&mut Iter` receiver). Since the merge of 2026-10-14 the `all` call
    // carries the counted panic-freedom aggregate, kept `runtime_checked`: `0 proved, 1
    // runtime-checked`, which the default lane accepts as the header says (measured on
    // the merged stage 1, 2026-10-15). The lane still credits nothing here.
    let mut it = xs.iter();
    let mut by_ref = &mut it;
    <&mut core::slice::Iter<'_, f64> as Iterator>::all(&mut by_ref, |x| x.is_finite())
}

#[cfg(any_method)]
pub fn any_finite(xs: &[f64]) -> bool {
    // (re-pinned 2026-10-15)
    // (re-pinned 2026-10-15)
    xs.iter().any(|x| x.is_finite())
}

#[cfg(drop_elem)]
pub struct Guard(pub u32);

#[cfg(drop_elem)]
impl Drop for Guard {
    fn drop(&mut self) {}
}

#[cfg(drop_elem)]
pub fn guards_positive(xs: &[Guard]) -> bool {
    // (re-pinned 2026-10-15)
    // (re-pinned 2026-10-15)
    xs.iter().all(|g| g.0 > 0)
}

#[cfg(fold_drop_acc)]
pub fn fold_into_vec(xs: &[u32]) -> Vec<u32> {
    // (re-pinned 2026-10-15)
    // (re-pinned 2026-10-15)
    xs.iter().fold(Vec::new(), |acc, _| acc)
}

#[cfg(user_iter_certify)]
pub struct Countdown(pub u32);

#[cfg(user_iter_certify)]
impl core::iter::Iterator for Countdown {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        //[user_iter_certify]~^ ERROR Trust Level 0 safety verification incomplete for `<slice_iter_consumer_refusals::Countdown as core::iter::traits::iterator::Iterator>::next`
        //[user_iter_certify]~| ERROR Trust strict verification failed for `<slice_iter_consumer_refusals::Countdown as core::iter::traits::iterator::Iterator>::next`
        self.0 -= 1;
        Some(100 / self.0)
    }
}

#[cfg(user_iter_certify)]
pub fn all_countdown(c: &mut Countdown) -> bool {
    //[user_iter_certify]~^ ERROR Trust Level 0 safety verification incomplete for `slice_iter_consumer_refusals::all_countdown`
    //[user_iter_certify]~| ERROR Trust strict verification failed for `slice_iter_consumer_refusals::all_countdown`
    c.all(|x| x > 0)
}

#[cfg(map_certify)]
pub fn map_all(xs: &[u32]) -> bool {
    //[map_certify]~^ ERROR Trust Level 0 safety verification incomplete for `slice_iter_consumer_refusals::map_all`
    //[map_certify]~| ERROR Trust strict verification failed for `slice_iter_consumer_refusals::map_all`
    xs.iter().map(|&x| 100 / x).all(|y| y > 0)
    //[map_certify]~^ ERROR Trust Level 0 safety verification incomplete for `slice_iter_consumer_refusals::map_all::{closure#0}`
    //[map_certify]~| ERROR Trust strict verification failed for `slice_iter_consumer_refusals::map_all::{closure#0}`
}

#[cfg(hash_map_certify)]
pub fn values_positive(m: &std::collections::HashMap<u32, u32>) -> bool {
    //[hash_map_certify]~^ ERROR Trust Level 0 safety verification incomplete for `slice_iter_consumer_refusals::values_positive`
    //[hash_map_certify]~| ERROR Trust strict verification failed for `slice_iter_consumer_refusals::values_positive`
    m.values().all(|&v| v > 0)
}
