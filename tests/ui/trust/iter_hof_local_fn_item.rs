//@ revisions: map_item_collect map_item_result map_assoc_item fn_item_panics generic_item
//@ revisions: self_recursion_item mutual_recursion_item
//@ revisions: sum_local_item_overflow sum_sysroot_item_overflow
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[map_item_collect] check-pass
//@[map_item_result] check-fail
//@[map_assoc_item] check-pass
//@[fn_item_panics] check-fail
//@[generic_item] check-fail
//@[self_recursion_item] check-pass
//@[mutual_recursion_item] check-fail
//@[sum_local_item_overflow] check-fail
//@[sum_sysroot_item_overflow] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! W4 ITER-HOF (b): a LOCAL function item handed where a closure goes.
//!
//! MEASURED OVER-REFUSAL (unaimed-90 d0/p06, d5/p07; `d0/v/m2.rs` vs `m3.rs`):
//! `s.split(' ').map(|w| ident(w)).collect()` built while `s.split(' ')
//! .map(ident).collect()` was refused. The `DefId` lane's HOF arm offered only
//! `ty::Closure` arguments for bundling, so `ident`'s body was never in the
//! bundle; the adapter's `next`, which calls it through
//! `<fn(&str) -> String {ident} as FnMut<(&str,)>>::call_mut`, failed to lower
//! ("resolved function item `ident`, but its body is not present"), the consumer
//! was evicted, and the root was left with an ABSENT `collect` whose `F` is a
//! user item — `NOT-VANILLA`, fatal. The item is now offered exactly like a
//! closure; the bridge already resolves that shim to the NAMED body.
//!
//! Second half of the same class: the collect's allocation count. The std-adaptor
//! authenticator read the `>` of the fn item's `->` as a closing bracket, so
//! `map::<String, for<'_> fn(&'_ str) -> String {ident}>` was not recognized as
//! std's `map` and the bounded-source walk minted
//! `UnboundedAllocation::Iterator::collect::count-not-derivable` — a row with no
//! runtime fallback.
//!
//! Soundness half: `fn_item_panics` hands over an item that CAN panic; the build
//! must still be refused. The refusal lands on the item, which is verified as its
//! own root, and the caller carries the tolerated closure-consumer row — exactly
//! what the closure spelling `.map(|w| w.as_bytes()[0])` has always produced.
//! `generic_item` is the half the W4 self-check added: a GENERIC local item is
//! verified per INSTANCE only (docs/TCB.md), and the instance handed to `map` is
//! instantiated by no lane of this compilation, so the caller is refused on the
//! unresolved callable (`local_fn_item_type_arg_is_unverified_instance`) — the
//! generic item itself verifies clean here, so that is the only error.
//!
//! BEFORE (stage-1 snapshot `fb304b993`, two commits behind this branch's base
//! `3b30328c07`; neither intervening commit touches these lanes): all five
//! revisions refused.
//!
//! Termination through a handed-over item (W4 ITER-HOF fix rounds, 2026-10-01).
//! An item handed to a HOF is a real call edge of the caller (the HOF arm feeds
//! the local call graph), so recursion that runs ONLY through such an edge is
//! charged the way main charges every other re-entry:
//!  * `mutual_recursion_item` (adversarial probe p15, a stack overflow at run
//!    time): `f` hands `g` to `Option::map` and `g` calls `f` — the cycle is a
//!    recursion SCC, and both members carry the unmeasured `[termination]`
//!    obligation (c927d6fd7f), so the build is refused.
//!  * `self_recursion_item` (adversarial probe i24): `g` hands ITSELF to
//!    `Option::and_then`. That is D9's self-reference census (`map(f)` is one of
//!    its named shapes): an `assumption:termination-unmeasured` row, CONDITIONAL on
//!    the default lane and refused by `certify`, with the advisory pinned below —
//!    exactly what main gives the reified spelling `let p: fn(u32) -> Option<u32>
//!    = g; p(x)` (measured rc=0 with the same advisory on main `07091c92c1`). Before
//!    W4 the item spelling was refused only because `and_then` over a local item
//!    was an absent `NOT-VANILLA` callee.
//!
//! A FALSE ACCEPT ON MAIN that the same arrow repair closes (found by this item's
//! fix round 2, 2026-10-01). `v.iter().copied().map(neg).sum::<u32>()` with a local
//! `fn neg(x: u32) -> u32 { x.wrapping_neg() }` (`sum_local_item_overflow`), and
//! the same with the sysroot item `u32::wrapping_neg` (`sum_sysroot_item_overflow`),
//! built rc=0 on main `07091c92c1` and panicked at run time ("attempt to add with
//! overflow" in core's `accum.rs`, `f(&[1, 1])`, verify-off driver exit 101), while
//! the closure spelling `.map(|x| x.wrapping_neg()).sum()` was refused on F4's
//! `iterator-fold-overflow` row. F4's integer-fold recognizer reads the qualified
//! `<Map<Copied<Iter<'_, u32>>, fn(u32) -> u32 {neg}> as Iterator>::sum::<u32>`
//! through vcgen's `vc_qualifier_group`, which closed the qualifier at the arrow's
//! `>` — so for a fn-item `F` it matched nothing and no row was minted. With the
//! arrow read as text all three spellings carry the row and are refused.

#[cfg(map_item_collect)]
fn ident(word: &str) -> String {
    word.to_string()
}

#[cfg(map_item_collect)]
pub fn f(s: &str) -> Vec<String> {
    s.split(' ').map(ident).collect()
}

#[cfg(map_item_result)]
#[derive(PartialEq)]
pub enum ScoreError {
    NotANumber,
    OutOfRange(u32),
}

#[cfg(map_item_result)]
fn parse_score(s: &str) -> Result<u32, ScoreError> {
    let n: u32 = s.trim().parse().map_err(|_| ScoreError::NotANumber)?;
    if n > 100 {
        return Err(ScoreError::OutOfRange(n));
    }
    Ok(n)
}

// Trust (POISON-EVICTION-FALSE-PROOF-1, 2026-11-12): RE-PINNED from check-pass. `f`
// passed only while the poison loop evicted members a retained body still called, and
// those withdrawn calls took credit. The loop now keeps them. MEASURED with
// `TRUST_MEMBER_PANIC_CENSUS=1` on this branch's stage 1: `evicting=[]`, and seven
// kept members, each `called by` or `named by` a retained body: `Map::size_hint`,
// `Result::from_iter`, `Global::alloc_impl_runtime`, `Global::grow_impl_runtime`,
// `RawVecInner::grow_amortized`, `panic_fmt` and `panic_nounwind_fmt`. Their absent
// callees include generic ones (`NonNull::<T>::…` in `alloc_impl_runtime`), which keep
// the default policy fail-closed. The lost admission is docs/DECISION_QUEUE.md
// POISON-EVICTION-KEEP-1.
#[cfg(map_item_result)]
pub fn f(input: &str) -> Result<Vec<u32>, ScoreError> {
    //[map_item_result]~^ ERROR Trust strict verification failed for `iter_hof_local_fn_item::f`
    //[map_item_result]~| NOTE a generic absent callee — keeps the function fail-closed
    input.split(',').map(parse_score).collect()
}

#[cfg(map_assoc_item)]
pub struct Words;

#[cfg(map_assoc_item)]
impl Words {
    fn width(w: &str) -> usize {
        w.len()
    }
}

#[cfg(map_assoc_item)]
pub fn f(s: &str) -> Vec<usize> {
    s.split(' ').map(Words::width).collect()
}

// `"a  b".split(' ')` yields an empty piece, and `first_byte("")` indexes out of
// bounds.
#[cfg(fn_item_panics)]
fn first_byte(w: &str) -> u8 { //[fn_item_panics]~ ERROR Trust strict verification failed
    w.as_bytes()[0]
}

#[cfg(fn_item_panics)]
pub fn f(s: &str) -> Vec<u8> {
    s.split(' ').map(first_byte).collect()
}

#[cfg(generic_item)]
fn first<T: Copy>(pair: &(T, T)) -> T {
    pair.0
}

#[cfg(generic_item)]
pub fn f(v: &[(u32, u32)]) -> Vec<u32> { //[generic_item]~ ERROR Trust
    v.iter().map(first::<u32>).collect()
}

#[cfg(self_recursion_item)]
fn g(x: u32) -> Option<u32> {
    //[self_recursion_item]~^ WARN termination is ASSUMED, not proved
    Some(x).and_then(g)
}

#[cfg(self_recursion_item)]
pub fn f(x: u32) -> Option<u32> {
    g(x)
}

#[cfg(mutual_recursion_item)]
pub fn f(x: Option<u32>) -> Option<u32> {
    //[mutual_recursion_item]~^ ERROR Trust strict verification failed
    x.map(g)
}

#[cfg(mutual_recursion_item)]
fn g(x: u32) -> u32 {
    //[mutual_recursion_item]~^ ERROR Trust strict verification failed
    match f(Some(x)) {
        Some(y) => y,
        None => 0,
    }
}

#[cfg(sum_local_item_overflow)]
fn neg(x: u32) -> u32 {
    x.wrapping_neg()
}

#[cfg(sum_local_item_overflow)]
pub fn f(v: &[u32]) -> u32 {
    //[sum_local_item_overflow]~^ ERROR Trust strict verification failed
    v.iter().copied().map(neg).sum()
}

#[cfg(sum_sysroot_item_overflow)]
pub fn f(v: &[u32]) -> u32 {
    //[sum_sysroot_item_overflow]~^ ERROR Trust strict verification failed
    v.iter().copied().map(u32::wrapping_neg).sum()
}
