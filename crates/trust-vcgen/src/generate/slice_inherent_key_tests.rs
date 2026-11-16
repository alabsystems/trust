//! Trust (2026-10-04, SLICE-INHERENT-1): a `<[T]>` inherent method is std's only
//! when its callee is DEFINED in a real sysroot crate (the compiler-minted
//! `callee_key`) and generic-strips to `core::slice::{method}`. Pinned on REAL
//! extracted MIR.
//!
//! `iterator_yield::vc_callee_is_slice_inherent` accepted `[T]` ANYWHERE in the
//! rendering plus a `::{method}` leaf. A user method whose OWNER is instantiated at
//! a slice renders exactly that: `impl<S: ?Sized, A> W<S, A> { fn windows(&self,
//! n: usize) -> It }` called in `fn win<T>(w: &W<[T]>)` is
//! `slicet::W::<[T]>::windows`. Every consumer then minted std's yield fact for the
//! user's iterator. Measured on `scratchpad/stage1-w11fix` (2026-10-04, default
//! policy), with `It` yielding a one-element slice twice and `Many` yielding 300
//! items:
//!
//!  * `win` (`for win in w.windows(3) { s = win[2] }`) and `chx`
//!    (`chunks_exact(4)`, `c[3]`): `slice proved` — `len(win) == 3` from
//!    `build_slice_iter_yield_guard_map`;
//!  * `en` (`for (i, _) in W::<[T], &[T]>::iter(s).enumerate() { s[i] }`):
//!    `slice proved` — `i < len(s)` from `build_enumerate_yield_guard_map`;
//!  * `trip` (`for _ in W::<[T], &[T; 4]>::iter(s) { acc += 1 }`, `acc: u8`):
//!    `overflow:add proved` and the check ELIDED — a trip count of 4 from
//!    `loop_bounds::trace_iter_to_into_iter_arg`.
//!
//! The std controls `win_std`, `en_std` and `trip_std` (`core::slice::<impl
//! [u8]>::windows`, `core::slice::<impl [T]>::iter`, `core::slice::<impl
//! [u8]>::iter`, all keyed `krate_is_real_sysroot: true`) keep their facts.

use trust_types::{CalleeKey, Terminator, Ty, VerifiableFunction};

use super::build_slice_iter_yield_guard_map;
use crate::generate::iterator_yield::{
    build_enumerate_yield_guard_map, vc_callee_is_slice_inherent,
};
use crate::generate::loop_bounds::next_call_to_array_operand;

fn key(real_sysroot: bool) -> CalleeKey {
    CalleeKey {
        sysroot_item: None,
        krate_is_real_sysroot: real_sysroot,
        krate_name_is_ambiguous: false,
        stable_crate_id: 0x1234,
        krate_name: if real_sysroot { "core".into() } else { "slicet".into() },
        foreign_block_leaf: None,
        upstream_foreign_link_symbol: None,
        diverging_entry: None,
    }
}

fn load(mir: &str) -> VerifiableFunction {
    serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
}

/// The destination local of the (only) `Iterator::next` call.
fn next_dest(func: &VerifiableFunction) -> usize {
    func.body
        .blocks
        .iter()
        .find_map(|b| match &b.terminator {
            Terminator::Call { func: callee, dest, .. }
                if callee.ends_with("core::iter::traits::iterator::Iterator>::next") =>
            {
                Some(dest.local)
            }
            _ => None,
        })
        .expect("the fixture has a `next` call")
}

/// Does the trip-count tracer reach a builtin array or slice (the operand whose
/// length bounds the loop) from the loop's `next` call?
fn trip_reaches_a_builtin_collection(func: &VerifiableFunction) -> bool {
    let Some(op) = next_call_to_array_operand(func, next_dest(func), 16) else { return false };
    let Some(ty) = crate::operand_ty_cow(func, &op) else { return false };
    let ty = match ty.as_ref() {
        Ty::Ref { inner, .. } => inner.as_ref().clone(),
        other => other.clone(),
    };
    matches!(ty, Ty::Array { .. } | Ty::Slice { .. })
}

#[test]
fn slice_inherent_requires_a_real_sysroot_key_and_the_core_slice_path() {
    // The user spellings, with the key the extractor mints for them.
    for (callee, method) in [
        ("slicet::W::<[T]>::windows", "windows"),
        ("slicet::W::<[T]>::chunks_exact", "chunks_exact"),
        ("slicet::W::<[T], &[T]>::iter", "iter"),
        ("slicet::W::<[T], &[T; 4]>::iter", "iter"),
    ] {
        assert!(!vc_callee_is_slice_inherent(callee, Some(&key(false)), method), "{callee}");
        // Even a (forged) sysroot key does not make a user path std's: the `[T]`
        // arm is gone, and the path does not strip to `core::slice::`.
        assert!(!vc_callee_is_slice_inherent(callee, Some(&key(true)), method), "{callee}");
    }
    for (callee, method) in [
        ("core::slice::<impl [u8]>::windows", "windows"),
        ("core::slice::<impl [T]>::iter", "iter"),
        ("core::slice::<impl [u8]>::iter", "iter"),
        ("core::slice::<impl [T]>::chunks_exact", "chunks_exact"),
    ] {
        assert!(vc_callee_is_slice_inherent(callee, Some(&key(true)), method), "{callee}");
        assert!(!vc_callee_is_slice_inherent(callee, Some(&key(false)), method), "{callee}");
        assert!(!vc_callee_is_slice_inherent(callee, None, method), "{callee}: no key");
    }
    // A trait method is never an inherent slice method.
    assert!(!vc_callee_is_slice_inherent(
        "<[T] as mycrate::Trait>::windows",
        Some(&key(true)),
        "windows"
    ));
}

#[test]
fn user_windows_and_chunks_exact_mint_no_yield_length_on_real_mir() {
    for (name, mir) in [("win", MIR_WIN), ("chx", MIR_CHX)] {
        let map = build_slice_iter_yield_guard_map(&load(mir));
        assert!(
            map.values().all(Vec::is_empty),
            "{name}: a user iterator got std's length: {map:?}"
        );
    }
    let map = build_slice_iter_yield_guard_map(&load(MIR_WIN_STD));
    assert!(map.values().any(|v| !v.is_empty()), "win_std: std's `windows` lost its length");
}

#[test]
fn user_iter_enumerate_mints_no_index_bound_on_real_mir() {
    let map = build_enumerate_yield_guard_map(&load(MIR_EN));
    assert!(map.values().all(Vec::is_empty), "en: a user iterator got `i < len(s)`: {map:?}");
    let map = build_enumerate_yield_guard_map(&load(MIR_EN_STD));
    assert!(map.values().any(|v| !v.is_empty()), "en_std: std's enumerate lost its bound");
}

#[test]
fn user_iter_gets_no_trip_count_on_real_mir() {
    assert!(
        !trip_reaches_a_builtin_collection(&load(MIR_TRIP)),
        "trip: a user `W::<[T], &[T; 4]>::iter` was read as a 4-trip loop"
    );
    assert!(
        trip_reaches_a_builtin_collection(&load(MIR_TRIP_STD)),
        "trip_std: `s.iter()` no longer reaches `s`"
    );
}

/// The fixture calls `slicet::W::<[T]>::windows` with a key that is NOT real
/// sysroot, and `std`'s `windows` with one that is — the facts the tests above
/// depend on, asserted so a re-capture that changes them is loud.
#[test]
fn the_captured_keys_are_what_the_extractor_mints() {
    let key_of = |func: &VerifiableFunction, needle: &str| {
        func.body.blocks.iter().find_map(|b| match &b.terminator {
            Terminator::Call { func: callee, callee_key, .. } if callee.contains(needle) => {
                Some(callee_key.clone())
            }
            _ => None,
        })
    };
    let user = key_of(&load(MIR_WIN), "::windows").expect("win calls windows");
    assert!(user.is_some_and(|k| !k.krate_is_real_sysroot));
    let std = key_of(&load(MIR_WIN_STD), "::windows").expect("win_std calls windows");
    assert!(std.is_some_and(|k| k.krate_is_real_sysroot));
}

/// REAL extracted MIR (`-Ztrust-dump=mir:<dir>`, `scratchpad/stage1-w11fix`,
/// 2026-10-04) of `slicet.rs` (crate `slicet`), under
/// `tests/fixtures/vcgen_recognizer_anchor/`:
///
/// ```text
/// pub struct W<S: ?Sized, A = ()>(pub u8, pub PhantomData<A>, pub PhantomData<S>);
/// impl<S: ?Sized, A> W<S, A> {
///     pub fn windows(&self, _n: usize) -> It { It { n: 0 } }        // yields &ONE[..] twice
///     pub fn chunks_exact(&self, _n: usize) -> It { It { n: 0 } }
///     pub fn iter(_a: A) -> Many { Many { n: 0 } }                    // yields 300 items
/// }
/// pub fn win<T>(w: &W<[T]>) -> u8 { let mut s = 0u8; for win in w.windows(3) { s = win[2]; } s }
/// pub fn chx<T>(w: &W<[T]>) -> u8 { let mut s = 0u8; for c in w.chunks_exact(4) { s = c[3]; } s }
/// pub fn en<T: Copy>(s: &[T]) -> Option<T> {
///     let mut r = None; for (i, _) in W::<[T], &[T]>::iter(s).enumerate() { r = Some(s[i]); } r }
/// pub fn trip<T>(s: &[T; 4]) -> u8 {
///     let mut acc = 0u8; for _ in W::<[T], &[T; 4]>::iter(s) { acc += 1; } acc }
/// pub fn win_std(s: &[u8]) -> u8 { let mut r = 0u8; for w in s.windows(3) { r = w[2]; } r }
/// pub fn en_std<T: Copy>(s: &[T]) -> Option<T> {
///     let mut r = None; for (i, _) in s.iter().enumerate() { r = Some(s[i]); } r }
/// pub fn trip_std(s: &[u8]) -> u64 { let mut acc = 0u64; for _ in s.iter() { acc += 1; } acc }
/// ```
const MIR_WIN: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/slice_win_mir.json");
const MIR_CHX: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/slice_chx_mir.json");
const MIR_EN: &str = include_str!("../../tests/fixtures/vcgen_recognizer_anchor/slice_en_mir.json");
const MIR_TRIP: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/slice_trip_mir.json");
const MIR_WIN_STD: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/slice_win_std_mir.json");
const MIR_EN_STD: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/slice_en_std_mir.json");
const MIR_TRIP_STD: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/slice_trip_std_mir.json");
