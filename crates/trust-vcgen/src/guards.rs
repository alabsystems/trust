// ignore-tidy-file-filelength -- pre-existing size, recorded 2026-08-21; do not grow casually
// trust_vcgen/guards.rs: Guard condition extraction and VC assumption threading
//
// Converts GuardCondition (from MIR control flow) into Formula assumptions.
// When a VC is generated inside a guarded block, the guard conditions on
// the path to that block become assumptions: guard => vc_formula.
//
// Part of #21: Guard condition extraction and clause discovery from MIR.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Known limitation: path_map() in trust-types uses first-predecessor-wins
// for guard accumulation at join points. A block reachable from multiple
// branches may only have one branch's guards, which is not a proof-grade
// encoding of join reachability. Ambiguous joins need disjunctive path
// conditions that cover all incoming guarded paths; until then, callers
// must conservatively use true/unknown instead of assuming one predecessor's
// guard is the complete path condition.
// See trust-types/src/model.rs path_map() for details.

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    AggregateKind, BasicBlock, BinOp, BlockId, ConstValue, Formula, GuardCondition, Operand,
    RoundingMode, Rvalue, Sort, Statement, Terminator, Ty, VerifiableFunction,
};
#[cfg(test)]
use trust_types::{AssertMessage, LocalDecl, Place, SourceSpan, VerifiableBody};

use crate::range::{type_max_formula, type_min_formula};
use crate::{
    ArrayReadCtx, ArrayVersionCtx, operand_to_formula, operand_to_formula_with_array_ctx,
    slice_len_formula, unsigned_value_to_formula,
};

// ─────────────────────────────────────────────────────────────────────────────
// Crate-origin anchors for the callee-name-keyed fact producers in this file
// (round-5 false-proof close). A GENUINE primitive/std callee renders CRATE-ROOTED
// — `core::slice::<impl [T]>::…`, `std::vec::Vec::<T>::…`, `core::str::<impl str>::…`,
// `core::num::<impl iN>::…`, `<T as core::ops::…>::m` — none of which a user free fn
// (`mycrate::…`) nor a user-trait impl (`<T as mycrate::…>::m`, carrying ` as mycrate`)
// can spell. These MIRROR the generate.rs round-4 helpers
// (`callee_is_std_slice_inherent`, `callee_is_std_vec_inherent`, `is_std_num_intrinsic`)
// and the shared `trust_types::total_call_summaries` doctrine, kept local so this file's
// forgery-rejection is self-contained. Fail-closed on a miss: a missed anchor just
// leaves the honest runtime-checked obligation (a missed proof, never a wrong one).
// `alloc`/`std`/`core` are foreign crates a user cannot shadow (the `--crate-name`
// literal attack is the accepted doctrine boundary, same as the mirrored helpers).

/// MIRROR of `generate::callee_is_std_vec_inherent`: an INHERENT method on the
/// std/alloc `Vec` type (`alloc::vec::Vec::<T>::…`, `std::vec::Vec::<T, A>::…`, the
/// UFCS `<alloc::vec::Vec<T>>::…`). Rejects a user free fn (no `alloc`/`std` root,
/// e.g. `userlib::Vec::<u32>::as_mut_slice`) and a user-trait impl on `Vec` (` as `).
fn callee_is_std_vec_inherent(callee: &str) -> bool {
    if callee.contains(" as ") {
        return false;
    }
    let c = callee.strip_prefix('<').unwrap_or(callee);
    c.starts_with("alloc::vec::Vec") || c.starts_with("std::vec::Vec")
}

/// MIRROR of `generate::callee_is_std_slice_inherent`: an INHERENT primitive-slice
/// method whose def-path ends in one of `suffixes` — `core::slice::<impl [T]>::…`
/// (crate root) or the bare inherent UFCS `<[T]>::…`. Rejects the free fn and the
/// ` as `-qualified user-trait impl on `[T]`.
fn callee_is_std_slice_inherent(callee: &str, suffixes: &[&str]) -> bool {
    if !suffixes.iter().any(|s| callee.ends_with(s)) {
        return false;
    }
    if callee.contains(" as ") {
        return false;
    }
    callee.starts_with("core::slice::")
        || callee.starts_with("std::slice::")
        || callee.starts_with("<[")
}

/// Companion for the INHERENT `str`/`String` methods (`is_empty`, `as_bytes`) whose
/// crate roots the slice/Vec mirrors do not cover. Genuine renderings:
/// `core::str::<impl str>::as_bytes`, `<str>::is_empty`,
/// `alloc::string::String::as_bytes`, `std::string::String::is_empty`. Rejects the
/// free fn (`mycrate::as_bytes`) and the ` as `-qualified user-trait UFCS.
fn callee_is_std_str_inherent(callee: &str, suffixes: &[&str]) -> bool {
    if !suffixes.iter().any(|s| callee.ends_with(s)) {
        return false;
    }
    if callee.contains(" as ") {
        return false;
    }
    callee.starts_with("core::str::")
        || callee.starts_with("std::str::")
        || callee.starts_with("alloc::str::")
        || callee.starts_with("<str")
        || callee.starts_with("alloc::string::String")
        || callee.starts_with("std::string::String")
}

/// MIRROR of `generate::is_std_num_intrinsic`: a `core::num::<impl iN>::…` /
/// `std::num::…` inherent — the un-forgeable `::num::` std segment under a core/std
/// crate root. A user `fn checked_add(..)->Option<..>` renders `mycrate::checked_add`
/// (no `::num::` under a std root) and is DECLINED.
fn is_std_num_intrinsic(callee: &str) -> bool {
    (callee.starts_with("core::") || callee.starts_with("std::")) && callee.contains("::num::")
}

/// A GENUINE length-PRESERVING deref/view hop for the base-collection tracer
/// ([`base_collection_step`]): std's OWN `Vec`/`String` `Deref::deref`/
/// `DerefMut::deref_mut` (the `*v` of a `Vec`/`String`) or the inherent
/// `Vec::as_slice`/`as_mut_slice`, called on `receiver` (the call's projection-free
/// first argument). The result and the receiver denote the SAME sequence with
/// IDENTICAL length, so tracing the result's length to the receiver's base is sound.
/// The bare `method_tail` match this backs admitted a user `fn as_slice(v:&Vec<T>)->&[T]`
/// (renders `userlib::…::as_slice` / `mycrate::as_slice`) that returns a
/// DIFFERENT-length view → the tie then discharges an OOB index on the view.
/// Fail-closed on a miss.
///
/// Trust (2026-10-04, DEREF-ANCHOR-1): the `deref`/`deref_mut` arm took
/// `callee_is_std_ops_method`, which checked only that the TRAIT is std's (removed
/// once this arm and STD-RECEIVER-ANCHOR-1 left it without a caller). A user
/// `impl Deref for Wrap { type Target = Vec<u32>; .. }` passes that (the callee is
/// `<m::Wrap as core::ops::deref::Deref>::deref`, keyed on core's trait-method DefId),
/// and its `deref` may return a different `Vec` on every call. Both `w.len()` results
/// were tied to one `coll_len(w)`, so `if w.len() == 0 { return 0; } w.len() - 1` read
/// `overflow:sub` Certified, the check was elided, and the program returned `usize::MAX`
/// where vanilla Rust panics (measured on the stage 1 of `38e6c69b1c` under default,
/// strict, certify and memory-safe; also `Target = String` and a two-level user hop).
/// The arm now requires BOTH:
///  * the callee spells std's own `Vec`/`String` `Deref`/`DerefMut` exactly
///    ([`std_container_deref_self`]); and
///  * the receiver's pointee type, read from the MIR, is that same std container
///    ([`deref_receiver_is_std_container`]) — the `Deref` twin of
///    `call_facts::primitive_int_ord_method`, which pins `Self` from MIR types for
///    `Ord::min`.
///
/// `Deref` has no type parameter, so for a receiver that IS std's `Vec` or `String` the
/// orphan rule leaves std's impl as the only `Deref` impl; the spelling then rules out
/// a user trait method that is merely named `deref`. "IS std's" rests on the receiver's
/// MIR type, not on the callee: in a `#![no_std]` graph a dependency built
/// `--crate-name alloc` spells `<alloc::vec::Vec<u32> as core::ops::deref::Deref>::deref`
/// unstamped (the callee's crate is core's). Until SEQ-RESIDENCY-1 (2026-10-04) the
/// receiver half was forgeable too: the extractor lowered any type carrying the `Vec`
/// diagnostic item to `Ty::Seq`, and a forged `alloc::vec::Vec` whose `Deref`
/// alternates two slices was hopped, Certified and its check elided (measured on the
/// stage 1 of `ee3f51541d`). `Ty::Seq` now also requires the residency-authenticated
/// sysroot `alloc`. Every other `Deref` — a user type,
/// a generic `T: Deref`, `Rc`/`Arc`/`Box`/`Cow` — is no longer a hop: its result is its
/// own base, which only withholds a length tie.
///
/// `pub(crate)` (local main, review round 107): `iterator_yield`'s bound-rewrite walk
/// follows the same hop, so it must ask the same predicate.
pub(crate) fn callee_is_length_preserving_deref(
    callee: &str,
    func: &VerifiableFunction,
    receiver: &trust_types::Place,
) -> bool {
    match crate::generate::method_tail(callee) {
        "deref" | "deref_mut" => std_container_deref_self(callee)
            .is_some_and(|container| deref_receiver_is_std_container(func, receiver, container)),
        "as_slice" | "as_mut_slice" => {
            callee_is_std_vec_inherent(callee)
                || callee_is_std_slice_inherent(callee, &["::as_slice", "::as_mut_slice"])
        }
        _ => false,
    }
}

/// Which std container's OWN `Deref` impl a callee names (DEREF-ANCHOR-1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StdDerefSelf {
    /// `alloc::vec::Vec<T, A>`: `deref` is `from_raw_parts(ptr, self.len)`.
    Vec,
    /// `alloc::string::String`: `deref` is the `str` over exactly its bytes.
    String,
}

/// The trait-and-method half of std's `Deref::deref` / `DerefMut::deref_mut`, as a
/// qualified callee spells it after its top-level ` as `. The extractor renders the
/// trait by its defining path, `core::ops::deref::Deref` (measured on the stage 1 of
/// `38e6c69b1c` for `Vec<u32>` and `String` receivers); the re-export spellings name the
/// same trait. Compared by EQUALITY, so the method carries no suffix.
const STD_DEREF_TRAIT_METHOD: [&str; 6] = [
    "core::ops::deref::Deref>::deref",
    "core::ops::Deref>::deref",
    "std::ops::Deref>::deref",
    "core::ops::deref::DerefMut>::deref_mut",
    "core::ops::DerefMut>::deref_mut",
    "std::ops::DerefMut>::deref_mut",
];

/// Trust (2026-10-04, DEREF-ANCHOR-1): does `callee` spell std's OWN `Deref::deref` /
/// `DerefMut::deref_mut` impl on std's `Vec` or `String`, and which one?
///
/// Every condition names the impl, the way `unwrap_panic::is_std_scalar_index_call`
/// names std's `Index<usize>`:
///  * the callee opens with `<`. The producer prefixes a callee whose defining crate
///    impersonates a sysroot name with `__trust_crate@…::`;
///  * it is split at its TOP-LEVEL ` as ` (`split_qualified_callee_at_top_level_as`),
///    never searched with `contains`. A self type can carry a fn item whose own
///    spelling holds ` as core::ops::deref::Deref>::deref` — measured:
///    `<alloc::vec::Vec<for<'_> fn(&'_ W) -> &'_ <W as core::ops::deref::Deref>::Target
///    {<W as core::ops::deref::Deref>::deref}> as fnitem::Tr>::deref` is a USER trait
///    method `Tr::deref` on a std `Vec`;
///  * the trait-and-method half EQUALS an entry of [`STD_DEREF_TRAIT_METHOD`];
///  * the self type is std's `Vec` by exact path (`unwrap_panic::is_std_vec_adt_name`,
///    the test IDX-TIE-1's ties use, so the two agree on "std's `Vec`") or std's
///    `String` by exact path.
///
/// A trailing `::<__trust_args@…>` tag (a duplicate-crate-name graph) is not in the
/// table, so such a call is declined, as NAME-ANCHOR-1's tie site declines it.
/// Fail-closed: every other spelling answers `None`.
fn std_container_deref_self(callee: &str) -> Option<StdDerefSelf> {
    if !callee.starts_with('<') {
        return None;
    }
    let (self_ty, trait_method) = crate::generate::split_qualified_callee_at_top_level_as(callee)?;
    if !STD_DEREF_TRAIT_METHOD.contains(&trait_method) {
        return None;
    }
    if crate::generate::is_std_vec_adt_name(self_ty) {
        Some(StdDerefSelf::Vec)
    } else if crate::generate::collection_range::STRING_OWNERS.contains(&self_ty) {
        Some(StdDerefSelf::String)
    } else {
        None
    }
}

/// Trust (2026-10-04, DEREF-ANCHOR-1): is `receiver`, the first argument of a call
/// [`std_container_deref_self`] accepted as `container`'s `Deref`, a reference to
/// that std container — read from the MIR's declared type, not from the callee text?
///
/// `Vec` takes the extractor's `Ty::Seq` (how it lowers std's `Vec`) or a `Ty::Adt`
/// named std's `Vec` by exact path; `String` takes a `Ty::Adt` named std's `String` by
/// exact path. This is the `Deref` twin of `call_facts::primitive_int_ord_method`,
/// which pins `Self` from MIR types: with `Self` std's own container, the orphan rule
/// leaves std's impl the only `Deref` that can run. Any other receiver — a user type,
/// a generic `T`, an `Rc`/`Arc`/`Box` — answers false.
///
/// Both answers are only as good as the producer's identity for the type. A `Ty::Adt`
/// name from a crate that impersonates `alloc`/`std` is stamped
/// (`sysroot_authenticated_def_path_str`). `Ty::Seq` was NOT authenticated until
/// SEQ-RESIDENCY-1 (2026-10-04): the extractor minted it on the `Vec` diagnostic item
/// alone, which a `#![no_std]` dependency built `--crate-name alloc` can declare, so a
/// forged `Vec` passed here (measured; see `callee_is_length_preserving_deref`). It now
/// also requires the defining crate to be the compiler's own resident sysroot `alloc`.
fn deref_receiver_is_std_container(
    func: &VerifiableFunction,
    receiver: &trust_types::Place,
    container: StdDerefSelf,
) -> bool {
    let Some(ty) = crate::place_ty_cow(func, receiver) else { return false };
    let Ty::Ref { inner, .. } = ty.as_ref() else { return false };
    match (container, inner.as_ref()) {
        (StdDerefSelf::Vec, Ty::Seq { .. }) => true,
        (StdDerefSelf::Vec, Ty::Adt { name, .. }) => crate::generate::is_std_vec_adt_name(name),
        (StdDerefSelf::String, Ty::Adt { name, .. }) => {
            crate::generate::collection_range::is_std_string_adt_name(name)
        }
        _ => false,
    }
}

/// Trust (VEC-AS-SLICE, 2026-09-25): the GENUINE std `Vec` slice view — `Vec`'s OWN
/// `Deref::deref`/`DerefMut::deref_mut` impl or its inherent `as_slice`/`as_mut_slice`.
/// It names a length EQUATION between the view and the `Vec`, so the impl itself must
/// be std's (`from_raw_parts(ptr, self.len)`).
///
/// Trust (SLICE-VIEW-ANCHOR-1, 2026-10-04): the `deref`/`deref_mut` arm is
/// [`std_container_deref_self`] answering `Vec`: the callee split at its TOP-LEVEL
/// ` as `, the trait-and-method half EQUAL to std's `Deref>::deref` /
/// `DerefMut>::deref_mut`, the self type std's `Vec` by exact path. It searched the
/// whole string with `contains(" as core::ops::deref::DerefMut>::deref_mut")` (and five
/// sibling needles) until then, and the method tail was the only other test. A USER
/// trait method named `deref_mut` on std's `Vec<u32>` whose trait takes a fn item as a
/// generic argument carries that needle inside the argument:
/// `<alloc::vec::Vec<u32> as m::Shrink<for<'_> fn(&'_ mut m::X) -> &'_ mut
/// <m::X as core::ops::deref::Deref>::Target
/// {<m::X as core::ops::deref::DerefMut>::deref_mut}>>::deref_mut`.
/// Its body truncated `v`, yet the `&mut v` it consumed counted as length-benign
/// (`local_mut_borrows_may_resize_one`), so `if v.len() == 0 { return 0; } <that call>;
/// v.len() - 1` kept its `.len()` tie, read `overflow:sub` Certified with the check
/// elided, and returned `usize::MAX`. The `deref` twin (`View<F>::deref` returning
/// `&[]`) got the view-length equation and the same wrong value (measured on the
/// stage 1 of `ee3f51541d`, every policy). The `Vec` self type of such a call is
/// genuine, so the receiver's MIR type cannot tell the two apart: only the exact
/// split does.
///
/// This answers from the callee TEXT alone. The two call sites that hold the receiver
/// also ask [`receiver_is_std_vec`], because in a `#![no_std]` graph an impersonating
/// `alloc` can still spell `<alloc::vec::Vec<u32> as core::ops::deref::Deref>::deref`
/// unstamped: the callee's defining crate is core, and only the duplicate-crate-name
/// rule tags generic arguments. The crate root of an INHERENT `alloc::vec::Vec::…`
/// callee is authenticated by the producer, which stamps an impersonating crate
/// (`impersonates_sysroot_crate`).
pub(crate) fn callee_is_std_vec_slice_view(callee: &str) -> bool {
    match crate::generate::method_tail(callee) {
        "deref" | "deref_mut" => std_container_deref_self(callee) == Some(StdDerefSelf::Vec),
        "as_slice" | "as_mut_slice" => callee_is_std_vec_inherent(callee),
        _ => false,
    }
}

/// Trust (SLICE-VIEW-ANCHOR-1, 2026-10-04): is `receiver`, the first argument of a
/// std `Vec` slice view ([`callee_is_std_vec_slice_view`]), a reference to std's `Vec`
/// by its MIR type? The receiver half of [`deref_receiver_is_std_container`], asked
/// for `Vec`. `Ty::Seq` is minted only for the residency-authenticated `alloc::vec::Vec`
/// (SEQ-RESIDENCY-1), and an impersonating crate's `Ty::Adt` name is stamped, so a
/// forged `alloc::vec::Vec` answers false here even when the callee text cannot say so.
pub(crate) fn receiver_is_std_vec(
    func: &VerifiableFunction,
    receiver: &trust_types::Place,
) -> bool {
    deref_receiver_is_std_container(func, receiver, StdDerefSelf::Vec)
}

/// Trust (VEC-AS-SLICE, 2026-09-25): the GENUINE std `<[T]>::to_vec`, which returns a
/// fresh `Vec` with exactly the receiver's length (`alloc::slice::<impl [T]>::to_vec`,
/// or the bare inherent UFCS `<[T]>::to_vec`). Rejects a ` as `-qualified trait
/// method and a user free fn (`mycrate::to_vec`).
fn callee_is_std_slice_to_vec(callee: &str) -> bool {
    crate::generate::method_tail(callee) == "to_vec"
        && !callee.contains(" as ")
        && (callee.starts_with("alloc::slice::")
            || callee.starts_with("std::slice::")
            || callee.starts_with("<["))
}

/// Trust (VEC-AS-SLICE, 2026-09-25): is `place` (after peeling at most one reference)
/// a std `Vec` — by the producer-authenticated ADT path, never the bare tail `Vec`
/// (which a user type named `Vec` shares; `is_owned_slice_container_name` read the
/// tail only until OWNED-VEC-NAME-1, 2026-10-04, and now takes the same exact path).
pub(crate) fn place_is_std_vec(func: &VerifiableFunction, place: &trust_types::Place) -> bool {
    let Some(ty) = crate::place_ty_cow(func, place) else { return false };
    let adt = match ty.as_ref() {
        Ty::Ref { inner, .. } => inner.as_ref(),
        other => other,
    };
    matches!(adt, Ty::Seq { .. })
        || matches!(adt, Ty::Adt { name, .. }
            if matches!(name.split('<').next(), Some("alloc::vec::Vec" | "std::vec::Vec")))
}

/// Trust (2026-10-15, STRING-AS-STR): is `place` (after peeling at most one reference)
/// std's `String`, by the producer-authenticated ADT path
/// (`collection_range::is_std_string_adt_name`)? The `String` twin of
/// [`place_is_std_vec`]; an impersonating crate's `String` is stamped and answers false.
pub(crate) fn place_is_std_string(func: &VerifiableFunction, place: &trust_types::Place) -> bool {
    let Some(ty) = crate::place_ty_cow(func, place) else { return false };
    let adt = match ty.as_ref() {
        Ty::Ref { inner, .. } => inner.as_ref(),
        other => other,
    };
    matches!(adt, Ty::Adt { name, .. }
        if crate::generate::collection_range::is_std_string_adt_name(name))
}

/// Convert a single GuardCondition into an SMT Formula.
///
/// SwitchIntMatch: discr == value
/// SwitchIntOtherwise: discr != v1 AND discr != v2 AND ...
/// AssertHolds: cond == expected
/// AssertFails: cond != expected (negation of the assert condition)
pub(crate) fn bool_guard_formula(
    func: &VerifiableFunction,
    discr: &Operand,
    truth_value: bool,
) -> Formula {
    if let Some(formula) = bool_switch_semantics(func, discr, truth_value) {
        return formula;
    }
    let discr_f = operand_to_formula(func, discr);
    if truth_value { discr_f } else { Formula::Not(Box::new(discr_f)) }
}

pub(crate) fn guard_to_formula(func: &VerifiableFunction, guard: &GuardCondition) -> Formula {
    match guard {
        GuardCondition::SwitchIntMatch { discr, value } => {
            let discr_ty = crate::operand_ty_cow(func, discr);
            let is_bool = matches!(discr_ty.as_deref(), Some(Ty::Bool));
            if is_bool {
                return bool_guard_formula(func, discr, *value != 0);
            }
            let discr_f = operand_to_formula(func, discr);
            {
                // The raw MIR label is a two's-complement BIT PATTERN at the
                // scrutinee's width; decode it under that type
                // (`crate::switch_label_to_formula`). Reading it as a magnitude
                // put `n == 4294967295` on an `i32` `-1` arm — UNSAT against
                // `n`'s own range fact, so the arm's path condition was VACUOUS
                // and every obligation under it discharged (the
                // `match n { -1 => x + 1, _ => 0 }` FALSE PROOF, and every
                // `match a.cmp(&b)`'s `Ordering::Less` arm with it).
                //
                // A label this cannot decode contributes NO conjunct. This is
                // an assumption lane: a weaker path condition means fewer
                // premises, which can only lose proofs, never manufacture one.
                match discr_ty
                    .as_deref()
                    .and_then(|ty| crate::switch_label_to_formula(ty, *value))
                {
                    Some(value_f) => Formula::Eq(Box::new(discr_f), Box::new(value_f)),
                    None => Formula::Bool(true),
                }
            }
        }
        GuardCondition::SwitchIntOtherwise { discr, excluded_values } => {
            let discr_ty = crate::operand_ty_cow(func, discr);
            if matches!(discr_ty.as_deref(), Some(Ty::Bool)) {
                let excludes_false = excluded_values.contains(&0);
                let excludes_true = excluded_values.iter().any(|value| *value != 0);
                return match (excludes_false, excludes_true) {
                    (false, false) => Formula::Bool(true),
                    (true, false) => bool_guard_formula(func, discr, true),
                    (false, true) => bool_guard_formula(func, discr, false),
                    (true, true) => Formula::Bool(false),
                };
            }
            if excluded_values.is_empty() {
                return Formula::Bool(true);
            }
            let discr_f = operand_to_formula(func, discr);
            // Same typed decode as the match arm above. An undecodable label
            // simply drops out of the conjunction: `otherwise` then excludes one
            // value fewer, which WEAKENS the path condition (fails closed) —
            // whereas the raw spelling asserted `n != 4294967295`, a tautology
            // on an `i32`, silently losing the real `n != -1` exclusion anyway.
            let Some(ty) = discr_ty.as_deref() else {
                return Formula::Bool(true);
            };
            if let [only_v] = excluded_values.as_slice() {
                return match crate::switch_label_to_formula(ty, *only_v) {
                    Some(value_f) => {
                        Formula::Not(Box::new(Formula::Eq(Box::new(discr_f), Box::new(value_f))))
                    }
                    None => Formula::Bool(true),
                };
            }
            let mut not_eqs: Vec<Formula> = excluded_values
                .iter()
                .filter_map(|v| {
                    let value_f = crate::switch_label_to_formula(ty, *v)?;
                    Some(Formula::Not(Box::new(Formula::Eq(
                        Box::new(discr_f.clone()),
                        Box::new(value_f),
                    ))))
                })
                .collect();
            // THE EMPTY CASE IS NOW REACHABLE, and it is a semantic answer
            // rather than a defensive one. Before the typed decode it could not
            // happen — the `excluded_values.is_empty()` early return above
            // covered it and the old `map` never dropped an element — so the
            // `None` arm below was pure defence. With `filter_map`, EVERY label
            // can fail to decode, and the answer is "excludes nothing": the
            // weakest path condition, which fails closed. Spelled as the literal
            // it means. `And([])` denotes the same thing (`formula_to_smtlib`
            // renders it `true`, `chc_fold_bool_expr`'s empty value is `true`),
            // but a reachable answer should say what it is —
            // `test_guard_switch_int_otherwise_u128_above_i128_max` pins this
            // spelling, and it is what the `SwitchIntMatch` arm above returns
            // for the same undecodable input.
            if not_eqs.is_empty() {
                return Formula::Bool(true);
            }
            // Let `pop` DECIDE the shape rather than testing `len` and then
            // asserting "therefore Some" — that second step is what used to
            // need a panic on a production path in the TCB. Semantics are
            // unchanged: exactly one conjunct folds to itself, 2+ go through
            // `And`.
            match not_eqs.pop() {
                Some(only) if not_eqs.is_empty() => only,
                Some(last) => {
                    not_eqs.push(last);
                    Formula::And(not_eqs)
                }
                // Unreachable: the `is_empty` return above already answered it.
                // Kept as the non-panicking identity, never a `panic!` — that is
                // the whole point of deciding the shape with `pop`.
                None => Formula::And(Vec::new()),
            }
        }
        GuardCondition::AssertHolds { cond, expected } => {
            let cond_f = operand_to_formula(func, cond);
            if *expected {
                // Assert expects true: cond == true
                cond_f
            } else {
                // Assert expects false: cond == false, i.e., NOT cond
                Formula::Not(Box::new(cond_f))
            }
        }
        GuardCondition::AssertFails { cond, expected, .. } => {
            // The assert failed, so cond != expected
            let cond_f = operand_to_formula(func, cond);
            if *expected {
                // Expected true but got false
                Formula::Not(Box::new(cond_f))
            } else {
                // Expected false but got true
                cond_f
            }
        }
        _ => Formula::Bool(true), /* unknown guard condition: do not hide bad states */
    }
}

/// Lower one CFG guard without any proof-direction weakening.
///
/// [`guard_to_formula`] is intentionally allowed to replace an unmodeled guard
/// by `true`: callers use the result as a hypothesis, so dropping a hypothesis
/// can only lose a proof.  A refutation lane has the opposite obligation.  SAT
/// after such a replacement need not describe an executable path, so this
/// companion returns `None` whenever the complete guard cannot be represented.
/// It also avoids the one-way predicate summaries in [`bool_switch_semantics`]
/// and keeps a Boolean discriminant as its raw value; the refutation producer
/// must subsequently pin that value to an exact definition or decline.
pub(crate) fn guard_to_refutation_formula(
    func: &VerifiableFunction,
    guard: &GuardCondition,
) -> Option<Formula> {
    // The public renderer deliberately maps future/unsupported operands to a
    // fresh symbol so proof-facing callers lose facts instead of panicking.
    // That is still too weak for SAT-as-witness: a model for the fresh symbol
    // need not be a value the source operand can take.  Reuse the checked CHC
    // boundary so every accepted operand has an exact carrier.
    let raw_operand =
        |operand: &Operand| crate::chc::operand_to_formula_checked(func, operand).ok();
    match guard {
        GuardCondition::SwitchIntMatch { discr, value } => {
            let discr_ty = crate::operand_ty_cow(func, discr)?;
            if matches!(discr_ty.as_ref(), Ty::Bool) {
                let discr_f = raw_operand(discr)?;
                return Some(match *value {
                    0 => Formula::Not(Box::new(discr_f)),
                    1 => discr_f,
                    // A Boolean can never carry any other switch label.  This
                    // is an exact unreachable edge, not an omitted condition.
                    _ => Formula::Bool(false),
                });
            }
            let value_f = crate::switch_label_to_formula(discr_ty.as_ref(), *value)?;
            Some(Formula::Eq(Box::new(raw_operand(discr)?), Box::new(value_f)))
        }
        GuardCondition::SwitchIntOtherwise { discr, excluded_values } => {
            let discr_ty = crate::operand_ty_cow(func, discr)?;
            if matches!(discr_ty.as_ref(), Ty::Bool) {
                let excludes_false = excluded_values.contains(&0);
                let excludes_true = excluded_values.contains(&1);
                let discr_f = raw_operand(discr)?;
                return Some(match (excludes_false, excludes_true) {
                    (false, false) => Formula::Bool(true),
                    (true, false) => discr_f,
                    (false, true) => Formula::Not(Box::new(discr_f)),
                    (true, true) => Formula::Bool(false),
                });
            }
            let discr_f = raw_operand(discr)?;
            if let Some((&last_val, prefix)) = excluded_values.split_last() {
                if prefix.is_empty() {
                    let value_f = crate::switch_label_to_formula(discr_ty.as_ref(), last_val)?;
                    return Some(Formula::Not(Box::new(Formula::Eq(
                        Box::new(discr_f),
                        Box::new(value_f),
                    ))));
                }
                let mut exclusions = Vec::with_capacity(excluded_values.len());
                for &value in prefix {
                    let value_f = crate::switch_label_to_formula(discr_ty.as_ref(), value)?;
                    exclusions.push(Formula::Not(Box::new(Formula::Eq(
                        Box::new(discr_f.clone()),
                        Box::new(value_f),
                    ))));
                }
                let last_f = crate::switch_label_to_formula(discr_ty.as_ref(), last_val)?;
                exclusions.push(Formula::Not(Box::new(Formula::Eq(
                    Box::new(discr_f),
                    Box::new(last_f),
                ))));
                Some(Formula::And(exclusions))
            } else {
                Some(Formula::Bool(true))
            }
        }
        GuardCondition::AssertHolds { cond, expected } => {
            let cond_f = raw_operand(cond)?;
            Some(if *expected { cond_f } else { Formula::Not(Box::new(cond_f)) })
        }
        GuardCondition::AssertFails { cond, expected, .. } => {
            let cond_f = raw_operand(cond)?;
            Some(if *expected { Formula::Not(Box::new(cond_f)) } else { cond_f })
        }
        // `GuardCondition` is non-exhaustive.  A future condition has no exact
        // refutation semantics until this match is deliberately widened.
        _ => None,
    }
}

#[derive(Clone)]
pub(crate) enum BoolSwitchBase {
    Condition(Formula),
    Ascii(Formula),
    StrAffix(Formula),
    IsEmptyLen(Formula),
    None,
}

fn bool_switch_semantics(
    func: &VerifiableFunction,
    discr: &Operand,
    truth_value: bool,
) -> Option<Formula> {
    let local = match discr {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => place.local,
        _ => return None,
    };
    let scope_id = crate::generate::callee_write_set::current_scope_id();
    let base = crate::fn_memo::bool_switch_base(func, (local, scope_id), || {
        if let Some(formula) = bool_condition_definition(func, discr) {
            return BoolSwitchBase::Condition(formula);
        }

        // An ascii predicate is membership in a fixed codepoint set, so the TRUE
        // branch gets the set and the FALSE branch its complement. (The FALSE branch
        // used to get no fact because the old family-wide bound `arg <= 127` was not
        // the definition of any predicate but `is_ascii`: its complement `>= 128` is
        // false of `b'x'` on the `!is_ascii_digit()` branch.) The set arrives already
        // VERSIONED at the predicate call, so it is a claim about the value the call
        // tested, not about whatever the tested place holds at this switch.
        if let Some(set) = ascii_predicate_bound(func, discr) {
            return BoolSwitchBase::Ascii(set);
        }

        // W4 STR-OFFSET (2026-09-25): an authenticated `s.starts_with(p)` /
        // `s.ends_with(p)` being TRUE implies `s.len() >= m` for the pattern's match
        // length `m`. TRUE branch only; the FALSE branch carries no fact (a string
        // may be long and still not start with `p`). Keyed on the callee's DefId
        // (`SysrootItem::StrStartsWith`/`StrEndsWith`), see `str_offset`.
        if let Some(fact) = crate::generate::str_affix_true_len_fact(func, discr) {
            return BoolSwitchBase::StrAffix(fact);
        }

        if let Some(len) = is_empty_result_len(func, discr) {
            return BoolSwitchBase::IsEmptyLen(len);
        }

        BoolSwitchBase::None
    });

    match base {
        BoolSwitchBase::Condition(formula) => {
            Some(if truth_value { formula } else { Formula::Not(Box::new(formula)) })
        }
        BoolSwitchBase::Ascii(set) => {
            Some(if truth_value { set } else { Formula::Not(Box::new(set)) })
        }
        BoolSwitchBase::StrAffix(fact) => {
            Some(if truth_value { fact } else { Formula::Bool(true) })
        }
        BoolSwitchBase::IsEmptyLen(len) => Some(if truth_value {
            Formula::Eq(Box::new(len), Box::new(Formula::Int(0)))
        } else {
            Formula::Gt(Box::new(len), Box::new(Formula::Int(0)))
        }),
        BoolSwitchBase::None => None,
    }
}

fn bool_condition_definition(func: &VerifiableFunction, discr: &Operand) -> Option<Formula> {
    let local = match discr {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => place.local,
        _ => return None,
    };
    if crate::generate::cached_terminator_presence_for_body(&func.body)
        .is_some_and(|tp| !tp.has_switch_int)
    {
        return None;
    }

    let mut candidate = None;
    for block in &func.body.blocks {
        let Terminator::SwitchInt { discr: switch_discr, .. } = &block.terminator else {
            continue;
        };
        if !same_plain_local_operand(discr, switch_discr, local) {
            continue;
        }

        let formula = latest_same_block_bool_definition(func, block, local)?;
        match &candidate {
            Some(existing) if existing != &formula => return None,
            Some(_) => {}
            None => candidate = Some(formula),
        }
    }

    candidate
}

fn same_plain_local_operand(lhs: &Operand, rhs: &Operand, local: usize) -> bool {
    matches!(
        (lhs, rhs),
        (
            Operand::Copy(lhs_place) | Operand::Move(lhs_place),
            Operand::Copy(rhs_place) | Operand::Move(rhs_place),
        ) if lhs_place.local == local
            && rhs_place.local == local
            && lhs_place.projections.is_empty()
            && rhs_place.projections.is_empty()
    )
}

/// The exact truth condition of bool `local` as read by `block`'s TERMINATOR, or
/// `None`. Every answer is DEFINITIONAL — the caller uses it in both polarities
/// (`formula` on the true edge, `Not(formula)` on the false edge), so a merely
/// weaker formula would be a STRONGER false-edge fact. Declining is the only
/// fail-closed answer; the caller then keeps the opaque discriminant, which is
/// exact by construction.
fn latest_same_block_bool_definition(
    func: &VerifiableFunction,
    block: &BasicBlock,
    local: usize,
) -> Option<Formula> {
    let mut walk =
        BoolDefinitionWalk { consumer: block.id, active: Vec::new(), fuel: 64, indirect_hops: 0 };
    bool_definition_reaching(func, block, block.stmts.len(), local, &mut walk)
}

/// State of ONE resolution of a bool guard through its `BitAnd`/`BitOr` leaves.
///
/// Trust: 2026-09-25 — the walk used to be unbounded and CYCLED. Each leaf was
/// resolved against the LATEST definition anywhere in the block rather than the
/// definition REACHING the statement that reads it, so an idempotent self-update
/// `_c = BitOr(copy _c, move _t)` — `changed |= step()` — resolved its own `_c`
/// operand to itself, and `latest_same_block_bool_definition` ↔
/// `resolve_same_block_bool_operand` recursed until the compiler died of a stack
/// overflow (SIGBUS compiling `ay-dpll` on the verified lane: `nelson_oppen_check`'s
/// `has_new_eqs |= arr_new; .. if !has_new_eqs && ..`, whose optimized MIR switches
/// on the self-updated local in the updating block). The same
/// misreading answered a leaf that is REASSIGNED later in the block with the
/// later value — a guard about a value the switch never tested.
///
/// The root fix is [`bool_definition_reaching`]'s `end`: a leaf of the statement
/// at index `i` is looked up in `stmts[..i]` only, so a same-block recursion
/// strictly decreases `end`. A cross-block hop follows a UNIQUE definition that
/// dominates its use in valid MIR, so it cannot cycle either — but the extracted
/// MIR is not certified valid MIR, so termination is made unconditional here:
/// `active` is the ancestor chain of `(block, local, end)` frames (a frame met
/// again on its own chain IS a cycle: the lookup is a pure function of its key)
/// and `fuel` bounds the total number of lookups, which also caps the formula a
/// DAG of shared leaves can unfold to. Both answer "unresolved" (`None`).
struct BoolDefinitionWalk {
    /// The block whose terminator reads the guard. A leaf read in THIS block is
    /// read at a known point before that terminator; a leaf read in another block
    /// is not (see [`opaque_bool_leaf_is_exact`]).
    consumer: BlockId,
    active: Vec<(BlockId, usize, usize)>,
    fuel: usize,
    /// How many cross-block hops on the current chain go from a defining block whose
    /// `Goto` does NOT target the block that hopped (see
    /// [`resolved_comparison_rebound_before_consumer`]): the statements between such a
    /// definition and its read are not on the chain this walk can scan.
    indirect_hops: usize,
}

/// The exact value of bool `local` as it stands just before `block.stmts[end]`
/// (`end == stmts.len()`: before the terminator), or `None` = unresolved.
fn bool_definition_reaching(
    func: &VerifiableFunction,
    block: &BasicBlock,
    end: usize,
    local: usize,
    walk: &mut BoolDefinitionWalk,
) -> Option<Formula> {
    let key = (block.id, local, end);
    // A frame already on its own ancestor chain is a CYCLE (the lookup is a pure
    // function of `key`, so re-entering it can only recurse forever).
    if walk.fuel == 0 || walk.active.contains(&key) {
        return None;
    }
    walk.fuel -= 1;
    walk.active.push(key);
    let found = bool_definition_reaching_step(func, block, end, local, walk);
    walk.active.pop();
    found
}

fn bool_definition_reaching_step(
    func: &VerifiableFunction,
    block: &BasicBlock,
    end: usize,
    local: usize,
    walk: &mut BoolDefinitionWalk,
) -> Option<Formula> {
    let prefix = block.stmts.get(..end)?;
    for (cmp_index, stmt) in prefix.iter().enumerate().rev() {
        let Statement::Assign { place, rvalue, .. } = stmt else {
            continue;
        };
        if place.local != local || !place.projections.is_empty() {
            continue;
        }
        let Rvalue::BinaryOp(op, lhs, rhs) = rvalue else {
            return None;
        };
        // Logical AND/OR of bools, e.g. the `(L..=U).contains(&x)` rewrite's
        // `dest = (x>=L) & (x<=U)`. Recurse so the guard resolves to the conjoined
        // comparison facts (`And(Ge,Le)`) instead of an opaque bool temp — without
        // this, downstream lanes (BV mul dominating-guard) lose both bounds and a
        // range-validated `x * <const>` false-FAILs. A short-circuit `&&` is NOT
        // this shape (it splits into two switches); only an explicit single-block
        // BitAnd/BitOr of bools reaches here. Semantically faithful: `dest==true`
        // iff `lhs && rhs`. Each operand is read AT `cmp_index`, so it is resolved
        // against `stmts[..cmp_index]` — the definition that reaches this read.
        if matches!(op, BinOp::BitAnd | BinOp::BitOr) {
            if !crate::operand_ty_cow(func, lhs)
                .as_deref()
                .is_some_and(|ty| matches!(ty, Ty::Bool))
            {
                return None;
            }
            let lf = resolve_same_block_bool_operand(func, block, cmp_index, lhs, walk)?;
            let rf = resolve_same_block_bool_operand(func, block, cmp_index, rhs, walk)?;
            return Some(match op {
                BinOp::BitAnd => Formula::And(vec![lf, rf]),
                _ => Formula::Or(vec![lf, rf]),
            });
        }
        if !matches!(op, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge) {
            return None;
        }
        // Trust #soundness: a resolved comparison guard `hi <= K` is STALE if `hi`
        // is reassigned between the comparison (which `c` captured) and the guard's
        // consumer — conjoined onto a guarded VC it contradicts the live `hi == big`
        // and vacuously discharges a real obligation (confirmed false-PROVEs of
        // `hi + hi` non-overflow and of a `(L..=U).contains(&x)`-guarded `x * x`).
        // Two channels:
        //   (1) SAME-block: `hi` reassigned LATER in this block, between the
        //       comparison and the SwitchInt that consumes `c`.
        //   (2) CROSS-block: `hi` reassigned in ANOTHER block on the way to the
        //       consumer — e.g. a BitAnd-range leaf resolved here in bb0 while a
        //       later block reassigns `hi` before switching. This is NOT caught by
        //       the path-guard map's inherited-redef kill, because the freshly-added
        //       switch guard is appended AFTER that block's kill.
        // Withhold resolution in either case — block-local reassign OR whole-
        // function instability of a compared operand — so the guard falls back to
        // the opaque bool `c` (an SSA temp, never reassigned). Monotone-sound (drops
        // a hypothesis: PROVE -> FAIL only); a non-reassigned operand still resolves
        // (control tests), so no over-conservatism for the legitimate guarded case.
        if compared_operand_reassigned_after(block, cmp_index, lhs, rhs)
            || [lhs, rhs].iter().any(|op| match op {
                Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                    value_local_is_unstable(func, p.local)
                }
                _ => false,
            })
        {
            return None;
        }

        let lhs_ty = crate::operand_ty_cow(func, lhs);
        let formula = if let Some(Ty::Float { width }) = lhs_ty.as_deref() {
            float_binop_to_formula(func, *op, lhs, rhs, *width)?
        } else {
            let lhs_f = same_block_inlined_operand_formula(func, block, lhs)
                .unwrap_or_else(|| operand_to_formula(func, lhs));
            let rhs_f = same_block_inlined_operand_formula(func, block, rhs)
                .unwrap_or_else(|| operand_to_formula(func, rhs));
            let width = lhs_ty.as_ref().and_then(|ty| ty.int_width());
            let signed = lhs_ty.as_ref().is_some_and(|ty| ty.is_signed());
            // Trust #integrity: fail closed on an unlowerable binop — return no
            // guard (a dropped HYPOTHESIS only makes proofs harder), never panic.
            crate::chc::try_binop_to_formula(*op, lhs_f, rhs_f, width, signed).ok()?
        };
        // Trust #soundness (2026-10-05): the two checks above see only WHOLE-local
        // writes of PLAIN-local operands. A compared PROJECTION (`(*_1).0`), or a
        // name the formula inlined (`s__slice_len`), written between the comparison
        // and the consumer's terminator — where every consumer renames the guard —
        // makes the guard name the POST-write value: `_2 = Lt((*_1).0, 4);
        // (*_1).0 = x; switchInt(_2)` gave the taken edge `s*.0 < 4` with `s*.0 ==
        // x`, and the `a[s.i]` bounds row under it PROVED (a false proof;
        // tests/stale_projected_compare_guard.rs). Withhold; the caller keeps the
        // opaque discriminant, which is exact.
        if resolved_comparison_rebound_before_consumer(
            func, block, cmp_index, &formula, lhs, rhs, walk,
        ) {
            return None;
        }
        return Some(formula);
    }

    // No definition in `stmts[..end]`. The `(L..=U).contains(&x)` rewrite leaves
    // `dest = BitAnd(..)` in the CALL block and unconditionally `Goto`s to the
    // SwitchInt block that consumes it, so the bool def is one block back. A local
    // with a single static definition dominates all its uses (MIR never reads an
    // uninitialized local), so resolve the UNIQUE defining block when it flows
    // forward unconditionally (`Goto`). If that block is THIS block, its one write
    // sits at or after `end` — it cannot reach this read (in valid MIR the read
    // would be of an uninitialized local), so decline rather than re-enter; any
    // other block is searched from its end. `BoolDefinitionWalk` makes termination
    // unconditional on top of that argument.
    //
    // THE UNIQUENESS QUESTION BELONGS TO THE SEAM. The dominance argument needs the
    // definition to be unique on EVERY channel a local can be written through, and it
    // is false outright for a PARAMETER; `local_defs::unique_defining_block` answers
    // both, and its doc names the two kernel-certified false proofs (`p7`, `p8`) that
    // a hand-rolled `Statement::Assign`-only scan here produced. The SAME-BLOCK arm
    // above needs no such check: that definition precedes the read by program order,
    // whoever wrote the local first.
    if crate::local_defs::is_parameter(func, local) {
        return None;
    }
    let defining = crate::local_defs::unique_defining_block(func, local)
        .and_then(|index| func.body.blocks.get(index))?;
    match defining {
        b if b.id != block.id && matches!(b.terminator, Terminator::Goto(_)) => {
            // Trust (2026-10-05): a hop from a block that does not `Goto` THIS block
            // leaves blocks between the definition and the read that the chain does
            // not name; a comparison resolved under it may keep only names whose
            // stability is answered function-wide.
            let indirect = !matches!(b.terminator, Terminator::Goto(target) if target == block.id);
            walk.indirect_hops += usize::from(indirect);
            let found = bool_definition_reaching(func, b, b.stmts.len(), local, walk);
            walk.indirect_hops -= usize::from(indirect);
            found
        }
        _ => None,
    }
}

/// Does a write between the comparison at `block.stmts[cmp_index]` and the end of
/// the walk's consumer block rebind a name `formula` (that comparison, resolved)
/// reads? Then the guard, which every consumer renames at its source terminal, would
/// name the POST-write value: an over-strong hypothesis.
///
/// The span scanned is `block.stmts[cmp_index + 1..]` and its terminator, plus every
/// block of the walk's chain once it leaves `block` (each WHOLE: a hop always enters
/// a block at its end, and the consumer is read at its terminator). A same-block
/// ancestor frame reads at a later index of `block`, inside the first span.
///
/// Every channel counts, by the shared taxonomy: [`Statement::place_writes`] /
/// [`Terminator::place_writes`] (store, call destination, `SetDiscriminant`,
/// `Deinit`, `&mut` / raw borrow, drop glue; `Unlocatable` fails closed), the operands
/// an `Rvalue::Unsupported` may alias, the opaque deref-store havoc the version oracle
/// applies (`deref_store_havoc_names_over`), and any call (its `&mut` arguments are
/// not place writes) — each against the read names under `dest_write_rebinds`, the
/// relation the version oracle itself mints by.
///
/// Under an INDIRECT hop (`walk.indirect_hops`) the blocks between are unknown, so
/// only names of projection-free operand locals survive: their stability is answered
/// function-wide by `value_local_is_unstable` at the call site.
fn resolved_comparison_rebound_before_consumer(
    func: &VerifiableFunction,
    block: &BasicBlock,
    cmp_index: usize,
    formula: &Formula,
    lhs: &Operand,
    rhs: &Operand,
    walk: &BoolDefinitionWalk,
) -> bool {
    fn collect<'a>(formula: &'a Formula, out: &mut FxHashSet<&'a str>) {
        trust_types::visit_formula_nodes(formula, &mut |node| {
            if let Some(name) = node.var_name() {
                out.insert(name);
            }
        });
    }
    let after = block.stmts.get(cmp_index + 1..).unwrap_or(&[]);
    if walk.indirect_hops == 0
        && after.is_empty()
        && block.terminator.call_args().is_none()
        && matches!(block.terminator.place_writes(), trust_types::PlaceWrites::None)
        && walk.active.iter().rev().skip(1).all(|&(id, _, _)| id == block.id)
    {
        return false;
    }
    let mut read = FxHashSet::default();
    collect(formula, &mut read);
    if read.is_empty() {
        return false;
    }
    if walk.indirect_hops > 0 {
        let plain: [Option<String>; 2] = [lhs, rhs].map(|op| match op {
            Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                Some(crate::place_to_var_name(func, p))
            }
            _ => None,
        });
        return !read
            .iter()
            .all(|&name| plain.iter().flatten().any(|p| p == name));
    }
    if span_rebinds_any(func, block, after, &block.terminator, &read) {
        return true;
    }
    let mut left_block = false;
    let mut scanned: Vec<BlockId> = Vec::new();
    for &(id, _, _) in walk.active.iter().rev().skip(1) {
        if !left_block && id == block.id {
            continue;
        }
        left_block = true;
        if scanned.contains(&id) {
            continue;
        }
        scanned.push(id);
        let Some(b) = func.body.blocks.get(id.0).filter(|b| b.id == id) else {
            return true;
        };
        if span_rebinds_any(func, b, &b.stmts, &b.terminator, &read) {
            return true;
        }
    }
    false
}

/// Does any write by `stmts` (a run of `block`'s statements) or `terminator` rebind
/// a name in `read`? See [`resolved_comparison_rebound_before_consumer`].
fn span_rebinds_any(
    func: &VerifiableFunction,
    block: &BasicBlock,
    stmts: &[Statement],
    terminator: &Terminator,
    read: &FxHashSet<&str>,
) -> bool {
    use trust_types::{PlaceWriteChannel, PlaceWrites};
    if terminator.call_args().is_some() {
        return true;
    }
    let rebinds =
        |written: &str| read.iter().any(|&name| crate::generate::dest_write_rebinds(written, name));
    let writes_rebind = |writes: PlaceWrites<'_>| match writes {
        PlaceWrites::None => false,
        PlaceWrites::Unlocatable => true,
        PlaceWrites::Places(places) => places.into_iter().any(|(place, channel)| {
            // Every channel writes (or may write) `place`; the match only makes a new
            // channel a compile error here.
            match channel {
                PlaceWriteChannel::Store
                | PlaceWriteChannel::SetDiscriminant
                | PlaceWriteChannel::Deinit
                | PlaceWriteChannel::MutBorrow
                | PlaceWriteChannel::RawBorrow { .. }
                | PlaceWriteChannel::CallDest
                | PlaceWriteChannel::TailCallReturn
                | PlaceWriteChannel::DropGlue => {}
            }
            rebinds(&crate::place_to_var_name(func, place))
        }),
    };
    if writes_rebind(terminator.place_writes()) {
        return true;
    }
    if stmts.is_empty() {
        return false;
    }
    for stmt in stmts {
        if writes_rebind(stmt.place_writes())
            || stmt
                .unsupported_rvalue_operands()
                .into_iter()
                .any(|place| rebinds(&crate::place_to_var_name(func, place)))
        {
            return true;
        }
    }
    crate::generate::deref_store_havoc_names_over(func, block, stmts)
        .iter()
        .any(|name| rebinds(name))
}

/// True if either comparison operand (a plain local) is reassigned by a statement
/// AFTER `cmp_index` in `block` — making a guard resolved from that comparison
/// stale for the block's guarded successors (see the call site).
fn compared_operand_reassigned_after(
    block: &BasicBlock,
    cmp_index: usize,
    lhs: &Operand,
    rhs: &Operand,
) -> bool {
    let operand_local = |op: &Operand| match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
        _ => None,
    };
    let (l0, l1) = (operand_local(lhs), operand_local(rhs));
    if l0.is_none() && l1.is_none() {
        return false;
    }
    block.stmts.iter().skip(cmp_index + 1).any(|stmt| {
        matches!(stmt, Statement::Assign { place, .. }
            if place.projections.is_empty()
                && (Some(place.local) == l0 || Some(place.local) == l1))
    })
}

/// Resolve the bool operand read by `block.stmts[use_index]` to a formula,
/// recursing through the definition that REACHES that read (`_t = x >= L`) so a
/// `BitAnd`/`BitOr` of bools unfolds to its leaf comparisons.
///
/// UNRESOLVED (no definition, an unsupported one, a cycle, or exhausted fuel) is
/// NOT a license to substitute anything weaker: the enclosing guard is used in
/// both polarities, so a leaf replaced by `true` would forge `Not(rhs)` on the
/// false edge. It falls back to the operand's OWN term only where that term still
/// denotes the value read here ([`opaque_bool_leaf_is_exact`]) — then the result
/// is exact, merely less informative than an unfolding. Otherwise `None`, and the
/// whole definition declines to the caller's opaque discriminant.
fn resolve_same_block_bool_operand(
    func: &VerifiableFunction,
    block: &BasicBlock,
    use_index: usize,
    operand: &Operand,
    walk: &mut BoolDefinitionWalk,
) -> Option<Formula> {
    if let Operand::Copy(place) | Operand::Move(place) = operand
        && place.projections.is_empty()
        && let Some(formula) = bool_definition_reaching(func, block, use_index, place.local, walk)
    {
        return Some(formula);
    }
    opaque_bool_leaf_is_exact(func, block, use_index, operand, walk.consumer)
        .then(|| operand_to_formula(func, operand))
}

/// Does the unresolved leaf `operand`, read by `block.stmts[use_index]`, still
/// hold the value it was read with when the guard is consumed at the end of
/// `consumer`?
///
///  * A constant always does.
///  * A single-static-assignment local (one whole value, no partial write, no
///    alias — `local_defs::is_single_static_assignment`) has one meaning at every
///    program point, wherever it was read.
///  * Any other local only when read in the CONSUMER block itself and neither
///    written nor aliased after the read, and never aliased anywhere (a store
///    through `*p` names `p`, not the local). A read in another block has an
///    unscanned path to the consumer, so it declines.
///
/// The read statement ITSELF may write the leaf: a leaf is read only by a
/// `dest = BitAnd/BitOr(..)` of bools, so that is the self-update
/// `c = c | t` (`changed |= step()`), and there the new value stands in exactly
/// for the old one — `c' | t == (c | t) | t == c | t == c'` (likewise for `&`),
/// by idempotence. That is the shape that used to overflow the stack.
fn opaque_bool_leaf_is_exact(
    func: &VerifiableFunction,
    block: &BasicBlock,
    use_index: usize,
    operand: &Operand,
    consumer: BlockId,
) -> bool {
    let place = match operand {
        Operand::Constant(_) => return true,
        Operand::Copy(place) | Operand::Move(place) => place,
        _ => return false,
    };
    if place
        .projections
        .iter()
        .any(|projection| matches!(projection, trust_types::Projection::Deref))
    {
        return false;
    }
    let local = place.local;
    if crate::local_defs::is_single_static_assignment(func, local) {
        return true;
    }
    block.id == consumer
        && block
            .stmts
            .iter()
            .skip(use_index + 1)
            .all(|stmt| matches!(stmt.local_write(local), trust_types::LocalWrite::Untouched))
        && matches!(block.terminator.local_write(local), trust_types::LocalWrite::Untouched)
        && !crate::any_local_write_stmt(func, &func.body.blocks, local, |_b, stmt| {
            crate::stmt_escapes_local(func, stmt, local)
        })
}

/// Resolve a plain-local comparison operand through its latest SAME-BLOCK
/// definition when that definition has a stable, place-keyed formula —
/// currently `PtrMetadata` (slice length).
///
/// Each `s.len()` produces a fresh MIR temp (`_4 = PtrMetadata(s)` in the
/// guard block, `_5 = PtrMetadata(s)` at the bounds assert). The resolved
/// guard `i < _4` would otherwise reference a temp nothing in the VC equates
/// to the assert block's `_5`, leaving the violation satisfiable and the
/// guarded slice index unprovable. Inlining the def maps both sides to the
/// same `{place}__slice_len` symbol. Sound: the substitution is exactly the
/// def equation, and the def dominates the comparison within its block (MIR
/// temps are not reassigned between their definition and use).
fn same_block_inlined_operand_formula(
    func: &VerifiableFunction,
    block: &BasicBlock,
    operand: &Operand,
) -> Option<Formula> {
    let local = match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => place.local,
        _ => return None,
    };
    for stmt in block.stmts.iter().rev() {
        let Statement::Assign { place, rvalue, .. } = stmt else {
            continue;
        };
        if place.local != local || !place.projections.is_empty() {
            continue;
        }
        return match rvalue {
            Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner) => {
                match crate::ptr_metadata_model(func, inner) {
                    crate::PtrMetadataModel::Length(formula) => Some(formula),
                    _ => None,
                }
            }
            // Trust (Imp3): a `slice.len()` in a guard can lower to `Rvalue::Len(place)`
            // (the array/slice `len` rvalue) rather than `PtrMetadata`. Inline it to the
            // SAME `{place}__slice_len` symbol the index-bounds VC uses, so a guard
            // `if buf.len() < HEADER_SIZE { return }` discharges the later `buf[i]`
            // (i < HEADER_SIZE) reads. `Rvalue::Len(place)` IS the slice length, so this is
            // monotone-sound (adds a true def equation; never removes a fact). Closes
            // astream `frame.rs` Frame::decode's header-index `[slice]` obligations.
            Rvalue::Len(place) => crate::place_slice_len_formula(func, place),
            _ => None,
        };
    }
    None
}

fn is_empty_result_len(func: &VerifiableFunction, discr: &Operand) -> Option<Formula> {
    let local = match discr {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => place.local,
        _ => return None,
    };
    let (callee, arg) = call_defining_local(func, local)?;
    if !callee.contains("is_empty") {
        return None;
    }
    // CRATE-ANCHOR (round-5 false-proof close): only the GENUINE std `[T]`/`Vec`/`str`/
    // `String` inherent `is_empty`. A user free fn `fn is_empty(s:&[i32])->bool{false}`
    // renders `mycrate::is_empty` and a user-trait UFCS `<T as mycrate::Trait>::is_empty`
    // carries ` as mycrate`; both are DECLINED — else `!is_empty ⇒ len>0` forges the
    // `v[0]` bound (OOB). The bare `contains("is_empty")` this replaces matched either
    // forgery (any path merely mentioning the substring).
    let is_genuine_is_empty = callee_is_std_slice_inherent(callee, &["::is_empty"])
        || (callee_is_std_vec_inherent(callee)
            && crate::generate::method_tail(callee) == "is_empty")
        || callee_is_std_str_inherent(callee, &["::is_empty"])
        // Trust (2026-09-25, std-range-family): `VecDeque::is_empty`, now that a
        // deque index carries a bound over the same `coll_len(base)` (see
        // `generate::collection_range::deque_receiver_len`).
        || crate::generate::collection_range::is_std_vecdeque_method(callee, &["is_empty"]);
    if !is_genuine_is_empty {
        return None;
    }
    // Slice / array / slice-ref receiver: its type-based length var (existing path).
    if let Some(len) = slice_len_formula(func, arg) {
        return Some(len);
    }
    // Trust: OWNED-CONTAINER receiver (`Vec`/`String`, a `Ty::Adt` — not slice-typed,
    // so `slice_len_formula` is `None`). Its abstract length is `coll_len_var(base)`,
    // the SAME symbolic var the container's `<Vec as Index>::index(v,i)` bound
    // references (see `coll_len_var`'s doc), so `!v.is_empty()` (→ `coll_len_var>0`)
    // discharges a `v[0]` bound — the common `if !v.is_empty(){ v[0] }` idiom.
    owned_container_len_var(func, arg)
}

/// Trust: the abstract length var of an OWNED slice-container (`Vec`/`String`)
/// receiver operand, or `None` if the receiver is not such a container (or its
/// length is not a stable bound here). Used by [`is_empty_result_len`] so a
/// `!v.is_empty()` guard on a `Vec`/`String` yields `coll_len_var(base) > 0` — the
/// SAME var the container's index bound uses.
///
/// SOUNDNESS (0 false-PROVE): gated on (a) a SHARED-reference (`&Vec`/`&String`,
/// NOT `&mut`) receiver whose pointee is an owned-slice-container TYPE
/// ([`crate::generate::is_owned_slice_container_name`]); and (b) the unique-base
/// trace [`base_collection_local_unique`] (fail-closed on ambiguity — a merged
/// receiver declines). The SHARED-ref gate is what makes `coll_len_var(base)` a
/// STABLE bound: a `&Vec` cannot be resized for the guard→index span (no `&mut`
/// alias can coexist under the borrow checker), so the RESIZE hazard
/// (`fn f(v:&mut Vec){ if !v.is_empty(){ v.clear(); v[0] } }` — `clear` empties `v`,
/// making `v[0]` a genuine OOB) is excluded at the TYPE level. A `&mut` receiver
/// (whose length CAN change between guard and index) declines here — the
/// length-mutation analysis does NOT model `clear`, so a type-level gate is the
/// sound choice. An UNguarded `v[0]` still REFUTES: without the guard `coll_len_var`
/// is unconstrained, so `0 < len` stays unprovable.
pub(crate) fn owned_container_len_var(func: &VerifiableFunction, arg: &Operand) -> Option<Formula> {
    let (Operand::Copy(p) | Operand::Move(p)) = arg else {
        return None;
    };
    if !p.projections.is_empty() {
        return None;
    }
    // Trust (struct-field Vec length identity, 2026-07-08): PLACE-keyed resolution.
    // When the receiver temp is a gated shared-field reborrow
    // (`_t = &((*self).history)` under a `&self` root — every gate lives in
    // [`base_collection_place_unique`]), the length identity is the canonical FIELD
    // PLACE, shared with the index-bound recovery
    // (`generate::collection_abstract_len_with_base_opts`) and the `.len()` tie
    // (`slice_last_some_nonempty_definitions`) — so `!self.history.is_empty()`
    // discharges a `self.history[..]` bound across DISTINCT reborrow temps. The key
    // distinguishes FIELDS (`self.a` and `self.b` mint different vars, so a guard
    // on one can never discharge the other) and FAILS CLOSED to the per-temp
    // whole-local behavior below — whose vars never unify across temps — for
    // `&mut self` roots and every other ungated shape.
    let base_place = base_collection_place_unique(func, p.local)?;
    if !base_place.projections.is_empty() {
        return match crate::place_ty_cow(func, &base_place)?.as_ref() {
            // Same container gate as the whole-local arm below (`Vec` via
            // `is_owned_slice_container_name`, or `String` — byte length). The
            // FIELD itself is the OWNED container: there is no ref layer to peel,
            // and the SHARED-ref immutability that makes the length a stable bound
            // lives on the ROOT, already enforced by the place trace.
            // Trust (OWNED-VEC-NAME-1, 2026-10-04): each name by its exact std path
            // (see the whole-local arm below); a user `struct Vec` field took this
            // arm by its last segment.
            Ty::Adt { name, .. }
                if crate::generate::is_owned_slice_container_name(name)
                    || crate::generate::collection_range::is_std_string_adt_name(name)
                    || crate::generate::collection_range::is_vecdeque_adt_name(name) =>
            {
                Some(coll_len_var_place(func, &base_place))
            }
            // Trust (VEC-AS-SLICE, 2026-09-25): std's `Vec` as the producer spells it.
            Ty::Seq { .. } => Some(coll_len_var_place(func, &base_place)),
            _ => None,
        };
    }
    let base = base_place.local;
    let base_ty = crate::local_ty_ref(func, base)?;
    // ONLY a SHARED `&Container` (immutable for the guard→index span) qualifies.
    let Ty::Ref { mutable: false, inner } = base_ty else {
        return None;
    };
    match inner.as_ref() {
        // `Vec<T>` (via `is_owned_slice_container_name`) OR `String`. `String`'s
        // abstract length is its BYTE length — `String::len`/`is_empty`/
        // `as_bytes().len()` are ALL byte length — so it shares `Vec`'s
        // `coll_len_var` semantics exactly. Recognised locally (NOT by widening
        // `is_owned_slice_container_name`, whose many coll_len-machinery callers
        // stay unchanged); this helper is already SHARED-ref-gated, so `&mut String`
        // + `clear()` still refutes.
        //
        // Trust (OWNED-VEC-NAME-1, 2026-10-04): both names by their EXACT std path
        // (`alloc::vec::Vec`/`std::vec::Vec`, `alloc::string::String`/
        // `std::string::String`), never by the last segment. The `is_empty` call is
        // std's, but this fact names the ROOT the receiver traces to, and the trace
        // hops a `Deref::deref`; a user `struct Vec`/`struct String` whose `deref`
        // alternates two fields passed the old `tail == "Vec"`/`"String"` test, so
        // `if w.is_empty() { return 0; } w.len() - 1` was proved with its overflow
        // check elided (measured on the stage 1 of `38e6c69b1c`, default, strict and
        // certify; the twin named `Wrap` read `overflow:sub` FAILED). std's `Vec` is
        // `Ty::Seq` (the arm below) and std's `String` is `alloc::string::String`
        // (measured with `-Ztrust-dump`), so neither real container is lost.
        Ty::Adt { name, .. }
            if crate::generate::is_owned_slice_container_name(name)
                || crate::generate::collection_range::is_std_string_adt_name(name) =>
        {
            Some(coll_len_var(func, base))
        }
        // Trust (2026-09-25, std-range-family): a SHARED `&VecDeque` — the same
        // shared-ref stability argument, and the var the deque index bound reads.
        t if crate::generate::collection_range::ty_is_vecdeque_or_ref(t) => {
            Some(coll_len_var(func, base))
        }
        // Trust (VEC-AS-SLICE, 2026-09-25): std's `Vec` as the producer spells it.
        Ty::Seq { .. } => Some(coll_len_var(func, base)),
        _ => None,
    }
}

/// `char`/`u8` predicate methods and their TRUE-sets as inclusive codepoint
/// ranges. Matched as the EXACT method LEAF (`method_tail`) of a crate-anchored
/// std callee (round-5): membership of the leaf in this set, never a substring
/// of the whole path (which admitted a same-named user free fn / nested module).
const ASCII_PREDICATES: &[(&str, &[(i128, i128)])] = &[
    ("is_ascii_alphanumeric", &[(0x30, 0x39), (0x41, 0x5A), (0x61, 0x7A)]),
    ("is_ascii_alphabetic", &[(0x41, 0x5A), (0x61, 0x7A)]),
    ("is_ascii_hexdigit", &[(0x30, 0x39), (0x41, 0x46), (0x61, 0x66)]),
    ("is_ascii_punctuation", &[(0x21, 0x2F), (0x3A, 0x40), (0x5B, 0x60), (0x7B, 0x7E)]),
    // `\t`, `\n`, `\x0C`, `\r`, ` `: U+000B VERTICAL TAB is not in the set.
    ("is_ascii_whitespace", &[(0x09, 0x0A), (0x0C, 0x0D), (0x20, 0x20)]),
    ("is_ascii_uppercase", &[(0x41, 0x5A)]),
    ("is_ascii_lowercase", &[(0x61, 0x7A)]),
    ("is_ascii_graphic", &[(0x21, 0x7E)]),
    ("is_ascii_control", &[(0x00, 0x1F), (0x7F, 0x7F)]),
    ("is_ascii_digit", &[(0x30, 0x39)]),
    ("is_ascii", &[(0x00, 0x7F)]),
];

/// The TRUE-set of the GENUINE std `char`/`u8` ascii predicate `callee` names, or
/// `None` (see the crate-anchor note in [`ascii_predicate_bound`]).
fn ascii_predicate_true_set(callee: &str) -> Option<&'static [(i128, i128)]> {
    let std_anchored = (callee.starts_with("core::") || callee.starts_with("std::"))
        && (callee.contains("::num::") || callee.contains("::char::"))
        && callee.contains("is_ascii");
    if !std_anchored {
        return None;
    }
    let tail = crate::generate::method_tail(callee);
    ASCII_PREDICATES.iter().find(|(name, _)| *name == tail).map(|&(_, set)| set)
}

/// Trust (2026-10-09): the interval-domain twin of [`ascii_predicate_bound`]. When
/// `discr` is the result of a genuine std ascii predicate over a WHOLE local `x` of
/// type `u8`/`char` that holds ONE value and is never reassigned or mutably
/// borrowed, returns `x` and the hull of the predicate's TRUE-set, which the
/// interval domain meets into `x` on the branch where the predicate held
/// (`if c.is_ascii_digit() { Some(c - b'0') }` then summarizes as `[0, 9]`).
///
/// Narrower than the path-guard lane on purpose: a single-valued, unescaped whole
/// local has the same value at the call and at every read, so no version pinning
/// is needed; anything else (a field, a value behind a pointer, a reassigned or
/// `&mut`-borrowed local) declines.
pub(crate) fn ascii_predicate_tested_hull(
    func: &VerifiableFunction,
    discr: &Operand,
) -> Option<(Operand, i128, i128)> {
    let local = match discr {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => place.local,
        _ => return None,
    };
    let (callee, arg) = call_defining_local(func, local)?;
    let true_set = ascii_predicate_true_set(callee)?;
    let bounded = deref_through_ref(func, arg).unwrap_or_else(|| arg.clone());
    let (Operand::Copy(place) | Operand::Move(place)) = &bounded else { return None };
    if !place.projections.is_empty()
        || !matches!(
            crate::operand_ty_cow(func, &bounded).as_deref(),
            Some(Ty::Char) | Some(Ty::Int { width: 8 | 32, .. })
        )
        || !crate::local_defs::holds_one_value(func, place.local)
        || value_local_is_unstable(func, place.local)
    {
        return None;
    }
    let lo = true_set.first()?.0;
    let hi = true_set.last()?.1;
    Some((bounded, lo, hi))
}

/// When `discr` is the boolean result of a `char`/`u8` ascii predicate call
/// (`ch.is_ascii()`, `ch.is_ascii_digit()`, …), returns the predicate's exact
/// TRUE-set as a formula over the tested value: `b.is_ascii_digit()` is
/// `48 <= b && b <= 57`, `b.is_ascii()` is `b <= 127`.
///
/// Mirrors [`is_empty_result_len`] (a guard predicate whose truth implies a
/// numeric fact): we find the `Call` that defines the switched-on boolean, match
/// the callee against the ascii predicate family, and build the membership
/// formula on the call ARGUMENT (the char/byte under test), lowered exactly as
/// the surrounding VC code lowers an operand.
///
/// SOUNDNESS: the formula is the predicate's definition, so the caller gives the
/// TRUE branch the formula and the FALSE branch its negation, like any other
/// boolean definition (`bool_condition_definition`). Each set is transcribed
/// from the `u8` and `char` bodies in `library/core/src/num/mod.rs` and
/// `library/core/src/char/methods.rs`, which spell the same codepoint ranges.
///
/// Before 2026-09-29 every predicate got the family-wide `arg <= 127` on the
/// TRUE branch only. That is true, but too weak for the commonest guard in
/// ordinary Rust: `if b.is_ascii_digit() { b - b'0' }` was refuted for
/// underflow (ordinary-Rust sweep, `e_digit`).
///
/// THE SET IS VERSIONED AT THE CALL (2026-09-29). The path-guard lane renames a
/// guard at its SWITCH, so a bare set was a claim about the tested place at the
/// switch and at every later read the rename connects to it. The predicate read it
/// at the CALL. When the place changes in between, through a pointer handed to a
/// callee, a pointer reloaded from memory (`x: &mut &mut u8`, a `&mut` field, a
/// holder's `self.cur`) or a direct store, the bare set is false:
/// `let d = x.is_ascii_digit(); zero(x); if d { *x - b'0' }` was proved,
/// kernel-certified, and panics, and a verified build of the holder shape elided the
/// check and returned 240 (the ascii precondition audit and its escape follow-up).
/// Every set therefore goes through `version_rename_at` at the point just after the
/// call returns, and passes untouched through the switch's own rename. A read of the
/// place that nothing wrote since connects to it; a read after any write the version
/// fabric sees (a store, a callee handed a `&mut`, every call for a place behind a
/// `&mut` or raw pointer) is a different SMT name, and the set says nothing about it.
///
/// The point is the call's return target when the call block is its ONLY
/// predecessor, and the call block's terminal otherwise. The first is the value
/// AFTER the call, which for a place behind a pointer is the call's own havoc token
/// (every call re-versions a pointer's pointee); it equals the value the predicate
/// read because a genuine std ascii predicate receives only `&place` of a `u8` or
/// `char` and writes nothing. Without it, `if x.is_ascii_digit() { *x - b'0' }` over
/// `x: &mut u8` would lose its fact to the predicate call's own havoc. A return
/// target with a second predecessor would mix in a value from another path, so it
/// falls back to the call block's terminal, the value BEFORE the call: always the
/// value the predicate read, connected to fewer reads.
fn ascii_predicate_bound(func: &VerifiableFunction, discr: &Operand) -> Option<Formula> {
    let local = match discr {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => place.local,
        _ => return None,
    };
    let (call_block, callee, arg) = call_block_defining_local(func, local)?;
    // (a) CRATE-ANCHOR (round-5 false-proof close): the GENUINE std `char`/`u8` ascii
    // predicate renders `core::num::<impl u8>::is_ascii*` or
    // `core::char::methods::<impl char>::is_ascii*`. Require a core/std crate root, the
    // un-forgeable `::num::`/`::char::` std segment, AND the method LEAF (not a substring
    // anywhere in the path) to be an ascii predicate. The bare `lc.contains(name)` this
    // replaces matched a user `fn is_ascii_digit(x:u64)->bool` (renders
    // `mycrate::…::is_ascii_digit`, substring hit) → a false `x <= 127` that discharges a
    // bounds/shift on a WIDE int (OOB/overflow).
    let true_set = ascii_predicate_true_set(callee)?;
    // The char/byte under test is bounded by 0x7F = 127. A method receiver
    // `b.is_ascii()` lowers to `_r = &b; is_ascii(move _r)`, so the call argument
    // is a REFERENCE to the value, not the value itself — bound the referent
    // (`*_r`, i.e. `b`), which the downstream cast/comparison defs connect to the
    // checked quantity. Bounding the reference local itself would be inert. A
    // by-value argument (no `&` indirection) is bound directly.
    let bounded = deref_through_ref(func, arg).unwrap_or_else(|| arg.clone());
    // (b) TYPE GATE (round-5 false-proof close): apply the `<= 127` bound ONLY when the
    // tested value is a `char`/`u8` — the ONLY types the std ascii predicates receive.
    // The real extractor spells `char` as `Ty::Char`; the older extractor / this file's
    // `ascii_guarded_shift_func` test lower it to `u32`, and `u8` is width 8 — so a
    // genuinely WIDE (u64/u128) arg is NOT a std ascii receiver and is DECLINED. This is
    // defense in depth behind (a): together they close the "forged is_ascii* on a wide
    // int" witness even if a name somehow slipped the anchor.
    let ty_is_char_or_byte = match crate::operand_ty_cow(func, &bounded).as_deref() {
        Some(Ty::Char) => true,
        Some(&Ty::Int { width, .. }) => width == 8 || width == 32,
        _ => false,
    };
    if !ty_is_char_or_byte {
        return None;
    }
    // SOUNDNESS (P0 false proof, 2026-06-17 hunt-8): the `x <= 127` bound describes x AT THE
    // GUARD point. If x's local is REASSIGNED (`x = 200`) or mutably borrowed in the guarded
    // region — `if x.is_ascii() { x = 200; arr[x as usize] }` — the symbol `x` is reused for a
    // different value, and the semantic guard `x <= 127` conjoined with the block-def `x == 200`
    // is a CONTRADICTION that vacuously discharges the `arr[x]` bounds (or `1<<x` shift) obligation
    // (OOB/overflow at runtime; proved in BOTH default and kernel-certified -full). Withhold the
    // bound when the tested value is unstable. Fail-closed: only turns PROVE -> not-proved.
    // NB: do NOT require `p.projections.is_empty()` — a PROJECTED tested value (`t.0.is_ascii()`)
    // is just as stale when its base aggregate is mutated (`t.0 = 200`); checking the BASE local
    // covers both bare and field/element values (hunt-9: the projection-field gap in the hunt-8 fix).
    // A value read THROUGH a reference whose memory nothing in the function can write
    // (every pointer derived from its root accounted for,
    // `local_defs::deref_read_is_never_written`) has one value throughout, so its set
    // is stated BARE and holds at every read: a pure reader called between the test
    // and the use (`show(&*x)`) keeps the fact. Any other value is versioned at the
    // call below (see this function's header), which a write in between — through any
    // alias the version fabric sees — disconnects.
    let mut bare_is_global = false;
    let mut value_is_stable = true;
    let mut behind_pointer = false;
    if let Operand::Copy(p) | Operand::Move(p) = &bounded {
        behind_pointer = matches!(p.projections.first(), Some(trust_types::Projection::Deref));
        if behind_pointer && crate::local_defs::deref_read_is_never_written(func, p) {
            bare_is_global = true;
        } else {
            value_is_stable = !value_local_is_unstable(func, p.local);
        }
    }
    let arg_f = operand_to_formula(func, &bounded);
    // Both types are unsigned, so a range starting at 0 is its upper bound alone.
    let set = if let &[(lo, hi)] = true_set {
        if lo == 0 {
            Formula::Le(Box::new(arg_f), Box::new(Formula::Int(hi)))
        } else {
            Formula::And(vec![
                Formula::Ge(Box::new(arg_f.clone()), Box::new(Formula::Int(lo))),
                Formula::Le(Box::new(arg_f), Box::new(Formula::Int(hi))),
            ])
        }
    } else {
        Formula::Or(
            true_set
                .iter()
                .map(|&(lo, hi)| {
                    let le = Formula::Le(Box::new(arg_f.clone()), Box::new(Formula::Int(hi)));
                    if lo == 0 {
                        le
                    } else {
                        Formula::And(vec![
                            Formula::Ge(Box::new(arg_f.clone()), Box::new(Formula::Int(lo))),
                            le,
                        ])
                    }
                })
                .collect(),
        )
    };
    if bare_is_global {
        return Some(set);
    }
    let Terminator::Call { target, .. } = &call_block.terminator else { return None };
    let (at_block, at_stmt) = match target {
        Some(t) if block_has_sole_predecessor(func, *t, call_block.id) => (*t, 0),
        _ => (call_block.id, call_block.stmts.len()),
    };
    let sv = crate::generate::stmt_versions_for(func);
    let pinned = crate::generate::version_rename_owned_at(set, &sv, func, at_block, at_stmt);
    // A name still BARE after the pin is the ENTRY value there (no write reached the
    // call), and the switch's own rename rebinds a bare name to its value at the
    // switch: pinning protects only a name that already carries a token. A fully
    // pinned set needs no further gate: a later store through `x` (`*x -= b'0'` in an
    // `iter_mut` loop) is a write the fabric versions, not a reason to drop the fact.
    //
    // A bare name for a value BEHIND A POINTER refuses outright. It means the fabric
    // put no token on that pointee even across the predicate call, which re-versions
    // every `&mut` pointee it can see, so the name is one the fabric does not track
    // (a pointer moved out of an `Option` or an iterator result is named through the
    // aggregate it came from), and the later write it misses is just as invisible.
    // Asking only whether the pointer LOCAL is stable let `if b.is_ascii_lowercase() {
    // b.make_ascii_uppercase(); *b - b'a' }` over `iter_mut` prove, and its verified
    // build returned 7 (the pointer-family check's precondition audit, 2026-09-29).
    // A plain value keeps the whole-function stability gate.
    let bare = trust_types::any_free_variable_name(&pinned, &mut |name| !name.contains('#'));
    if bare && (behind_pointer || !value_is_stable) {
        return None;
    }
    Some(pinned)
}

/// True when exactly one edge of a `SwitchInt` (its value targets and `otherwise`)
/// leads to `block`, so entering `block` from the switch means that one value.
fn switch_edge_is_sole(targets: &[(u128, BlockId)], otherwise: BlockId, block: BlockId) -> bool {
    targets.iter().filter(|(_, t)| *t == block).count() + usize::from(otherwise == block) == 1
}

/// True when `from` is the ONLY block with an edge into `block`.
pub(crate) fn block_has_sole_predecessor(
    func: &VerifiableFunction,
    block: BlockId,
    from: BlockId,
) -> bool {
    if let Some(ans) = crate::fn_memo::sole_predecessors(func)
        .and_then(|table| table.block_has_sole_predecessor(block, from))
    {
        return ans;
    }
    (func.body.blocks.get(block.0).is_some_and(|b| b.id == block)
        || func.body.blocks.iter().any(|b| b.id == block))
        && func
            .body
            .blocks
            .iter()
            .all(|b| b.id == from || !b.terminator.has_in_cfg_successor(block))
}

/// True when `local`'s symbolic value is NOT stable — it is REASSIGNED (a parameter with any store
/// to it, or a non-parameter with 2+ stores; counting WHOLE-local AND projected/field stores
/// `t.0 = ..`, `SetDiscriminant`/`Deinit`, plus Call-terminator dests) or mutably borrowed
/// (`Ref{mutable:true}`/`AddressOf`).
/// A guard-narrowing fact (e.g. `is_ascii` => x<=127, or about a field `t.0<=127`) is STALE in any
/// region where the value was reassigned, so it must not be emitted (hunt-8 + hunt-9 P0 fix). Field
/// stores are counted on the BASE local — conservative (a write to ANY field disqualifies the whole
/// aggregate's facts), which is the sound direction.
///
/// Trust (2026-10-01, linear cost): answered from the per-function table
/// [`unstable_locals`] when generation holds a [`crate::generate::FuncAnalysisScope`]
/// for `func` — the scan below is `O(body)` per question (plus `O(body)` per `Call`
/// argument for the borrow-temp lookup), and the lanes ask it once per guard, per
/// operand and per row, which made every such lane quadratic in the body. The table
/// is the same predicate for every local at once; under `cfg(test)` both are computed
/// and asserted equal on every question (`generate::differential_enabled`).
pub(crate) fn value_local_is_unstable(func: &VerifiableFunction, local: usize) -> bool {
    if let Some(table) = crate::generate::unstable_locals_for(func)
        && let Some(&answer) = table.get(local)
    {
        #[cfg(any(test, feature = "version-oracle-differential"))]
        if crate::generate::differential_enabled() {
            assert_eq!(
                answer,
                value_local_is_unstable_scan(func, local),
                "unstable-locals table disagrees with the scan for local {local} of `{}`",
                func.def_path
            );
        }
        return answer;
    }
    value_local_is_unstable_scan(func, local)
}

/// [`value_local_is_unstable`] for EVERY local of `func.body.locals`, in one pass.
///
/// The same predicate, restated per local so it can be read off a table:
///
///  * ESCAPED — some statement takes `&mut local` / `&raw (const|mut) local`
///    (`Ref { mutable: true }` / `AddressOf(_, ..)` of a place rooted at it), or some
///    `Call` passes a projection-free argument local whose FIRST whole-local `Assign`
///    in program order is such a pointer to it — exactly what
///    `operand_local_is_mut_borrow_of` answers (the same wide form since 2026-09-30),
///    which returns at that first `Assign`;
///  * STORES — every `Assign` / `SetDiscriminant` / `Deinit` whose place is rooted at
///    it (projected or not), plus every `Call` destination rooted at it;
///  * unstable iff escaped, or a parameter with one store, or any local with two.
///
/// A local outside `0..locals.len()` is not in the table and keeps the scan.
pub(crate) fn unstable_locals(func: &VerifiableFunction) -> Vec<bool> {
    crate::fn_memo::count_body_scan_items(
        func.body.blocks.iter().map(|b| b.stmts.len() as u64 + 1).sum(),
    );
    let n = func.body.locals.len();
    let mut stores = vec![0u32; n];
    let mut escaped = vec![false; n];
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if let Rvalue::Ref { mutable: true, place: bp } | Rvalue::AddressOf(_, bp) =
                        rvalue
                        && let Some(slot) = escaped.get_mut(bp.local)
                    {
                        *slot = true;
                    }
                    if let Some(count) = stores.get_mut(place.local) {
                        *count = count.saturating_add(1);
                    }
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    if let Some(count) = stores.get_mut(place.local) {
                        *count = count.saturating_add(1);
                    }
                }
                _ => {}
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator
            && let Some(count) = stores.get_mut(dest.local)
        {
            *count = count.saturating_add(1);
        }
    }
    (0..n)
        .map(|local| {
            let is_param = local >= 1 && local <= func.body.arg_count;
            escaped[local] || if is_param { stores[local] >= 1 } else { stores[local] >= 2 }
        })
        .collect()
}

/// The whole-body scan behind [`value_local_is_unstable`] (and its test-time witness).
fn value_local_is_unstable_scan(func: &VerifiableFunction, local: usize) -> bool {
    // Counted like every whole-body walk, so a scaling test sees a per-question scan.
    crate::fn_memo::count_body_scan_items(
        func.body.blocks.iter().map(|b| b.stmts.len() as u64 + 1).sum(),
    );
    let is_param = local >= 1 && local <= func.body.arg_count;
    let mut assigns = 0u32;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if let Rvalue::Ref { mutable: true, place: bp } | Rvalue::AddressOf(_, bp) =
                        rvalue
                        && bp.local == local
                    {
                        return true;
                    }
                    if place.local == local {
                        assigns += 1;
                    }
                }
                // Modeled value writes that carry no Assign rvalue still stale
                // every fact rooted at the place. Count the base conservatively;
                // a Deref-first write only over-invalidates a pointer-local fact,
                // which is the safe direction for this staleness gate.
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place }
                    if place.local == local =>
                {
                    assigns += 1;
                }
                _ => {}
            }
        }
        // Trust (P0 call-arg &mut staleness): a `&mut local` / `&raw mut local`
        // materialized as a borrow temp and passed as a Call ARGUMENT mutates
        // `local` through the callee (`mem::swap`/`replace`/`take`, a user setter
        // `set(&mut local, ..)`). The `Ref{mutable:true}`/`AddressOf` borrow itself
        // is the `Statement::Assign` scanned above, so this is already caught for
        // the materialized-temp shape.
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.local == local
        {
            assigns += 1;
        }
    }
    if is_param { assigns >= 1 } else { assigns >= 2 }
}

/// True iff a MUTABLE borrow of `local` exists anywhere in `func` — either
/// materialized as a borrow temp (`_t = &mut local` / `&raw mut local`) or such
/// a temp passed as a Call argument. Writes through that pointer are invisible
/// to direct-def scans, so NO derived value bound — traced (`unsigned_upper_bound`)
/// or structural (`clamp_upper_bound`) — may be trusted for a mut-borrowed local.
/// This is the borrow-escape slice of [`value_local_is_unstable`]; plain
/// reassignment (multiple direct defs) deliberately does NOT match, because a
/// whole-body def scan can still reason soundly about every direct def.
pub(crate) fn value_local_is_mut_borrowed(func: &VerifiableFunction, local: usize) -> bool {
    crate::any_local_write_stmt(func, &func.body.blocks, local, |_block, stmt| {
        matches!(
            stmt,
            Statement::Assign {
                rvalue: Rvalue::Ref { mutable: true, place: bp } | Rvalue::AddressOf(_, bp),
                ..
            } if bp.local == local
        )
    })
}

/// True iff `borrow_temp`'s defining rvalue is a pointer that can write `target`
/// (`&mut target`, `&raw mut target`, `&raw const target` — the wide form the
/// statement scans of [`value_local_is_unstable`] / [`value_local_is_mut_borrowed`]
/// spell, `trust_types::Statement::escapes_local` keyed on `target`).
/// Used to recognize such a pointer passed as a call argument (materialized into
/// `borrow_temp` by MIR). A SHARED borrow (`Ref{mutable:false}`, i.e. `&target`)
/// and a by-value copy are deliberately NOT matched: a write through a pointer
/// derived from a shared reference is UB. `&raw const` joined on 2026-09-30; both
/// callers' statement scans already refused it first, so this changed no verdict.
#[cfg(test)]
fn operand_local_is_mut_borrow_of(
    func: &VerifiableFunction,
    borrow_temp: usize,
    target: usize,
) -> bool {
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt
                && place.local == borrow_temp
                && place.projections.is_empty()
            {
                return matches!(
                    rvalue,
                    Rvalue::Ref { mutable: true, place: bp } | Rvalue::AddressOf(_, bp)
                        if bp.local == target
                );
            }
        }
    }
    false
}

/// If `operand` is `Copy/Move(_r)` where `_r`'s ONE value is a borrow
/// `_r = &referent` (the auto-ref a method call inserts for its `&self`
/// receiver), return `Copy(referent)` so a fact meant for the referent value is
/// stated about the value, not the (inert) reference local. Returns `None` for a
/// by-value operand, leaving it unchanged, and for a reference with any other
/// value (a second borrow, a parameter's entry value): the first borrow found was
/// not necessarily the one the call received.
fn deref_through_ref(func: &VerifiableFunction, operand: &Operand) -> Option<Operand> {
    let local = match operand {
        Operand::Copy(p) | Operand::Move(p)
            if p.projections.is_empty() && !crate::local_defs::is_parameter(func, p.local) =>
        {
            p.local
        }
        _ => return None,
    };
    match crate::local_defs::unique_value_def(func, local)? {
        Rvalue::Ref { place: referent, .. } => Some(Operand::Copy(referent.clone())),
        _ => None,
    }
}

/// The callee and first argument of the `Call` terminator that defines whole-local
/// `local`, when that call is the ONLY thing that gives `local` a value.
///
/// Every caller's conclusion is about the value `local` holds at a LATER READ, so the
/// call has to be the definition reaching that read. An earlier revision left that as a
/// REQUIREMENT on the three callers and argued it was met because rustc never makes a
/// parameter a `Call` destination — an argument from probing, and one that says nothing
/// about a second `Call` or an `Assign` writing the same local. The requirement is now
/// discharged HERE, by the seam: `local_defs::holds_one_value` counts a parameter's
/// ENTRY definition and every `trust_types::LocalWrite` channel, so any local that can
/// hold a second value — from a parameter's entry value, another `Call`, an `Assign`, a
/// projected store, a `SetDiscriminant`/`Deinit`/`Drop`, or an unlocatable pointer
/// write — is refused before any caller sees an answer. Declining is monotone: each
/// caller loses a hypothesis, so a PROVE can become a FAIL and never the reverse.
fn call_defining_local(func: &VerifiableFunction, local: usize) -> Option<(&str, &Operand)> {
    call_block_defining_local(func, local).map(|(_, callee, arg)| (callee, arg))
}

/// [`call_defining_local`], with the block whose terminator is the call.
fn call_block_defining_local(
    func: &VerifiableFunction,
    local: usize,
) -> Option<(&trust_types::BasicBlock, &str, &Operand)> {
    if crate::local_defs::is_parameter(func, local)
        || !crate::generate::terminator_presence_for(func).has_bare_dest_call
    {
        return None;
    }
    let found = crate::find_local_write_term(func, &func.body.blocks, local, |block, term| {
        let Terminator::Call { func: callee, args, dest, .. } = term else {
            return None;
        };
        if dest.local == local && dest.projections.is_empty() {
            return Some(args.first().map(|arg| (block, callee.as_str(), arg)));
        }
        None
    })
    .flatten()?;
    crate::local_defs::holds_one_value(func, local).then_some(found)
}

/// Trust: if `local` is the result of an `as_bytes()` call (`b = recv.as_bytes()`),
/// return the receiver operand `recv`. `as_bytes` is BYTE-LENGTH-PRESERVING
/// (`str::as_bytes().len() == str.len()`; `str` is modeled as `[u8]`), so
/// [`crate::slice_len_formula`] resolves `b`'s length to `recv`'s OWN length var —
/// unifying an `!recv.is_empty()` guard (length on `recv`) with a
/// `recv.as_bytes()[i]` index bound (length on `b`), letting guarded string
/// indexing PROVE (the slice-only recogniser already handles `!s.is_empty()` +
/// `s[i]` on a `&[u8]`; this closes the `str`→`&[u8]` conversion).
///
/// SOUNDNESS (0 false-PROVE): the length transfers ONLY when `recv` itself resolves
/// to a slice length (`slice_len_formula(recv)` is `Some`) — true for the `str`/
/// `&[u8]` receiver of the real `str::as_bytes`, and FAIL-CLOSED (`None`) for any
/// other receiver (e.g. a user `Foo::as_bytes` whose `&Foo` has no slice length),
/// so a non-length-preserving impostor cannot borrow a bogus length. Resolves the
/// defining call with [`call_defining_local`], which returns the FIRST `Call` whose
/// dest is `local` — see its own note for what that does and does not establish.
/// An UNguarded `recv.as_bytes()[i]` still REFUTES: `recv`'s length var is
/// unconstrained without the guard, so `0 < len` stays unprovable.
pub(crate) fn as_bytes_length_receiver(
    func: &VerifiableFunction,
    local: usize,
) -> Option<&Operand> {
    let (callee, arg) = call_defining_local(func, local)?;
    // CRATE-ANCHOR (round-5 false-proof close): only the GENUINE byte-length-preserving
    // `str::as_bytes` (`core::str::<impl str>::as_bytes`, `<str>::as_bytes`) /
    // `String::as_bytes` (`alloc::string::String::as_bytes`). A user
    // `fn as_bytes(&Foo)->&[u8]` renders `mycrate::…::as_bytes` (or a ` as mycrate`
    // UFCS) and is DECLINED. The bare `method_tail == "as_bytes"` this replaces admitted
    // a length-CHANGING impostor: when its receiver is itself slice-typed (so
    // `slice_len_formula(recv)` is `Some`), a shorter/longer forged result borrows the
    // receiver's length var → discharges an OOB index on the fresh `as_bytes` result.
    if callee_is_std_str_inherent(callee, &["::as_bytes"]) {
        return Some(arg);
    }
    None
}

/// Convert a sequence of guard conditions into a single conjunction Formula.
///
/// An empty guard list yields `true` (no assumptions).
#[cfg(test)]
pub(crate) fn guards_to_assumption(
    func: &VerifiableFunction,
    guards: &[GuardCondition],
) -> Formula {
    if guards.is_empty() {
        return Formula::Bool(true);
    }
    let mut formulas: Vec<Formula> = guards.iter().map(|g| guard_to_formula(func, g)).collect();
    // `pop` decides the shape; no "len == 1 implies Some" panic step. The
    // empty case is unreachable via the early return above, and folds to
    // `And(vec![])` = `true` rather than aborting the verifier.
    match formulas.pop() {
        Some(only) if formulas.is_empty() => only,
        Some(last) => {
            formulas.push(last);
            Formula::And(formulas)
        }
        None => Formula::And(Vec::new()),
    }
}

/// Wrap a VC formula with path guard assumptions.
///
/// Returns: guards => vc_formula
/// If guards is empty (or trivially true), returns the vc_formula unchanged.
#[must_use]
#[cfg(test)]
pub(crate) fn guarded_formula(
    func: &VerifiableFunction,
    guards: &[GuardCondition],
    vc_formula: Formula,
) -> Formula {
    if guards.is_empty() {
        return vc_formula;
    }
    let assumption = guards_to_assumption(func, guards);
    // VC convention: formula is SAT iff violation exists.
    // With guards: we only want violations reachable under the guard.
    // So: guard_assumption AND vc_violation_formula
    Formula::And(vec![assumption, vc_formula])
}

/// The single, well-typed checked integer operation whose overflow flag an
/// `Assert(expected = false)` consumes.
///
/// This is a proof-authority boundary, not just a MIR convenience recognizer.
/// Synthetic/imported TrustIR can violate rustc's ordinary SSA and typing
/// invariants, so fail closed unless all of them are explicit here:
///
/// - the condition is exactly the asserted tuple's `.1` field;
/// - that tuple has one and only one write in the block, a whole-local
///   `CheckedBinaryOp(Add|Sub|Mul)`;
/// - both operands and the tuple result have one identical integer type;
/// - the checked operation does not read its own pre-write tuple; and
/// - no value-affecting statement follows the snapshot before the Assert.
///
/// The last two conditions prevent an unversioned formula such as
/// `checked.0 == a + b` from silently referring to a different value at the
/// block exit than the one the checked operation actually read.
fn checked_operand_matches_type(
    func: &VerifiableFunction,
    operand: &Operand,
    expected: &Ty,
) -> bool {
    match operand {
        // Signed MIR constants deliberately lose their source width in the
        // portable VF (`ConstValue::Int`). Recover it only from the checked
        // tuple's authenticated value type, and only when the value is exactly
        // representable there. This admits genuine `i32 + 1` without allowing
        // a forged `i8 + 128` to mint impossible success-edge facts.
        Operand::Constant(ConstValue::Int(value)) => match expected {
            Ty::Int { width: 8, signed: true } => i8::try_from(*value).is_ok(),
            Ty::Int { width: 16, signed: true } => i16::try_from(*value).is_ok(),
            Ty::Int { width: 32, signed: true } => i32::try_from(*value).is_ok(),
            Ty::Int { width: 64, signed: true } | Ty::PtrSizedInt { signed: true } => {
                i64::try_from(*value).is_ok()
            }
            Ty::Int { width: 128, signed: true } => true,
            _ => false,
        },
        // Unsigned constants retain their compiler-extracted width. Require it
        // to agree exactly with the checked tuple carrier (including the
        // faithful pointer-sized spelling) and independently validate the
        // serialized value's range.
        Operand::Constant(ConstValue::Uint(value, source_width)) => {
            let expected_width = match expected {
                Ty::Int { width, signed: false } => *width,
                Ty::PtrSizedInt { signed: false } => 64,
                _ => return false,
            };
            if *source_width != expected_width {
                return false;
            }
            match expected_width {
                8 => u8::try_from(*value).is_ok(),
                16 => u16::try_from(*value).is_ok(),
                32 => u32::try_from(*value).is_ok(),
                64 => u64::try_from(*value).is_ok(),
                128 => true,
                _ => false,
            }
        }
        _ => crate::operand_ty_cow(func, operand).as_deref() == Some(expected),
    }
}

/// Trust (2026-10-12, CHECKED-OP-TRAILING-COPY-1): may statement `k` of `block`,
/// AFTER the asserted `CheckedBinaryOp` and before its `Assert`, stand between them
/// without changing anything the op's facts are stated over?
///
/// THE DEFECT THIS CLOSES (false refutation of valid Rust, both lanes). A closure
/// that bumps a counter it captured by unique borrow and rereads it (`count += 1;
/// count - 1`, trust-ir-conformance `CharCarriers::of`, `subset.rs:577-578`) lowers
/// to `bb0: _5 = copy ((*_1).0); _2 = CheckedAdd(copy (*_5), 1); _6 = copy
/// ((*_1).0); assert(!move (_2.1)) -> bb1`: rustc copies the captured `&mut usize`
/// for the store in bb1 BEFORE the assert. The old rule admitted only inert
/// statements after the op, so the copy into `_6` withheld every assert-passed
/// fact of bb0 (`_2.0 == _1*.0* + 1`, the operand ranges), the value bb1 stores and
/// rereads floated free, and both the `[overflow:sub]` row and its hardened twin
/// were refuted at `_2.0 = 0`. KILLED-ENTRY-EXISTS-1 renamed a fact that was never
/// produced here, which is why it moved no CharCarriers row.
///
/// The facts are stated over the operand names as read AT the op, over the tuple
/// `_N.0`/`_N.1`, and (unversioned in the hardened lane) are conjoined at the
/// block's end. A trailing statement keeps them true at block end iff it changes
/// none of those values. Admitted, fail-closed, only:
///
///  * an `Assign` to a WHOLE local (no projection, so no store through a pointer
///    and no field or element store),
///  * that local is not the tuple and does not occur ANYWHERE in either operand's
///    place (base or `Index` local), so neither the op's reads nor a pointer it
///    reads through is re-seated,
///  * that local's storage is never aliased in the body
///    ([`crate::local_defs::storage_never_aliased`]: no `Ref`, shared or mutable, no
///    `AddressOf`, no reborrow, and no write channel but whole named assigns), so no
///    pointer an operand reads through can denote it,
///  * and the per-statement write oracle ([`crate::generate::stmt_writes_name`])
///    rebinds no free name of either operand's formula.
///
/// Every other statement (a store through a pointer, `SetDiscriminant`, `Deinit`,
/// `CopyNonOverlapping`, an intrinsic) keeps the old refusal: no facts.
fn trailing_stmt_leaves_checked_op_reads(
    func: &VerifiableFunction,
    block: &BasicBlock,
    k: usize,
    tuple_local: usize,
    operands: [&Operand; 2],
) -> bool {
    let Some(Statement::Assign { place, .. }) = block.stmts.get(k) else {
        return false;
    };
    if !place.projections.is_empty() || place.local == tuple_local {
        return false;
    }
    let written = place.local;
    let place_mentions = |p: &trust_types::Place| {
        p.local == written
            || p.projections
                .iter()
                .any(|proj| matches!(*proj, trust_types::Projection::Index(i) if i == written))
    };
    if operands.iter().any(|operand| match operand {
        Operand::Copy(p) | Operand::Move(p) => place_mentions(p),
        _ => false,
    }) {
        return false;
    }
    if !crate::local_defs::storage_never_aliased(func, written) {
        return false;
    }
    operands.iter().all(|operand| {
        trust_types::all_free_variable_names(&operand_to_formula(func, operand), &mut |name| {
            !crate::generate::stmt_writes_name(func, block, k, name)
        })
    })
}

fn exact_asserted_checked_binary_op<'a>(
    func: &'a VerifiableFunction,
    block: &'a BasicBlock,
) -> Option<(usize, BinOp, &'a Operand, &'a Operand, &'a Ty)> {
    let Terminator::Assert { cond, expected: false, .. } = &block.terminator else {
        return None;
    };
    let cond_place = match cond {
        Operand::Copy(place) | Operand::Move(place)
            if matches!(place.projections.as_slice(), [trust_types::Projection::Field(1)]) =>
        {
            place
        }
        _ => return None,
    };
    let tuple_local = cond_place.local;

    let mut checked = None;
    for (idx, stmt) in block.stmts.iter().enumerate() {
        match stmt {
            Statement::Assign { place, rvalue, .. } if place.local == tuple_local => {
                // A projection write or second whole-local write makes the
                // asserted tuple's reaching definition ambiguous.
                if !place.projections.is_empty() || checked.is_some() {
                    return None;
                }
                let Rvalue::CheckedBinaryOp(op @ (BinOp::Add | BinOp::Sub | BinOp::Mul), lhs, rhs) =
                    rvalue
                else {
                    return None;
                };
                checked = Some((idx, *op, lhs, rhs));
            }
            Statement::SetDiscriminant { place, .. } | Statement::Deinit { place }
                if place.local == tuple_local =>
            {
                return None;
            }
            _ => {}
        }
    }
    let (checked_idx, op, lhs, rhs) = checked?;

    if block.stmts.iter().enumerate().skip(checked_idx + 1).any(|(k, stmt)| {
        !matches!(
            stmt,
            Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Retag { .. }
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop
        ) && !trailing_stmt_leaves_checked_op_reads(func, block, k, tuple_local, [lhs, rhs])
    }) {
        return None;
    }
    if [lhs, rhs].iter().any(|operand| {
        matches!(operand, Operand::Copy(place) | Operand::Move(place) if place.local == tuple_local)
    }) {
        return None;
    }

    let Ty::Tuple(fields) = &func.body.locals.get(tuple_local)?.ty else {
        return None;
    };
    let [value_ty, Ty::Bool] = fields.as_slice() else {
        return None;
    };
    if !matches!(value_ty, Ty::Int { .. } | Ty::PtrSizedInt { .. })
        || !checked_operand_matches_type(func, lhs, value_ty)
        || !checked_operand_matches_type(func, rhs, value_ty)
    {
        return None;
    }

    Some((tuple_local, op, lhs, rhs, value_ty))
}

/// Extract semantic assert-passed guards from a block.
///
/// When a block contains a CheckedBinaryOp assignment followed by an Assert
/// terminator on the overflow flag, the assert passing implies:
/// 1. A range constraint: the result is in [min, max] for the type
/// 2. A result definition: `_N.0 = lhs op rhs` (the `.0` field equals the
///    mathematical result), which connects the tuple result to its operands
///
/// Returns a (possibly empty) Vec of formulas. The range constraint ensures
/// the solver knows the assert-passed semantics (e.g., hi >= lo for unsigned
/// CheckedSub), while the result definition enables dataflow tracking through
/// subsequent blocks.
///
/// This is different from the syntactic guard (`NOT _flag`) that path_map
/// already propagates: the syntactic guard refers to an unconstrained boolean
/// variable, while the semantic guard encodes the actual arithmetic meaning.
pub(crate) fn extract_assert_passed_semantics(
    func: &VerifiableFunction,
    block: &BasicBlock,
) -> Vec<Formula> {
    let Some((tuple_local, op, lhs, rhs, value_ty)) = exact_asserted_checked_binary_op(func, block)
    else {
        return Vec::new();
    };

    let lhs_f = operand_to_formula(func, lhs);
    let rhs_f = operand_to_formula(func, rhs);
    let Some(width) = value_ty.int_width() else {
        return Vec::new();
    };
    let signed = value_ty.is_signed();

    // Include input range constraints for the operands of the
    // CheckedBinaryOp. Without these, variables like `hi` that appear in the
    // semantic guard but not in the downstream VC formula would be unconstrained,
    // allowing the solver to pick out-of-range values (e.g., hi > u64::MAX)
    // that satisfy the guard while still causing a false overflow violation.
    let lhs_range = crate::range::input_range_constraint(&lhs_f, width, signed);
    let rhs_range = crate::range::input_range_constraint(&rhs_f, width, signed);

    let result = match op {
        BinOp::Add => Formula::Add(Box::new(lhs_f), Box::new(rhs_f)),
        BinOp::Sub => Formula::Sub(Box::new(lhs_f), Box::new(rhs_f)),
        BinOp::Mul => Formula::Mul(Box::new(lhs_f), Box::new(rhs_f)),
        _ => return Vec::new(),
    };

    // No-overflow means result is in [min, max] for the type.
    let min_f = type_min_formula(width, signed);
    let max_f = type_max_formula(width, signed);

    let in_range = Formula::And(vec![
        Formula::Le(Box::new(min_f), Box::new(result.clone())),
        Formula::Le(Box::new(result.clone()), Box::new(max_f)),
    ]);

    // Also define _N.0 = result_formula. This connects the
    // tuple's result field to the actual arithmetic expression, enabling
    // dataflow tracking when _N.0 is read in subsequent blocks.
    let result_field_name = func
        .body
        .locals
        .get(tuple_local)
        .and_then(|d| d.name.as_deref())
        .map_or_else(|| format!("_{tuple_local}.0"), |n| format!("{n}.0"));
    let result_def =
        Formula::Eq(Box::new(Formula::Var(result_field_name, Sort::Int)), Box::new(result));

    let mut facts = vec![in_range, result_def, lhs_range, rhs_range];
    // Tighten a WIDENED operand (`_4 = a as u16`) to its SOURCE type's range
    // (`0 <= _4 <= 255` for a u8 source), not the wider ADD-operand range
    // (`0 <= _4 <= 65535`). Without this the solver picks an out-of-source-range
    // value for the widened operand and fabricates a false overflow — the
    // hardened panic_boundary OVER-REFUTATION of a provably-safe
    // `a as u16 + b as u16` (the operand range above, keyed on the wider add
    // type, admits `_4 = _5 = 65535`). Sound: the source-width range is an
    // unconditional truth about a value-preserving widening cast (monotone — a
    // true conjunct can only discharge a false-FAIL, never manufacture a
    // false-PROVE). A non-widened operand (e.g. plain `u32 + u32`) yields None,
    // so a genuinely-overflowing add still refutes.
    if let Some(range) = widening_operand_source_range(func, lhs) {
        facts.push(range);
    }
    if let Some(range) = widening_operand_source_range(func, rhs) {
        facts.push(range);
    }
    facts
}

/// The CANONICAL out-of-range **violation** for the block's asserted checked
/// binary op: `result < min ∨ result > max`.
///
/// This is the De Morgan dual of [`extract_assert_passed_semantics`]'s leading
/// `in_range` conjunct, and — this is the whole point — it is the term the rest
/// of the system already agrees on:
///
/// * `generate::overflow_vc` emits exactly this shape as its `out_of_range` core
///   for the per-statement `[arithmetic_overflow_*]` row, and
/// * `trust_semantics::noOverflow_violation_formula` — the trust-types
///   reflection of the Clean kernel's `noOverflow` definition — is pinned
///   STRUCTURALLY equal to it by
///   `range.rs::semantics_violation_formula_is_the_emitted_out_of_range_term`.
///
/// WHY THIS EXISTS (measured 2026-08-27, ledger #221/#222). The `unix_hardened`
/// panic-boundary twin used to hand-roll its violation as
/// `Formula::Not(Box::new(in_range))` — a NEGATED CONJUNCTION. That is the same
/// proposition (z3 4.x reports both UNSAT on `blocked.rs`, and both SAT with the
/// same witness on the guard-widened mutant), but it is a DIFFERENT SYNTAX, and
/// `trust_certify::certify_disjunctive_contradiction` builds its kernel proof by
/// case-splitting a `Formula::Or` found in the normalized conjunct pool. A
/// negated conjunction never reaches that recognizer, so the interval solver's
/// `Proved` was dropped by the authority gate with
/// `"Proved label lacked exact kernel/native proof authority"` — and every crate
/// containing a guarded integer add failed the strict lane on a row nothing
/// refuted.
///
/// The fix is on THIS side, not the certifier's: the recognizer stays exactly as
/// narrow as it is, and the twin is handed the same spelling as its primary.
/// Emitting the canonical dual is not a widening — `¬(min ≤ r ∧ r ≤ max)` and
/// `r < min ∨ r > max` are interderivable over a total order, so the violation's
/// satisfying set is unchanged and a genuinely-overflowing op still refutes
/// (pinned end to end by `blocked_overflows.rs` in
/// `scripts/trust_strict_pass_frontier.sh` and by
/// `crates/trust-certify/tests/hardened_overflow_twin_certification.rs`'s
/// `a_genuinely_overflowing_twin_certifies_nothing_before_or_after_de_morgan`).
///
/// Returns `None` on exactly the blocks where `extract_assert_passed_semantics`
/// returns empty — the biconditional is pinned by
/// `out_of_range_violation_is_the_de_morgan_dual_of_in_range`.
pub(crate) fn checked_binop_out_of_range_violation(
    func: &VerifiableFunction,
    block: &BasicBlock,
) -> Option<Formula> {
    let (_tuple_local, op, lhs, rhs, value_ty) = exact_asserted_checked_binary_op(func, block)?;
    let lhs_f = operand_to_formula(func, lhs);
    let rhs_f = operand_to_formula(func, rhs);
    let width = value_ty.int_width()?;
    let signed = value_ty.is_signed();

    // Byte-identical to `extract_assert_passed_semantics`'s `result`.
    let result = match op {
        BinOp::Add => Formula::Add(Box::new(lhs_f), Box::new(rhs_f)),
        BinOp::Sub => Formula::Sub(Box::new(lhs_f), Box::new(rhs_f)),
        BinOp::Mul => Formula::Mul(Box::new(lhs_f), Box::new(rhs_f)),
        _ => return None,
    };

    let min_f = type_min_formula(width, signed);
    let max_f = type_max_formula(width, signed);
    // NOTE: this deliberately keeps BOTH disjuncts, including for unsigned
    // `Sub`, where `generate::overflow_vc` drops the tautologically-false
    // `result > max` half to keep the `u64::MAX` literal out of ay's i64 domain.
    // That refinement needs the operand ranges to justify it and would make this
    // a semantic change rather than a re-spelling; it is a separate, separately
    // measurable improvement and must not be smuggled in here. The negated
    // conjunction this replaces carried the same `max` literal already.
    Some(Formula::Or(vec![
        Formula::Lt(Box::new(result.clone()), Box::new(min_f)),
        Formula::Gt(Box::new(result), Box::new(max_f)),
    ]))
}

/// If `operand` is `Copy/Move(_n)` where `_n` is defined by a value-preserving
/// widening integer cast `_n = src as wider`, return the SOURCE type's range
/// constraint on `_n` (e.g. `0 <= _n <= 255` for a `u8` source widened to `u16`).
///
/// This bounds a widened arithmetic operand by the type it actually came from,
/// not by the wider operation type — which the integer model otherwise treats as
/// an unconstrained value of the wider type. Sound by construction: a
/// value-preserving widening cast result unconditionally lies within the source
/// type's range (see [`widening_cast_result_range`]), so the returned fact is a
/// true conjunct.
fn widening_operand_source_range(func: &VerifiableFunction, operand: &Operand) -> Option<Formula> {
    let place = match operand {
        Operand::Copy(p) | Operand::Move(p) => p,
        _ => return None,
    };
    if !place.projections.is_empty() {
        return None;
    }
    let local = place.local;
    // The whole-function cast scan below is only an exact reaching definition
    // when this operand local is SSA-stable. A reassigned/mutably-borrowed local
    // can carry a later value outside the cast's source range; injecting the
    // stale narrow bound would contradict that value and vacuously prove a real
    // overflow. Withhold the optional precision fact on any instability.
    if crate::local_defs::is_parameter(func, local) || value_local_is_unstable(func, local) {
        return None;
    }
    let (src, to_ty) = crate::find_local_write_stmt(func, &func.body.blocks, local, |_block, stmt| {
        match stmt {
            Statement::Assign { place: dest, rvalue: Rvalue::Cast(src, to_ty), .. }
                if dest.local == local && dest.projections.is_empty() =>
            {
                Some((src, to_ty))
            }
            _ => None,
        }
    })?;
    if !matches!(to_ty, Ty::Int { .. }) {
        return None;
    }
    // Value-preserving widening keeps its tighter source-width range; a
    // narrowing / reinterpreting cast (defined, no CastOverflow VC) is
    // type-tracked by its target-type range so a widened use of the wrapped
    // value (`(x as u8) as u32 + 1`) proves rather than reading as a free int.
    let src_ty = crate::operand_ty_cow(func, src);
    let src_ty_ref = src_ty.as_deref();
    if !matches!(src_ty_ref, Some(Ty::Int { .. } | Ty::Bool)) {
        return None;
    }
    let dest_name = func
        .body
        .locals
        .get(local)
        .and_then(|d| d.name.as_deref())
        .map_or_else(|| format!("_{local}"), |n| n.to_string());
    widening_cast_result_range_with_ty(src_ty_ref, to_ty, &dest_name).or_else(|| {
        let range = narrowing_cast_result_range_with_ty(src_ty_ref, to_ty, &dest_name)?;
        Some(match narrowing_cast_value_fact_with_ty(func, src, src_ty_ref, to_ty, &dest_name) {
            Some(value) => Formula::And(vec![range, value]),
            None => range,
        })
    })
}

/// Define the checked-arithmetic OVERFLOW FLAG `_N.1` in terms of the operands,
/// for consumers that model both the success and failure edges. Returns
/// `[_N.1 <=> (result < min ∨ result > max), lhs_range, rhs_range]`, or empty
/// when the block is not a `CheckedBinaryOp` + overflow `Assert`.
///
/// Without this the assert-failure condition `_N.1` is a FREE boolean, so every
/// arithmetic panic boundary fails spuriously even when a dominating guard makes
/// overflow impossible. Unlike `extract_assert_passed_semantics` this does NOT
/// emit the `in_range` fact (which assumes no overflow and would vacuously
/// discharge the failure — a false PROVE). It emits only the EXACT flag
/// biconditional (`_N.1` is true iff the unbounded result leaves the type
/// range), a true fact at the assert: under a guard that forces the result in
/// range the failure is UNSAT (proves); with no guard the overflow stays
/// reachable (fails closed).
///
/// Deliberately do NOT define `_N.0` here. MIR's value field wraps when overflow
/// is true, so `_N.0 ==` the unbounded mathematical result holds only on the
/// Assert success edge. [`extract_assert_passed_semantics`] owns that
/// success-only equation and the path-definition fixpoint transports it only
/// along the normal edge.
pub(crate) fn extract_overflow_flag_semantics(
    func: &VerifiableFunction,
    block: &BasicBlock,
) -> Vec<Formula> {
    let Some((tuple_local, op, lhs, rhs, value_ty)) = exact_asserted_checked_binary_op(func, block)
    else {
        return Vec::new();
    };

    let lhs_f = operand_to_formula(func, lhs);
    let rhs_f = operand_to_formula(func, rhs);
    let Some(width) = value_ty.int_width() else {
        return Vec::new();
    };
    let signed = value_ty.is_signed();

    let lhs_range = crate::range::input_range_constraint(&lhs_f, width, signed);
    let rhs_range = crate::range::input_range_constraint(&rhs_f, width, signed);

    let result = match op {
        BinOp::Add => Formula::Add(Box::new(lhs_f), Box::new(rhs_f)),
        BinOp::Sub => Formula::Sub(Box::new(lhs_f), Box::new(rhs_f)),
        BinOp::Mul => Formula::Mul(Box::new(lhs_f), Box::new(rhs_f)),
        _ => return Vec::new(),
    };

    let min_f = type_min_formula(width, signed);
    let max_f = type_max_formula(width, signed);

    let flag_field_name = func
        .body
        .locals
        .get(tuple_local)
        .and_then(|d| d.name.as_deref())
        .map_or_else(|| format!("_{tuple_local}.1"), |n| format!("{n}.1"));

    // `_N.1` is true exactly when the unbounded result leaves the type range.
    let overflowed = Formula::Or(vec![
        Formula::Lt(Box::new(result.clone()), Box::new(min_f)),
        Formula::Gt(Box::new(result), Box::new(max_f)),
    ]);
    let flag_def = Formula::Eq(
        Box::new(Formula::Var(flag_field_name, Sort::Bool)),
        Box::new(overflowed),
    );

    vec![flag_def, lhs_range, rhs_range]
}

/// Extract dataflow definitions from a block's assignment statements.
///
/// Each `Assign { place, rvalue }` is converted to `Eq(Var(place_name), rvalue_formula)`.
/// This allows the solver to know that intermediate locals (e.g., `_5 = _4 / 2`)
/// are constrained by their definitions, not free variables.
///
/// CheckedBinaryOp assignments are skipped (handled by `extract_assert_passed_semantics`).
/// Whole-function facts from `let v = a.checked_add(b)?` (and `checked_sub`): on
/// the success path the unwrapped value equals `a + b` (resp. `a - b`), because
/// `checked_*` returns `Some(a OP b)` exactly when it does not overflow. The
/// LIBRARY `checked_add` lowers to a CALL (not a `CheckedBinaryOp` intrinsic),
/// followed by `Try::branch` and a `ControlFlow::Continue(.0)` / `Some(.0)`
/// payload read — which the per-block `CheckedBinaryOp` semantics miss. This
/// recovers `payload == a OP b` so a guard `payload <= self.len` connects to an
/// obligation over `a + b` (aterm's `slice` offset case).
///
/// SOUND on two counts: the equality is emitted ONLY for the value-bearing
/// variant (`Some` / `Continue`, by matching the downcast's variant index), and
/// it is true wherever the payload local is defined — so conjoining it can only
/// help prove a genuinely-unsatisfiable violation, never erase a real one.
pub(crate) fn build_checked_arith_facts(func: &VerifiableFunction) -> Vec<Formula> {
    if !crate::generate::terminator_presence_for(func).has_call {
        return Vec::new();
    }
    fn operand_local(op: &Operand) -> Option<usize> {
        match op {
            Operand::Copy(p) | Operand::Move(p) => Some(p.local),
            _ => None,
        }
    }
    // Soundness gate (issue 4): every fact produced here is conjoined onto EVERY
    // sep VC in the function (see generate.rs), so each must be a function-wide
    // invariant — not a value a later reassignment can falsify. A fact
    // `payload == a OP b` is emitted only when the payload and each operand
    // base-local holds AT MOST ONE VALUE. A multiply-valued local could hold a
    // different value at the VC site than at the checked-arith site, which would
    // make the global conjunction unsound — and a PARAMETER's first explicit store
    // is already its second value, which a block scan cannot see
    // (`crate::local_defs`).
    let stable_local = |l: usize| crate::local_defs::value_count(func, l).is_at_most(1);
    let stable_operand = |op: &Operand| match op {
        Operand::Constant(_) => true,
        Operand::Copy(p) | Operand::Move(p) => stable_local(p.local),
        // Unknown operand shape: fail closed — don't treat it as stable.
        _ => false,
    };
    // local -> (value `a OP b`, variant index that CARRIES the value).
    // `checked_*` yields `Option` (value in `Some`, variant 1); `Try::branch`
    // re-wraps it as `ControlFlow` (value in `Continue`, variant 0).
    let mut value_of: FxHashMap<usize, (Formula, usize)> = FxHashMap::default();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, callee_key, .. } = &block.terminator
        else {
            continue;
        };
        // CRATE-ANCHOR (round-5 false-proof close): only the GENUINE
        // `core::num::<impl iN>::checked_add`/`checked_sub` inherent mints the
        // `Some-payload == a OP b` value. A user `fn checked_add(a:u32,b:u32)->Option<u32>{Some(BIG)}`
        // renders `mycrate::checked_add` (no `::num::` under a core/std root) and is
        // DECLINED — the bare `lc.contains("checked_add")` this replaces would conjoin a
        // FALSE `payload == a+b` globally (its `Some(BIG) != a+b`) → discharges a bounds
        // check. Method LEAF exact-match (not substring).
        if args.len() >= 2 && is_std_num_intrinsic(callee) {
            let tail = crate::generate::method_tail(callee);
            if matches!(tail, "checked_add" | "checked_sub") {
                // Only record the value when both operands are SSA-stable, so the
                // resulting fact stays a function-wide invariant (see gate above).
                if stable_operand(&args[0]) && stable_operand(&args[1]) {
                    let lhs = Box::new(operand_to_formula(func, &args[0]));
                    let rhs = Box::new(operand_to_formula(func, &args[1]));
                    let val = if tail == "checked_add" {
                        Formula::Add(lhs, rhs)
                    } else {
                        Formula::Sub(lhs, rhs)
                    };
                    value_of.insert(dest.local, (val, 1)); // Option::Some
                }
                continue;
            }
        }
        // `Try::branch(opt)` re-wraps the value into `ControlFlow::Continue`. The
        // re-wrap must itself be the genuine total hop to keep the payload identity
        // true: a user `fn branch(o:Option<u32>)->ControlFlow<_,u32>{Continue(BIG)}`
        // (round 5: the bare `lc.contains("branch")` admitted it) re-wraps a
        // DIFFERENT payload than the source's `a OP b` → a FALSE `payload == a OP b`.
        //
        // Trust (STD-RECEIVER-ANCHOR-1, 2026-10-04): identified by the compiler-minted
        // key `SysrootItem::TryBranch`, never by the spelling. The key is minted only
        // for the trait method `core::ops::try_trait::Try::branch` of the REAL sysroot
        // `core` (`is_real_sysroot_crate`), so a crate compiled `--crate-name core` or
        // a key-less call (indirect, pre-carrier) answers false. The string gate this
        // replaces (`callee_is_std_ops_method` + method tail `branch`) admitted any
        // `<T as core::ops::…>::branch` spelling. The key names no impl
        // (`CalleeOwner::TraitDecl`); `Self` is pinned by the receiver instead:
        // `value_of` holds only the `Option` a genuine `checked_*` above returned or
        // the `ControlFlow` a previous re-wrap returned, and coherence lets only
        // `core` implement `core::ops::Try` for either (`Some(v)`/`Continue(v)` ->
        // `Continue(v)`).
        if trust_types::CalleeKey::opt_is_one_of(
            callee_key.as_ref(),
            &[trust_types::SysrootItem::TryBranch],
        ) && args.len() == 1
            && let Some(src) = args.first().and_then(operand_local)
            && let Some((val, _)) = value_of.get(&src).cloned()
        {
            value_of.insert(dest.local, (val, 0)); // ControlFlow::Continue
        }
    }

    if value_of.is_empty() {
        return Vec::new();
    }
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place, rvalue, .. } = stmt else { continue };
            let (Rvalue::Use(Operand::Copy(src)) | Rvalue::Use(Operand::Move(src))) = rvalue else {
                continue;
            };
            if let [trust_types::Projection::Downcast(v), trust_types::Projection::Field(0)] =
                src.projections.as_slice()
                && let Some((val, expect_v)) = value_of.get(&src.local)
                && v == expect_v
                // The payload local must itself be SSA-stable, else a later
                // reassignment of it would falsify the globally-conjoined fact.
                && stable_local(place.local)
            {
                let payload = crate::place_to_formula(func, place);
                facts.push(Formula::Eq(Box::new(payload), Box::new(val.clone())));
            }
        }
    }
    facts
}

/// Emit `{dest}__slice_len == <referent slice length>` when `referent` is a slice
/// place borrowed (`&`) or raw-pointed (`&raw const/mut`) by `dest`. A pointer
/// preserves the slice's LENGTH metadata — a borrow cannot change a slice's
/// length, not even `&mut [T]` — so the equality is SOUND. It lets a slice length
/// read through the pointer (`PtrMetadata`) — notably the `dst.len()` of a guarded
/// `&mut [T]` index `if i < dst.len() { dst[i] = .. }`, which lowers via a
/// `FakeForPtrMetadata` raw pointer — tie back to the underlying slice's length
/// var. Borrowing `*ref` (deref of a slice reference) resolves through the trailing
/// `Deref` to the underlying reference's STABLE length var (a parameter's), so the
/// guard's and the index's reads share one var. Without this the read is a fresh
/// unconstrained var and a SAFE guarded `&mut` index false-refutes.
fn push_borrow_slice_len(
    func: &VerifiableFunction,
    dest_name: &str,
    referent: &trust_types::Place,
    defs: &mut Vec<Formula>,
    seen_dests: &mut FxHashSet<String>,
) {
    let target = match referent.projections.as_slice() {
        [trust_types::Projection::Deref] => {
            std::borrow::Cow::Owned(trust_types::Place::local(referent.local))
        }
        [.., trust_types::Projection::Deref] => {
            let mut base = referent.clone();
            base.projections.pop();
            std::borrow::Cow::Owned(base)
        }
        _ => std::borrow::Cow::Borrowed(referent),
    };
    // Trust: 2026-09-16 (round A9) — a referent reached through `Index(l)` with a
    // multi-valued `l` (`&(*s)[j]` with `j` reseated) has a length name `s*[_j]__slice_len`
    // that denotes a different slice at every value of `j`. The version rename now
    // rebinds that name on every write of `j` (`path_defs::write_covers_index_segment`),
    // so a tie here would be sound; it is withheld anyway, because a tie is a fact
    // KEYED on that name and a fact must never rest on a name the rename is the only
    // thing keeping distinct. Same rule in `push_unsize_slice_len` / `push_copy_slice_len`.
    if !crate::local_defs::place_index_locals_are_single_static_assignment(func, &target) {
        return;
    }
    if let Some(referent_len) = crate::place_slice_len_formula(func, &target) {
        let name = format!("{dest_name}__slice_len");
        if seen_dests.insert(name.clone()) {
            defs.push(Formula::Eq(
                Box::new(Formula::var_owned(name, Sort::Int)),
                Box::new(referent_len),
            ));
        }
    }
}

/// The element type and CONSTANT length of an array-shaped operand type:
/// `&[T; N]` / `&mut [T; N]` / `*const [T; N]` / `*mut [T; N]` / `[T; N]` all give
/// `(T, N)`. A const-generic length gives the same per-param symbol
/// `slice_len_formula` uses for `[T; N]`, so a guard written against `N`
/// discharges an index whose bound came through a coercion.
///
/// `None` for every non-array shape — in particular for a source that is ALREADY
/// a slice, whose length is a free variable and therefore carries no static fact.
fn array_pointee_len(ty: &Ty) -> Option<(&Ty, Formula)> {
    let pointee = match ty {
        Ty::Ref { inner, .. } => inner.as_ref(),
        Ty::RawPtr { pointee, .. } => pointee.as_ref(),
        other => other,
    };
    match pointee {
        Ty::Array { elem, len } => Some((elem.as_ref(), Formula::Int(i128::from(*len)))),
        Ty::SymArray { elem, len_sym } => {
            Some((elem.as_ref(), crate::sym_array_len_formula(len_sym)))
        }
        _ => None,
    }
}

/// The element type of a slice-pointer target: `&[T]` / `&mut [T]` /
/// `*const [T]` / `*mut [T]` / `[T]` all give `T`. `None` otherwise — notably for
/// `str` (whose metadata is a BYTE length, not an element count) and for
/// `dyn Trait` (whose metadata is a vtable).
fn slice_pointee_elem(ty: &Ty) -> Option<&Ty> {
    let pointee = match ty {
        Ty::Ref { inner, .. } => inner.as_ref(),
        Ty::RawPtr { pointee, .. } => pointee.as_ref(),
        other => other,
    };
    match pointee {
        Ty::Slice { elem } => Some(elem.as_ref()),
        _ => None,
    }
}

/// Emit `{dest}__slice_len == N` for an array→slice UNSIZE coercion
/// `dest = src as &[T]`, where `src: &[T; N]`.
///
/// MIR spells `&[T; N] -> &[T]` as
/// `_d = copy _s as &[T] (PointerCoercion(Unsize, Implicit))`, and
/// `trust-mir-extract`'s slice-unsize arm lowers it to `Rvalue::Cast(op, <the
/// slice-ref target>)`. TrustIR's `Rvalue::Cast` does not carry the `CastKind`, so
/// the coercion is recognised here by its TYPES instead. `slice_len_formula` maps
/// the DEST — a slice reference — to the FREE var `{dest}__slice_len`, which
/// discards the `N` that was part of the SOURCE's type. This is the tie for the
/// coercion that [`push_borrow_slice_len`] is for a borrow, and it exists for the
/// same reason its doc names: without it the length read is a fresh unconstrained
/// var, so `a.len() - 1` on a `&[u8; 8]` refutes with `len = 0`, and the free
/// length reaches every obligation kind that consumes it (bounds, div/rem-by-zero,
/// add/sub/mul overflow).
///
/// SOUND: the coercion sets the result's length metadata to exactly the source
/// array's `N`, so the equality holds on every execution and conjoining it removes
/// no real model. A genuine out-of-bounds `a[i]` still refutes, because what is
/// unconstrained there is `i`, not the length.
///
/// FAIL-CLOSED on shape. `Rvalue::Cast` is the SAME TrustIR variant used for
/// `PtrToPtr` and int-to-int casts, so the tie is gated on both ends:
/// the source pointee must be an array ([`array_pointee_len`], which declines a
/// source that is already a slice) and the target pointee must be a slice of the
/// SAME element type ([`slice_pointee_elem`]). An element-type change such as
/// `*const [u32] -> *const [u8]` — where the preserved metadata counts a different
/// unit — therefore never reaches the tie.
fn push_unsize_slice_len(
    func: &VerifiableFunction,
    dest_name: &str,
    source: &Operand,
    source_ty: Option<&Ty>,
    to_ty: &Ty,
    defs: &mut Vec<Formula>,
    seen_dests: &mut FxHashSet<String>,
) {
    let Some(target_elem) = slice_pointee_elem(to_ty) else { return };
    let Some(source_ty) = source_ty else { return };
    let Some((source_elem, len)) = array_pointee_len(source_ty) else { return };
    if source_elem != target_elem {
        return;
    }
    // Trust: 2026-09-16 (round A9) — see `push_borrow_slice_len`: no tie keyed on a
    // source place whose index locals are not single-valued.
    if let Operand::Copy(src) | Operand::Move(src) = source
        && !crate::local_defs::place_index_locals_are_single_static_assignment(func, src)
    {
        return;
    }
    let name = format!("{dest_name}__slice_len");
    if seen_dests.insert(name.clone()) {
        defs.push(Formula::Eq(Box::new(Formula::var_owned(name, Sort::Int)), Box::new(len)));
    }
}

/// `dest = copy/move source` for a slice/str reference or raw pointer: the fat
/// pointer's length metadata is copied with it, so `{dest}__slice_len == len(source)`
/// — the `Use` sibling of [`push_borrow_slice_len`] / [`push_unsize_slice_len`].
/// Emitted only when the destination's length is a NAME (`slice_len_formula` returns
/// the `__slice_len` variable — a constant-length `&[T; N]` destination needs no tie)
/// and the source has a modelled length (a name or a constant).
fn push_copy_slice_len(
    func: &VerifiableFunction,
    dest: &trust_types::Place,
    dest_name: &str,
    source: &Operand,
    defs: &mut Vec<Formula>,
    seen_dests: &mut FxHashSet<String>,
) {
    let Some(Formula::Var(name, _)) = crate::place_slice_len_formula(func, dest) else {
        return;
    };
    if name.strip_suffix(crate::generate::SLICE_LEN_SUFFIX) != Some(dest_name) {
        return;
    }
    // Trust: 2026-09-16 (round A9) — THE FALSE PROVE THIS TIE MINTED. `_12 = copy
    // (*_1)[_3]` before `j = k` and `_13 = copy (*_1)[_3]` after it both tied their
    // dest's length to the ONE unversioned name `s*[_3]__slice_len`, and
    // `v2_formula_with_slice_len_ties` conjoined both onto the `RangeTo` obligation:
    // `let mut j = 0; let n = s[j].len().min(100); j = k; s[j][..n]` PROVED
    // kernel-certified while `f(&[&[1,2,3,4,5], &[9]], 1)` panics
    // (`index_local_min_bug`, `index_local_min_let_bug`). The rename now versions that
    // name by `j`'s writes (`path_defs::write_covers_index_segment`); the tie is
    // withheld as well, so no fact is keyed on a name whose index local is not
    // single-valued. See `push_borrow_slice_len`.
    if let Operand::Copy(src) | Operand::Move(src) = source
        && !crate::local_defs::place_index_locals_are_single_static_assignment(func, src)
    {
        return;
    }
    let Some(source_len) = crate::slice_len_formula(func, source) else { return };
    if seen_dests.insert(name.clone()) {
        defs.push(Formula::Eq(Box::new(Formula::var_owned(name, Sort::Int)), Box::new(source_len)));
    }
}

/// `dest = source as *const [T]` (or a transmute between slice fat pointers): the
/// cast keeps the length metadata, so `{dest}__slice_len == len(source)`. The
/// source may be wrapped in core's pointer scaffold, as the elaborated deref of a
/// `Box<[T]>` reads it (`_8 = copy (_1.0: Unique<[T]>).0: NonNull<[T]> as *const
/// [T]`): the wrapper is peeled down to its raw fat pointer, whose length names
/// the box's slice. Every `b.len()` / `b[i]` on one `Box<[T]>` makes a FRESH cast
/// temp, so without this tie the guard and the index name two unrelated lengths
/// (Trust, 2026-10-08; ordinary-Rust sweep `c90_boxed_slice`, `c90b`).
fn push_cast_slice_len(
    func: &VerifiableFunction,
    dest: &trust_types::Place,
    dest_name: &str,
    source: &Operand,
    defs: &mut Vec<Formula>,
    seen_dests: &mut FxHashSet<String>,
) {
    let (Operand::Copy(src) | Operand::Move(src)) = source else { return };
    let Some(Formula::Var(name, _)) = crate::place_slice_len_formula(func, dest) else {
        return;
    };
    if name.strip_suffix(crate::generate::SLICE_LEN_SUFFIX) != Some(dest_name) {
        return;
    }
    if !crate::local_defs::place_index_locals_are_single_static_assignment(func, src) {
        return;
    }
    let mut src = std::borrow::Cow::Borrowed(src);
    // At most the two-level `Unique` -> `NonNull` scaffold, each a one-field
    // `repr(transparent)` struct around the fat pointer.
    for _ in 0..3 {
        let src_ty = crate::place_ty_cow(func, &src);
        // Only a FAT source carries the metadata being copied. A thin `*const [T;
        // N]` source has a static length too, but an element-changing array cast
        // (`[u32; 4]` -> `[u8]`) would make `N` count the wrong unit; array sources
        // are `push_unsize_slice_len`'s, which checks the element type.
        let src_is_fat = matches!(
            src_ty.as_deref(),
            Some(Ty::RawPtr { pointee, .. } | Ty::Ref { inner: pointee, .. })
                if matches!(pointee.as_ref(), Ty::Slice { .. } | Ty::Str)
        );
        if src_is_fat && let Some(len) = crate::place_slice_len_formula(func, &src) {
            // The pointee `*dest` is the slice the fat pointer describes, so its
            // length is the same metadata (`(*_10)[i]` reads `_10*__slice_len`).
            let mut pointee = dest.clone();
            pointee.projections.push(trust_types::Projection::Deref);
            if let Some(Formula::Var(pointee_name, _)) =
                crate::place_slice_len_formula(func, &pointee)
                && seen_dests.insert(pointee_name.clone())
            {
                defs.push(Formula::Eq(
                    Box::new(Formula::var_owned(pointee_name, Sort::Int)),
                    Box::new(len.clone()),
                ));
            }
            if seen_dests.insert(name.clone()) {
                defs.push(Formula::Eq(
                    Box::new(Formula::var_owned(name, Sort::Int)),
                    Box::new(len),
                ));
            }
            return;
        }
        match src_ty.as_deref() {
            Some(Ty::Adt { name: adt, .. })
                if adt == "core::ptr::non_null::NonNull"
                    || adt == "core::ptr::unique::Unique"
                    // Trust (1.101): Box's field 0 is BoxRaw, not Unique.
                    || adt == "alloc::boxed::BoxRaw" =>
            {
                src.to_mut().projections.push(trust_types::Projection::Field(0));
            }
            _ => return,
        }
    }
}

/// `dest = copy source` where both are a `Box<[T]>` (or the `Unique`/`NonNull`
/// it is built from): the wrapped fat pointer's length is copied with the value, so
/// `{dest}.0.0.0__slice_len == {source}.0.0.0__slice_len` (the path through the
/// wrappers to the raw `*const [T]`). A `&Box<[T]>` deref copies the box out first
/// (`_8 = copy (*_1); _11 = copy (_8.0.0) as *const [T]`), once per `b.len()` /
/// `b[i]`, so the cast ties of [`push_cast_slice_len`] end at three unrelated copies
/// without this one (Trust, 2026-10-08).
fn push_copy_wrapped_slice_len(
    func: &VerifiableFunction,
    dest: &trust_types::Place,
    source: &Operand,
    defs: &mut Vec<Formula>,
    seen_dests: &mut FxHashSet<String>,
) {
    let (Operand::Copy(src) | Operand::Move(src)) = source else { return };
    let dest_ty = crate::place_ty_cow(func, dest);
    let Some(mut ty) = dest_ty.as_deref() else { return };
    if !matches!(ty, Ty::Adt { .. }) {
        return;
    }
    let mut path_len = 0usize;
    for _ in 0..4 {
        match ty {
            Ty::RawPtr { pointee, .. }
                if path_len > 0 && matches!(pointee.as_ref(), Ty::Slice { .. } | Ty::Str) =>
            {
                if !crate::local_defs::place_index_locals_are_single_static_assignment(func, src) {
                    return;
                }
                let with = |base: &trust_types::Place| {
                    let mut p = base.clone();
                    p.projections.resize(p.projections.len() + path_len, trust_types::Projection::Field(0));
                    crate::place_slice_len_formula(func, &p)
                };
                if let (Some(Formula::Var(d, _)), Some(len)) = (with(dest), with(src))
                    && seen_dests.insert(d.clone())
                {
                    defs.push(Formula::Eq(
                        Box::new(Formula::var_owned(d, Sort::Int)),
                        Box::new(len),
                    ));
                }
                return;
            }
            Ty::Adt { name, fields, .. }
                if (name == "alloc::boxed::Box"
                    // Trust (1.101): Box's field 0 is BoxRaw, not Unique; the
                    // chase depth to the raw pointer is unchanged (3 fields).
                    || name == "alloc::boxed::BoxRaw"
                    || name == "core::ptr::unique::Unique"
                    || name == "core::ptr::non_null::NonNull")
                    && !fields.is_empty() =>
            {
                path_len += 1;
                ty = &fields[0].1;
            }
            _ => return,
        }
    }
}

pub(crate) fn extract_block_definitions(
    func: &VerifiableFunction,
    block: &BasicBlock,
) -> Vec<Formula> {
    extract_block_definitions_until(func, block, block.stmts.len())
}

/// [`extract_block_definitions`] with each def tagged by the index of the
/// statement that EMITTED it (program order, indices non-decreasing). Trust:
/// 2026-09-16 (round A11) — the index is what lets a consumer establish-version a
/// def at ITS OWN statement (`block_defs::version_block_def_at_establish` with
/// `end = k + 1`) and thread a block's defs in statement order
/// (`path_defs::v2_path_def_fixpoint`), instead of searching from the block END
/// for "the latest write of the subject", which is a LATER reseat whenever one
/// exists (`p.0 = 3; p = q; t[p.0]` — the field def re-stamped onto the
/// post-reseat version, a kernel-certified false PROVE).
pub(crate) fn extract_block_definitions_indexed(
    func: &VerifiableFunction,
    block: &BasicBlock,
) -> Vec<(usize, Formula)> {
    extract_block_definitions_until_impl(func, block, block.stmts.len(), false)
}

pub(crate) fn extract_block_definitions_until(
    func: &VerifiableFunction,
    block: &BasicBlock,
    end_stmt_exclusive: usize,
) -> Vec<Formula> {
    extract_block_definitions_until_impl(func, block, end_stmt_exclusive, false)
        .into_iter()
        .map(|(_, d)| d)
        .collect()
}

/// Variant for the ESTABLISH-POINT-VERSIONED consumer
/// (`v2_formula_with_block_defs_at_point`), which stamps every def's reads at its
/// own statement (`version_block_def_at_establish`) before conjoining. On that
/// path, PURE PLACE-READ defs (`_t == place` from `_t = Copy/Move(place)`) are
/// KEPT even when a later statement clobbers the read place: the establish-point
/// token pins the def to the PRE-write value, and a post-write read of the same
/// place mints a DIFFERENT token (the same name-disjointness that let the
/// deref-store-havoc kill be deleted on this path, proven 0-residual by
/// `block_def_establish_subsumes_kill` + the 65-mutant falsification gate).
/// Without this, a closure's `&mut`-upvar guard (`_2 = (*(_1.0)); if _2 < K {
/// (*(_1.0)) += 1 }`) loses its read-def to the write-back and `_2`/`_4` stay
/// free — the last unified over-refutation instance. COMPUTED defs
/// (`c == (m < 1000)`) keep the staleness kill unchanged, belt-and-suspenders.
/// UNversioned consumers (hardened profile, arm recovery, semantic-guard
/// threading) MUST keep using [`extract_block_definitions_until`] — without the
/// establish stamp, a kept read-def against a later-clobbered place is exactly
/// the `c = m < 1000; m = BIG` false-PROVE the kill exists to stop.
pub(crate) fn extract_block_definitions_until_versioned(
    func: &VerifiableFunction,
    block: &BasicBlock,
    end_stmt_exclusive: usize,
) -> Vec<Formula> {
    extract_block_definitions_until_versioned_indexed(func, block, end_stmt_exclusive)
        .into_iter()
        .map(|(_, d)| d)
        .collect()
}

/// [`extract_block_definitions_until_versioned`] with each def tagged by its
/// emitting statement index — the form the establish-point consumers MUST use:
/// the subject-rebinding exemption this variant grants (see the clobber walk in
/// `extract_block_definitions_until_impl`) is sound only when the consumer pins
/// the def at that exact statement (`version_block_def_at_establish` with
/// `end = k + 1`), never at "the latest write of the subject before block end".
pub(crate) fn extract_block_definitions_until_versioned_indexed(
    func: &VerifiableFunction,
    block: &BasicBlock,
    end_stmt_exclusive: usize,
) -> Vec<(usize, Formula)> {
    extract_block_definitions_until_impl(func, block, end_stmt_exclusive, true)
}

/// The defs ONE statement emits in isolation — [`extract_block_definitions_indexed`]
/// restricted to `stmts[stmt_idx..=stmt_idx]`: no later statement to dedupe against or
/// clobber with. Every def a prefix extraction `extract_block_definitions_until(..,
/// end)` with `end > stmt_idx` keeps for that statement is among these, because the
/// prefix walk differs only by a LARGER `seen_dests` (it skips more) and a LARGER
/// clobber set (it drops more). The statement write index uses that superset to
/// decide when an exact prefix extraction can be skipped.
pub(crate) fn extract_statement_definitions_isolated(
    func: &VerifiableFunction,
    block: &BasicBlock,
    stmt_idx: usize,
) -> Vec<Formula> {
    extract_block_definitions_range_impl(func, block, stmt_idx, stmt_idx + 1, false)
        .into_iter()
        .map(|(_, d)| d)
        .collect()
}

fn extract_block_definitions_until_impl(
    func: &VerifiableFunction,
    block: &BasicBlock,
    end_stmt_exclusive: usize,
    keep_versionable_read_defs: bool,
) -> Vec<(usize, Formula)> {
    extract_block_definitions_range_impl(
        func,
        block,
        0,
        end_stmt_exclusive,
        keep_versionable_read_defs,
    )
}

fn extract_block_definitions_range_impl(
    func: &VerifiableFunction,
    block: &BasicBlock,
    start_stmt: usize,
    end_stmt_exclusive: usize,
    keep_versionable_read_defs: bool,
) -> Vec<(usize, Formula)> {
    // Every def is tagged with the index of the statement that emitted it
    // (`stmt_of`, filled in lockstep at the top of each iteration so the many
    // `continue` arms need no bookkeeping). The walk below is in REVERSE program
    // order, so the indices are non-increasing until the final reverse.
    let mut defs: Vec<Formula> = Vec::new();
    let mut stmt_of: Vec<usize> = Vec::new();
    let mut last_idx: Option<usize> = None;
    let range_span = end_stmt_exclusive.saturating_sub(start_stmt);
    let mut seen_dests: FxHashSet<String> = FxHashSet::default();

    // Trust: McCarthy array-theory version context. Computed lazily on the first
    // `Statement::Assign` from `func` alone (a deterministic forward prepass over
    // the no-join CFG), so the store side and the read side share one oracle while
    // empty ranges and non-Assign statements pay nothing. For non-array /
    // join-bearing functions this is empty and every read/store stays on the scalar
    // path.
    let mut array_ctx: Option<std::rc::Rc<ArrayVersionCtx>> = None;

    for (stmt_idx, stmt) in
        block.stmts.iter().take(end_stmt_exclusive).enumerate().skip(start_stmt).rev()
    {
        // BUDGET POLL, per STATEMENT — the granularity of the expensive work. One
        // statement costs a whole-rvalue lowering plus, on several arms, a
        // WHOLE-FUNCTION walk (`local_is_mutably_borrowed`, `aggregate_field_
        // definitions`, the array-version `live_version` read), and this extractor is
        // itself called once per block by `block_written_names` / `v2_live_path_defs`
        // / the semantic-guard thread — so a wide block in a large function is its own
        // overrun channel and had no poll. Placed at the TOP of the iteration so a
        // partial statement is never emitted: the wrapping-binop arm pushes its
        // operand range tautologies BEFORE its `Eq`, and those ranges are load-bearing
        // for that def (without them the refute direction can cross the modular Ite's
        // branch boundary).
        //
        // BREAK, not `return`: the staleness `retain` below is what drops a def whose
        // operand a LATER statement overwrites (`c = m < 1000; m = BIG`), and skipping
        // it would KEEP a stale fact — a false PROVE. Breaking keeps that filter over
        // whatever was collected. The degradation is fewer defs, and since iteration
        // is REVERSE program order the ones lost are the EARLIEST statements', each
        // surviving def still being checked against every later def. Fail-closed:
        // these defs are HYPOTHESES at their consumers, so dropping them turns PROVE
        // into FAIL, never FAIL into PROVE. The dropped-def WRITE-VISIBILITY channel
        // stays closed exactly as it does for this function's existing `continue`
        // arms: the kill/gen-set oracles union the raw statement destinations
        // (`generate::extend_with_assigned_place_dests` + `extend_with_derived_slice_len`),
        // so no kill is lost with the def.
        //
        // Tag everything the PREVIOUS iteration pushed with that statement's index
        // before the poll, so a break never leaves a def untagged.
        if let Some(prev) = last_idx {
            stmt_of.resize(defs.len(), prev);
        }
        last_idx = Some(stmt_idx);
        if trust_types::verify_budget::budget_exhausted() {
            break;
        }
        crate::fn_memo::count_extraction_stmts(1);
        let Statement::Assign { place, rvalue, .. } = stmt else {
            continue;
        };

        // Read context for element reads in THIS statement: the live array
        // version just before `stmt_idx` (the single store-count oracle).
        let array_ctx = array_ctx.get_or_insert_with(|| crate::v2_array_version_prepass(func));
        let read_ctx = ArrayReadCtx::new(array_ctx, block.id, stmt_idx);

        // ---- Array-theory STORE: `a[Index(idx)] = w` into an eligible local.
        // Emit `v{n+1} == Store(v{n}, idx, w)` and SKIP the scalar `seen_dests`
        // handling entirely (each variable-index store must survive — they share
        // the `a[_i]` name and would otherwise dedup to one). NEVER emit the
        // scalar `Eq(Var(a[_i]), w)`.
        if crate::is_array_theory_element_store(func, place.local, stmt) {
            if let Some(model) = crate::array_theory_local(func, place.local) {
                let elem = model.elem_sort;
                let n = array_ctx.live_version(func, place.local, block.id, stmt_idx);
                let idx_proj = &place.projections[0];
                let value = match rvalue {
                    Rvalue::Use(operand) => {
                        operand_to_formula_with_array_ctx(func, operand, Some(&read_ctx))
                    }
                    // A non-`Use` store value (rare) is modeled by its scalar
                    // formula; fall back to the dest place name when unsupported.
                    _ => crate::place_to_formula(func, place),
                };
                defs.push(Formula::Eq(
                    Box::new(crate::array_term_var(place.local, n + 1, elem.clone())),
                    Box::new(Formula::Store(
                        Box::new(crate::array_term_var(place.local, n, elem)),
                        Box::new(crate::array_index_formula(func, idx_proj)),
                        Box::new(value),
                    )),
                ));
                // Skip the scalar `seen_dests` handling ONLY when the array store
                // was actually emitted. If the array is NOT eligible
                // (`array_theory_local` is None) the store must fall through to
                // the scalar `[c;min=len]` path -- otherwise the fact vanishes and
                // a same-slot read goes stale (regresses the #54 const-index case,
                // which is an Index store to a NON-eligible array).
                continue;
            }
        }

        if seen_dests.is_empty() && range_span > 1 {
            seen_dests.reserve(range_span);
        }
        let dest_name = crate::place_to_var_name(func, place);
        if !seen_dests.insert(dest_name.clone()) {
            continue;
        }

        // Skip CheckedBinaryOp — its result definition is handled by semantic guards.
        if matches!(rvalue, Rvalue::CheckedBinaryOp(..)) {
            continue;
        }

        // Trust: 2026-09-19 (the NEGATION lane's spelling dependence) — a whole
        // integer local defined by a CLOSED CONSTANT EXPRESSION is defined to the
        // exact integer the machine computes, as a LITERAL, before any shape-specific
        // rendering runs.
        //
        // WHY, IN THE INT LANE. `let lim = (1u64 << 20) as i64;` lowers (un-optimized)
        // to `_4 = Shl(const 1u64, const 20i32); _3 = Cast(move _4, i64)`, and the
        // `Cast` arm below admits a value-preserving int->int cast only of a LITERAL
        // operand — `_4` is a temporary, so the cast contributed NO definition at all.
        // `_4 == 1048576` was mined and then pruned as disconnected, `lim` stayed a
        // free `i64`, and the `OverflowNeg` row `lim == i64::MIN` was REFUTED: a strict
        // build error on valid Rust whose only defect was the SPELLING of the bound
        // (`1048576i64` and `1i64 << 20` both compile clean, because neither puts a
        // cast between the constant and the negated local).
        //
        // WHY, AT 128 BITS. `-(1i128 << 62)` lowers to `_5 = Shl(const 1i128, const
        // 62i32)`, and the `BinaryOp` arm renders a 128-bit shift faithfully as the BV
        // round trip `_5 == BvToInt(BvShl(IntToBv(1), IntToBv(62)))`. That is TRUE, but
        // it is an opaque mixed-sort term: conjoined onto the `OverflowNeg` row's QF_BV
        // core, in-process ay rejected the whole query (`incomplete self-check-rejected`)
        // and the row came back UNKNOWN, which the strict lane reports as a build error
        // just the same. The literal `4611686018427387904` says exactly the same thing
        // in the theory the rest of the row already lives in.
        //
        // EXACTNESS, AND WHY SKIPPING THE OTHER ARMS IS SAFE. The resolver is
        // exact-or-nothing (every step range-checked against its own destination type,
        // no variable anywhere inside, `local_defs::unique_value_def` for the walk, so
        // an aliased, re-assigned or parameter local resolves to NOTHING), so the
        // literal IS the machine's value and this def is strictly SHARPER than the arm
        // it replaces — never weaker, never different. The auxiliary facts those arms
        // push alongside their equality are result RANGES and modular-Ite operand
        // tautologies, all implied by a literal, and slice-length / array-theory ties,
        // which no `Ty::Int` destination has. A non-resolving rvalue falls straight
        // through to the arms below, unchanged.
        if place.projections.is_empty()
            && let Some(dest_ty) = crate::place_ty_cow(func, place)
            && matches!(dest_ty.as_ref(), Ty::Int { .. })
            && let Some(value) = crate::const_expr::v2_const_expr_rvalue_int(
                func,
                rvalue,
                dest_ty.as_ref(),
                crate::const_expr::V2_CONST_EXPR_FUEL,
            )
        {
            defs.push(Formula::Eq(
                Box::new(Formula::Var(dest_name, Sort::Int)),
                Box::new(Formula::Int(value)),
            ));
            continue;
        }

        let rvalue_formula = match rvalue {
            Rvalue::Use(operand) => {
                // SOUNDNESS (P0 false proof, 2026-06-17 hunt-15): a read of an ENUM
                // PAYLOAD projection `(o as Variant).field` of a mutably-borrowed local
                // `o` must NOT be tied to the shared payload symbol. `o.as_mut()` /
                // `o.insert(b)` / `o.get_or_insert_with(|| b)` can REASSIGN the payload
                // BETWEEN two such reads, e.g.
                //   if let Some(v) = o { if v < 5 { o.as_mut().map(|r| *r = b);
                //                                    match o { Some(i) => arr[i], .. } } }
                // Both `v` and the later `i` lower to `copy ((o as Some).0)`, so they share
                // one var name; the guard bound `v < 5` then transfers to `i` and vacuously
                // discharges `arr[i]` even though `i` became the unbounded `b` (OOB at
                // runtime). hunt-7 gated only the CONSTRUCTION-time field fact
                // (`o@k.field == op`) and the demux re-injection; this is the READ-ALIASING
                // sibling — the `*r = b` Deref-store through the `&mut o` is not tracked as a
                // write to `o`, so the payload symbol stays stale. Emit a FRESH dest (skip
                // the equality) so the two reads are independent. Fail-closed FOR THE
                // HYPOTHESIS: dropping the equality only turns PROVE -> not-proved, never a
                // false-FAIL; the safe non-mutated form (no `&mut o`) is unaffected and
                // still proves. The dest WRITE stays in the gen-sets via
                // `generate::extend_with_assigned_place_dests` (a skipped def must never
                // hide the write itself — the dropped-def write-visibility class).
                if let Operand::Copy(p) | Operand::Move(p) = operand
                    && p.projections
                        .iter()
                        .any(|pr| matches!(pr, trust_types::Projection::Downcast(_)))
                    && local_is_mutably_borrowed(func, p.local)
                {
                    continue;
                }
                // Trust: 2026-09-16 (round A8) — a whole COPY of a slice reference
                // copies its length metadata verbatim, exactly as a reborrow or an
                // unsize cast does; tie `{dest}__slice_len == len(source)` here as
                // `push_borrow_slice_len` / `push_unsize_slice_len` do for those, at
                // this statement's establish point. Without the tie rustc's `-O0`
                // argument temps (`_8 = copy _1; index(move _8, ..)`) read a length
                // (`_8__slice_len`) that nothing connects to the root's — so once the
                // min lane's unlicensed global `n <= s__slice_len` was withheld
                // (`callee_summaries::param_slice_len`), `s = b; let n =
                // s.len().min(100); s[..n]` (correct) lost its proof at `-O0` while
                // keeping it at `-O1`, where the argument is `move _1` itself.
                // Pushed BEFORE the `dest == source` equality (clobber-dedup
                // ordering, as the cast arm's ranges). A stale tie is what the
                // derive-aware clobber below exists for: a later whole write of the
                // source in this block clobbers `{source}__slice_len` and drops it.
                push_copy_slice_len(func, place, &dest_name, operand, &mut defs, &mut seen_dests);
                push_copy_wrapped_slice_len(func, place, operand, &mut defs, &mut seen_dests);
                match operand {
                    Operand::Copy(source) | Operand::Move(source) => {
                        crate::enum_entry::scalar_read(func, source).unwrap_or_else(|| {
                            operand_to_formula_with_array_ctx(func, operand, Some(&read_ctx))
                        })
                    }
                    _ => operand_to_formula_with_array_ctx(func, operand, Some(&read_ctx)),
                }
            }
            // Trust (2026-10-02, proof-loss class 9): rustc's null-dereference
            // check tests `size_of::<P>() != 0` before it lets a null `*p` pass
            // (a ZST may be read through null). When `P` is provably non-ZST the
            // test IS `true`; define it so, and leave the opaque `size_of` symbol
            // (its site or key, OPAQUE-SCALAR-ID-1) unconstrained. Every gate is in
            // `check_null_zst`.
            Rvalue::BinaryOp(..)
                if crate::check_null_zst::check_null_zst_test_is_true(func, block, stmt_idx) =>
            {
                Formula::Bool(true)
            }
            Rvalue::BinaryOp(op, lhs, rhs) => {
                // The shift's own result type, recovered from the DESTINATION when the
                // shifted value is a width-less signed constant. Everything below —
                // the result range AND the `dest == lhs << rhs` equality — reads this
                // one type, so the range can never be stated at a width the definition
                // does not use.
                let lhs_ty = shift_result_ty_from_dest(func, place, op, lhs)
                    .map(std::borrow::Cow::Owned)
                    .or_else(|| crate::operand_ty_cow(func, lhs));
                // an unsigned right-shift by a constant tightens its result
                // below the type max; push that bound BEFORE the `dest == lhs >> rhs`
                // equality (mirroring #52) so it survives the operand-clobber dedup, and
                // so `(x >> k) + …` proves even when `x` is an unconstrained payload.
                // The shift AMOUNT is rendered through the same operand path as the
                // `dest == lhs << rhs` equality below, so `variable_shl_result_range`'s
                // antecedent names the identical symbol; a differently-rendered symbol
                // would leave the implication permanently unfireable instead of wrong.
                let mut cached_l: Option<Formula> = None;
                let mut cached_r: Option<Formula> = None;
                if matches!(op, BinOp::Shl | BinOp::Shr)
                    && let Some(range) = shift_result_range_with(
                        func,
                        lhs_ty.as_deref(),
                        op,
                        lhs,
                        rhs,
                        &dest_name,
                        || {
                            let f = operand_to_formula_with_array_ctx(func, rhs, Some(&read_ctx));
                            cached_r = Some(f.clone());
                            f
                        },
                    )
                {
                    defs.push(range);
                }
                // ...and an unsigned floor-division is additionally bounded by its own
                // dividend (`x >> k <= x`, `x / c <= x`). The constant bound above
                // cannot discharge the safe-midpoint `low + ((high - low) >> 1)`;
                // this relational one can, in either spelling.
                // Rendered through the same operand path as the `dest == lhs >> rhs`
                // equality below so both facts name the identical LHS symbol.
                if matches!(op, BinOp::Shr | BinOp::Div)
                    && let Some(rel) = unsigned_floor_div_le_lhs_with(
                        lhs_ty.as_deref(),
                        op,
                        rhs,
                        &dest_name,
                        || {
                            let f = operand_to_formula_with_array_ctx(func, lhs, Some(&read_ctx));
                            cached_l = Some(f.clone());
                            f
                        },
                    )
                {
                    defs.push(rel);
                }
                if lhs_ty.as_deref().is_some_and(|ty| matches!(ty, Ty::Bool)) {
                    let l = cached_l.unwrap_or_else(|| {
                        operand_to_formula_with_array_ctx(func, lhs, Some(&read_ctx))
                    });
                    let r = cached_r.unwrap_or_else(|| {
                        operand_to_formula_with_array_ctx(func, rhs, Some(&read_ctx))
                    });
                    match op {
                        BinOp::BitAnd => Formula::And(vec![l, r]),
                        BinOp::BitOr => Formula::Or(vec![l, r]),
                        BinOp::BitXor => {
                            Formula::Not(Box::new(Formula::Eq(Box::new(l), Box::new(r))))
                        }
                        _ => {
                            // Pass signedness for correct right-shift selection.
                            let width = lhs_ty.as_deref().and_then(|ty| ty.int_width());
                            let signed = lhs_ty.as_deref().is_some_and(|ty| ty.is_signed());
                            // Trust #integrity: fail closed — skip the def
                            // (a dropped hypothesis), never panic mid-verification.
                            match crate::chc::try_binop_to_formula(*op, l, r, width, signed) {
                                Ok(formula) => formula,
                                Err(_) => continue,
                            }
                        }
                    }
                } else if let Some(Ty::Float { width }) = lhs_ty.as_deref() {
                    // Float ARITHMETIC (Add/Sub/Mul/Div): the dest is a
                    // BitVec(width) bit pattern, so the value-definition is a
                    // COMPLETE structural Eq lifting both sides into FP space
                    // (Eq(FpFromBits(dest), fp.op(RNE, ..))). Push it directly and
                    // `continue` — the generic emitter at the bottom would build
                    // Eq(Var(dest, BitVec), <FP term>), which is ill-sorted.
                    if let Some(def) = fp_arith_value_def(func, *op, lhs, rhs, &dest_name, *width) {
                        defs.push(def);
                        continue;
                    }
                    // Comparisons return a Bool result for the generic
                    // `dest_bool == fp.cmp(..)` definition.
                    match float_binop_to_formula(func, *op, lhs, rhs, *width) {
                        Some(formula) => formula,
                        None => continue,
                    }
                } else {
                    // Pass signedness for correct right-shift selection.
                    let width = lhs_ty.as_ref().and_then(|ty| ty.int_width());
                    let signed = lhs_ty.as_ref().is_some_and(|ty| ty.is_signed());
                    // Trust (2026-07-06, modulo-index): an UNSIGNED `dest = a % b`
                    // with a NON-CONSTANT divisor (`i % s.len()`, the common
                    // ring-buffer idiom) produces a nonlinear `%` TERM that ay's
                    // linear-arith lane REJECTS (`ay_lra … has_unsupported`,
                    // re-parse FAILED), fail-closing the safe index `s[i%s.len()]`
                    // to UNKNOWN. The LINEAR bound `(b==0) ∨ (dest < b)` from the
                    // GLOBAL `build_modulo_bound_facts` is SUFFICIENT to discharge
                    // the index (with the `len>0` guard), so DROP this nonlinear
                    // scalar def rather than emit a term no linear backend can
                    // parse. DROP-ONLY for the HYPOTHESIS: removing it can only
                    // WEAKEN a PROVE; the bound fact compensates for the common
                    // bound/comparison uses. The WRITE itself must stay visible
                    // regardless — `generate::extend_with_assigned_place_dests`
                    // keeps the destination in every gen-set, because a dropped
                    // def that also vanished from the write domain let stale
                    // bare facts unify across the assignment (the measured
                    // false-proof class in `tests/dropped_def_write_visibility.rs`).
                    // A CONSTANT divisor keeps its def (`% k` is a smaller,
                    // often-handled term whose exact value may matter).
                    if matches!(op, trust_types::BinOp::Rem)
                        && !signed
                        && !matches!(rhs, Operand::Constant(_))
                    {
                        continue;
                    }
                    // Trust (2026-08-20, bare-BinaryOp wrapping — the -O /
                    // overflow-checks-off form): rustc MIR defines the PLAIN
                    // integer `Add`/`Sub`/`Mul` as WRAPPING mod 2^w.
                    // Overflow-CHECKED user arithmetic arrives as the separate
                    // `CheckedBinaryOp` + overflow-`Assert` pair (skipped
                    // above — its success-path value equation is edge-sensitive
                    // and owned by the path-definition map), and UB-on-overflow
                    // arithmetic as `UncheckedBinaryOp` (unmatched here — no
                    // def). The extractor preserves the three forms distinctly
                    // (`trust-mir-extract convert_supported_binop`), so a bare
                    // `Rvalue::BinaryOp` IS the wrapping case by construction
                    // and no session overflow-checks bit exists or is needed:
                    // with checks ON the bare form arises only from wrapping
                    // intrinsics (e.g. `wrapping_add` inlined at -O), with
                    // checks OFF from all user arithmetic — both wrap.
                    //
                    // The old model here was `try_binop_to_formula`'s UNBOUNDED
                    // `dest == a + b`, FALSE of every execution that wraps:
                    // conjoined as a hypothesis it excluded exactly the wrap
                    // traces, and in the `-full` assert-refutation lane (where
                    // UNSAT of the panic-path formula is consumed as PROVED)
                    // it false-PROVED `assert!(a + b >= a)`-shaped asserts
                    // that panic at runtime — see `wrapping_binop_defs_tests::
                    // wrapping_add_ge_lhs_false_prove_control` for the measured
                    // instance. Encode the EXACT modular semantics instead, via
                    // the SAME shared constructor the authenticated
                    // wrapping-call model uses (`wrapping_binop_modular_ite` —
                    // one spelling, so the call form and the dissolved -O form
                    // can never encode differently in one query), pushing the
                    // operands' type-range tautologies FIRST (true of every
                    // execution; they keep a refute-direction model from
                    // picking an out-of-range operand — and the pre-Eq order is
                    // the same clobber-dedup rationale as `shift_result_range`).
                    // `Mul` and width>64 have no encoding in this lane: DROP
                    // the def, exactly the call form's `WrappingMul => None`
                    // boundary. An Add/Sub/Mul whose operand width is UNKNOWN
                    // is likewise dropped, never modeled unbounded.
                    //
                    // SOUNDNESS OF THE DROP: it is fail-closed for the
                    // HYPOTHESIS only — an ungrounded value can only demote a
                    // row. It is NOT fail-closed for the version-map
                    // side-channel: the gen-sets used to be derived from the
                    // extracted defs, so this `continue` also deleted the WRITE
                    // from write visibility, downstream reads rendered BARE,
                    // and rename-exempt bare facts (preconditions, path/
                    // semantic guards) unified across the invisible write — a
                    // measured false PROOF (`tests/dropped_def_write_visibility.rs`).
                    // The write stays visible via
                    // `generate::extend_with_assigned_place_dests`, which
                    // unions every raw statement destination into the gen-sets
                    // regardless of whether a def was emitted here.
                    //
                    // Trust (2026-10-13, BARE-BINOP-LITERAL-LHS-WIDTH-1): the
                    // `(width, signed)` the wrap is modelled at comes from the
                    // DESTINATION, with each operand checked against it
                    // (`bare_binop_machine_shape`), not from `lhs_ty`. A MIR
                    // `Add`/`Sub`/`Mul` has one type for both operands and the
                    // result, but `operand_ty` of a width-less `ConstValue::Int`
                    // LEFT operand is derived from its VALUE (i64), so `1 + x`
                    // on `i32` was modelled as wrapping at 2^64 with i64 operand
                    // ranges: the i32 wrap was never representable, and with
                    // checks off `ensures result > x` PROVED while the binary
                    // returns `i32::MIN`. The `x + 1` twin read the place's
                    // width and was right. Shapes that disagree drop the def
                    // (the write stays visible, as above).
                    if matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
                        if matches!(op, BinOp::Mul) {
                            continue;
                        }
                        let Some((width, signed)) = bare_binop_machine_shape(func, place, lhs, rhs)
                        else {
                            continue;
                        };
                        let l = cached_l.unwrap_or_else(|| {
                            operand_to_formula_with_array_ctx(func, lhs, Some(&read_ctx))
                        });
                        let r = cached_r.unwrap_or_else(|| {
                            operand_to_formula_with_array_ctx(func, rhs, Some(&read_ctx))
                        });
                        let Some(wrap) =
                            crate::generate::wrapping_binop_modular_ite(*op, &l, &r, width, signed)
                        else {
                            continue;
                        };
                        defs.push(crate::range::input_range_constraint(&l, width, signed));
                        defs.push(crate::range::input_range_constraint(&r, width, signed));
                        wrap
                    } else {
                        let l = cached_l.unwrap_or_else(|| {
                            operand_to_formula_with_array_ctx(func, lhs, Some(&read_ctx))
                        });
                        let r = cached_r.unwrap_or_else(|| {
                            operand_to_formula_with_array_ctx(func, rhs, Some(&read_ctx))
                        });
                        // Trust #integrity: fail closed — skip the def
                        // (a dropped hypothesis), never panic mid-verification.
                        match crate::chc::try_binop_to_formula(*op, l, r, width, signed) {
                            Ok(formula) => formula,
                            Err(_) => continue,
                        }
                    }
                }
            }
            Rvalue::UnaryOp(trust_types::UnOp::Neg, op) => {
                // Float negation is EXACT (a sign-bit flip): define
                // FpFromBits(dest) = fp.neg(FpFromBits(op)) and `continue`
                // (the dest is BitVec; integer `Formula::Neg` would be ill-sorted
                // on a float bit pattern). Fail-closed on non-IEEE widths.
                if let Some(Ty::Float { width }) = crate::operand_ty_cow(func, op).as_deref() {
                    if let Some(def) = fp_neg_value_def(func, op, &dest_name, *width) {
                        defs.push(def);
                    }
                    continue;
                }
                // Trust (2026-10-05, NEG-WRAP-OFF-1): rustc MIR defines the integer
                // `Neg` as WRAPPING — `-MIN == MIN`. The overflow check, when the
                // session has one, is NOT part of the operation: it is the separate
                // `Assert(OverflowNeg)` terminator that dominates the `Neg`, so with
                // checks ON no `MIN` reaches this statement on any path, and with
                // checks OFF (`-Coverflow-checks=off`, honored by memory-safe and
                // advisory) `MIN` does reach it and the result is `MIN`. The bare
                // `Neg` is therefore the wrapping case under BOTH settings — the
                // `Shl`/`Shr` (SHIFT-1) and plain `Add`/`Sub`/`Mul` (arm above)
                // reasoning, for the last integer op it had not reached.
                //
                // The old def was the mathematical `dest == -x`, FALSE of the
                // `x == MIN` execution. Conjoined beside the wrap-exact return pin
                // (`chc::rvalue_to_formula_with_dest`, which spells the same `Neg`
                // as `BvToInt(0 -w x)`), the two contradicted each other at `MIN`, so
                // the postcondition query was UNSAT exactly where it fails:
                // `fn abs_like(x: i32) -> i32 ensures result >= 0 { if x < 0 { -x }
                // else { x } }` PROVED under memory-safe and advisory with checks off,
                // and returns `-2147483648`. Now the def is exact:
                // `dest == ite(x == MIN, MIN, -x)`. Off `MIN` it is the old def node
                // for node (`Formula::Neg`, linear), so every lane that read the old
                // def reads the same term there; the `Ite` is lifted to guarded
                // equalities by the general term-`Ite` elimination, as for the
                // binop arm's modular `Ite`. The operand's type range is pushed
                // FIRST — true of every execution, it keeps a refute-direction model
                // from choosing an out-of-range operand, and the pre-`Eq` order is
                // the binop arm's clobber-dedup rationale. With checks on, the
                // `AssertHolds` path guard `x != MIN` selects the `-x` branch.
                //
                // Width comes from the DESTINATION (a MIR `Neg`'s result type is its
                // operand type): a width-less `ConstValue::Int` operand reports a
                // VALUE-derived width (`i64` for `i32::MIN`), the wrong-width hazard
                // recorded at `generate::wrapping_neg_call_dest_value`. A PLACE
                // operand whose type disagrees, an unsigned destination (no Rust
                // `Neg` produces one) or a non-integer one drops the def: fail-closed
                // for the hypothesis, and the write itself stays visible through
                // `generate::extend_with_assigned_place_dests`.
                let Some((width, true)) = bare_neg_machine_shape(func, place, op) else {
                    continue;
                };
                let value = operand_to_formula_with_array_ctx(func, op, Some(&read_ctx));
                let Some(wrapped) = bare_neg_wrap_ite(&value, width) else { continue };
                defs.push(crate::range::input_range_constraint(&value, width, true));
                wrapped
            }
            Rvalue::UnaryOp(trust_types::UnOp::Not, op) => {
                Formula::Not(Box::new(operand_to_formula_with_array_ctx(func, op, Some(&read_ctx))))
            }
            Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, op) => {
                match crate::ptr_metadata_model(func, op) {
                    crate::PtrMetadataModel::Length(formula) => formula,
                    crate::PtrMetadataModel::Unit
                    | crate::PtrMetadataModel::Unsupported
                    | crate::PtrMetadataModel::Invalid => continue,
                }
            }
            // Trust: `_N = Len(s)` ties the length temp `_N` to the slice's
            // `<s>__slice_len` symbol — the SAME symbol the index/bounds obligation
            // uses (rvalue_safety::collection_len_formula). Without this fact, a
            // dominating guard `index < s.len()` (resolved to `Lt(index, _N)`) is
            // name-disjoint from the obligation `Ge(index, s__slice_len)` and cannot
            // discharge it — a false-positive `index_out_of_bounds`. Mirrors the
            // `PtrMetadata` arm above (and `Rvalue::Len` is already treated this way
            // in generate.rs). `Len` IS the slice length, so the emitted
            // `Eq(Var(_N), s__slice_len)` is a model tautology (sound, monotone).
            Rvalue::Len(place) => match crate::place_slice_len_formula(func, place) {
                Some(formula) => formula,
                None => continue,
            },
            Rvalue::Cast(op, to_ty) => {
                let op_ty = crate::operand_ty_cow(func, op);
                let op_ty_ref = op_ty.as_deref();
                // push the source-width range on the result FIRST, so the
                // clobber-dedup below (which keys staleness on each `Eq` lhs) sees the
                // range before this cast's own `dest == source` equality inserts `dest`
                // into the clobbered set — otherwise the range would be dropped as
                // "stale against its own dest". The range is a value-preserving-widening
                // tautology, so at worst its omission costs precision, never soundness.
                if let Some(range) = widening_cast_result_range_with_ty(op_ty_ref, to_ty, &dest_name)
                {
                    defs.push(range);
                }
                // Trust (drop-in cast type-tracking): a narrowing / reinterpreting
                // int->int cast carries no CastOverflow VC (defined behavior); track
                // the type change so downstream stays sound + precise by bounding the
                // dest to its TARGET-type range. Push BEFORE the `dest == source`
                // equality (same clobber-dedup ordering rationale as the widening
                // range above).
                if let Some(range) = narrowing_cast_result_range_with_ty(op_ty_ref, to_ty, &dest_name)
                {
                    defs.push(range);
                    if let Some(value) =
                        narrowing_cast_value_fact_with_ty(func, op, op_ty_ref, to_ty, &dest_name)
                    {
                        defs.push(value);
                    }
                }
                // Trust (2026-10-11, VC-NARROW-CAST-FALSE-REFUTE-1): the same narrowing
                // cast IS the identity on every source its target type represents:
                // `(to_min <= src <= to_max) => dest == src`, vacuous outside, so it never
                // contradicts the range above. Without it the result was a FREE value of
                // the target and `arr[x as u8 as usize]` under `x < 0x80` was refuted at
                // `dest = 128`. Pushed BEFORE the `dest == source` equality (same
                // clobber-dedup ordering as the ranges); the staleness kill below drops it
                // when a later statement writes `src` or `dest` — since UNION-SIBLING-WRITE-1
                // (2026-10-12) also a write of a UNION SIBLING of either, which the place
                // names took for disjoint storage (`path_defs::union_write_cover_name`).
                if let Some(identity) =
                    narrowing_cast_in_range_identity_with_ty(func, op, op_ty_ref, to_ty, &dest_name)
                {
                    defs.push(identity);
                }
                // An array→slice unsize coercion keeps the source array's STATIC
                // length; tie it, or the coerced slice's length is a free var.
                // Pushed BEFORE the `dest == source` equality for the same
                // clobber-dedup ordering reason as the two ranges above.
                push_unsize_slice_len(
                    func,
                    &dest_name,
                    op,
                    op_ty_ref,
                    to_ty,
                    &mut defs,
                    &mut seen_dests,
                );
                push_cast_slice_len(func, place, &dest_name, op, &mut defs, &mut seen_dests);
                // Trust (verified-sysroot §5 step 3, slice 2): when the expose
                // cast's SOURCE pointer provably roots at a model-covered
                // allocation (`&x`/`&raw x` of a whole local of statically
                // sized scalar/array sort, through unique thin-identity defs),
                // bound the minted ADDRESS by the model's two axioms — never
                // null, one-past-end representable. This is what turns the
                // `*mut T::add::precondition_check` overflow legs from
                // STATABLE into PROVABLE on covered shapes. Pushed BEFORE the
                // `dest == source` equality (clobber-dedup ordering, as the
                // ranges above). Fail-closed: an unrooted / reassigned /
                // projected / non-covered source mints NOTHING.
                if let Some(bounds) =
                    alloc_model_expose_root_bounds_with_ty(func, op, op_ty_ref, to_ty, &dest_name)
                {
                    defs.push(bounds);
                }
                match cast_definition_formula_with_ty(func, place, op, op_ty_ref, to_ty) {
                    Some(formula) => formula,
                    None => continue,
                }
            }
            Rvalue::Aggregate(kind, operands) => {
                // Trust (ENC-DEFECTS 13a, 2026-09-26): constructing a FIELDLESS
                // (C-like) enum value defines that value's integer model to be the
                // variant's DECODED discriminant tag — see
                // [`fieldless_enum_construction_tag`] for the model and every gate.
                // The `Discriminant` arm below reads the same name back, so a
                // `match` on the value is tied to the branch that built it through
                // the ordinary place versioning (the defect: `let m = if c { A }
                // else { B }; match m { A => x + 1, .. }` refuted at `c == false`
                // with the read `_4 = 1` and the carrier `discr_m = 0` unrelated).
                //
                // The mutably-borrowed-whole-local gate is the construction-fact
                // gate of the payload arm just below (hunt-7), applied for the same
                // reason: a store through a `&mut` of the local is only killed by
                // the whole-function havoc, so dropping the fact at the source is
                // the fail-closed direction.
                if let AggregateKind::Adt { variant, active_field: None, .. } = kind
                    && operands.is_empty()
                    && let Some(tag) = fieldless_enum_construction_tag(func, place, *variant)
                {
                    let dest_sort = crate::place_sort(func, place).unwrap_or(Sort::Int);
                    if dest_sort != Sort::Int
                        || (place.projections.is_empty()
                            && local_is_mutably_borrowed(func, place.local))
                    {
                        continue;
                    }
                    defs.push(Formula::Eq(
                        Box::new(Formula::Var(dest_name, dest_sort)),
                        Box::new(Formula::Int(tag)),
                    ));
                    continue;
                }
                // Trust: whole-array CONSTRUCTION of an eligible array-theory local
                // — seed `v0 == Store(Store(.. Store(FREE_base, 0, e0) ..), N-1,
                // eN-1))` so element reads via `Select(v0, c)` resolve. This bypasses
                // the scalar aggregate_field_definitions / `[c;min=len]` path.
                if matches!(kind, AggregateKind::Array)
                    && place.projections.is_empty()
                    && let Some(model) = crate::array_theory_local(func, place.local)
                {
                    if let Some(seed) = array_construction_seed(
                        func,
                        place.local,
                        &model.elem_sort,
                        operands,
                        &read_ctx,
                    ) {
                        defs.push(seed);
                    }
                    continue;
                }
                // SOUNDNESS (P0 false proof, 2026-06-17 hunt-7): suppress the construction field
                // facts `place@k.i == op_i` when `place` is mutably borrowed anywhere — `&mut place`
                // or `place.as_mut()` (any call taking `&mut place`) can REASSIGN the payload AFTER
                // construction (`let mut o=Some(a.min(3)); if let Some(r)=o.as_mut(){*r=b;} match o {
                // Some(i)=>arr[i] }`), so a propagated `o@1.0 == _5` is STALE and vacuously discharges
                // the `arr[i]` bounds obligation on the mutated payload `i==b` (OOB). The downstream
                // kill machinery does not remove it (the demux re-injects, and the `*r=b` Deref-store
                // through the returned `&mut` is not tracked as a write to `o`), so drop it at the
                // SOURCE. Fail-closed FOR THE HYPOTHESIS: losing a construction fact only turns
                // PROVE -> not-proved. The aggregate WRITE itself stays gen-set-visible via
                // `generate::extend_with_assigned_place_dests` even when every field fact is
                // suppressed here.
                if !operands.is_empty()
                    && !(place.projections.is_empty()
                        && local_is_mutably_borrowed(func, place.local))
                {
                    let mut field_defs = aggregate_field_definitions(func, place, kind, operands);
                    for (field_name, field_def) in field_defs.drain(..).rev() {
                        if seen_dests.insert(field_name) {
                            defs.push(field_def);
                        }
                    }
                }
                continue;
            }
            // Trust: `[op; count]` construction of an eligible array-theory local
            // is the constant array of `op` (`array_repeat_seed`), whatever `count`.
            Rvalue::Repeat(op, _count) => {
                if place.projections.is_empty()
                    && let Some(model) = crate::array_theory_local(func, place.local)
                    && let Some(seed) =
                        array_repeat_seed(func, place.local, &model.elem_sort, op, &read_ctx)
                {
                    defs.push(seed);
                }
                continue;
            }
            // A shared borrow `r = &P` implies `*r == P`. The compiler lowers a
            // match-guard binding by reference (`_4 = &payload; guard tests
            // *_4`) while the arm body reads the payload by value, so without
            // this the guard constrains a free `*r` variable disconnected from
            // the value the arm uses — and a guarded binding like
            // `Some(v) if v < K => v + 1` false-fails. Connecting the deref name
            // to the referent fixes it. Sound for shared refs (P cannot be
            // mutated through an immutable borrow). `&mut` is deliberately
            // skipped: a later `*r = ..` could invalidate the equality.
            //
            // `place_to_var_name` renders a trailing `Deref` projection as a
            // `*` suffix, so the deref place's name is exactly `dest_name + "*"`.
            Rvalue::Ref { place: referent, mutable: false } => {
                let deref_name = format!("{dest_name}*");
                if seen_dests.insert(deref_name.clone()) {
                    let sort = crate::place_sort(func, referent).unwrap_or(Sort::Int);
                    defs.push(Formula::Eq(
                        Box::new(Formula::Var(deref_name, sort.clone())),
                        Box::new(Formula::Var(crate::place_to_var_name(func, referent), sort)),
                    ));
                }
                push_borrow_slice_len(func, &dest_name, referent, &mut defs, &mut seen_dests);
                continue;
            }
            // A MUTABLE borrow `r = &mut P` cannot change the referent slice's
            // LENGTH — a slice's length metadata is immutable through `&mut [T]`
            // (only its ELEMENTS are mutable) — so, exactly like `AddressOf` below
            // and `push_borrow_slice_len`'s own contract, tie the length. We do NOT
            // tie the deref-VALUE equality here (that IS unsound for `&mut`, since a
            // later `*r = ..` could invalidate it — the shared arm above owns it).
            // This lets a guarded `&mut [T]` op — `if i < s.len() { *s.get_unchecked_mut(i) = v }`
            // — discharge: the guard's `s.len()` and the `&mut (*s)` receiver
            // reborrow resolve to the same `{param}__slice_len`. SOUND: the emitted
            // `{dest}__slice_len == referent_len` is a TRUE fact (a reborrow
            // preserves length), so conjoining it removes no real model.
            Rvalue::Ref { place: referent, mutable: true } => {
                push_borrow_slice_len(func, &dest_name, referent, &mut defs, &mut seen_dests);
                continue;
            }
            // `r = &raw const/mut P` (e.g. the `FakeForPtrMetadata` pointer that
            // `<[T]>::len()` reads on a `&mut [T]`). Tie the pointer's slice length
            // to the referent slice's so a `PtrMetadata(r)` read recovers it.
            Rvalue::AddressOf(_mutable, referent) => {
                push_borrow_slice_len(func, &dest_name, referent, &mut defs, &mut seen_dests);
                continue;
            }
            // Trust (ENC-DEFECTS 13a, 2026-09-26): the discriminant READ of a
            // FIELDLESS enum place is that place's integer model, which the
            // construction arm above pins to the variant's decoded tag. The def is a
            // pure place-read (`d == p`, the shape a `Use` copy mints), so it rides
            // exactly the versioning a copy does: a later write of `p` — or of any
            // ancestor of a projected `p` such as `self*.2` — rebinds the name and a
            // stale def cannot reach a read after it. Every gate is in
            // [`fieldless_enum_discriminant_read_def`].
            Rvalue::Discriminant(src) => {
                match fieldless_enum_discriminant_read_def(func, place, src, &read_ctx)
                    .or_else(|| crate::enum_entry::discriminant_read(func, place, src))
                {
                    Some(value) => value,
                    None => continue,
                }
            }
            // Skip complex rvalues — not needed for basic dataflow tracking.
            _ => continue,
        };

        let dest_sort = crate::place_sort(func, place).unwrap_or(Sort::Int);
        defs.push(Formula::Eq(
            Box::new(Formula::Var(dest_name, dest_sort)),
            Box::new(rvalue_formula),
        ));
    }

    // Tag the defs of the last statement visited.
    if let Some(prev) = last_idx {
        stmt_of.resize(defs.len(), prev);
    }
    debug_assert_eq!(stmt_of.len(), defs.len(), "every extracted def carries its statement index");
    if defs.is_empty() {
        return Vec::new();
    }

    // Trust: drop any def whose rvalue mentions a local a *later* statement in
    // this block overwrites. `defs` is in reverse program order here (the last
    // statement's defs first), so a front-to-back walk meets later statements
    // before earlier ones; a fact is stale exactly when one of its operands is
    // the destination of an already-visited (later) statement. Retaining such a
    // fact is unsound: `c = m < 1000; m = BIG;` would otherwise emit
    // `c == (m < 1000)` against the post-`m = BIG` value of `m`, and inside a
    // later `if c { m + 1 }` the contradictory hypotheses vacuously discharge the
    // overflow VC — a false-PROVE of a real overflow. The same-block last-write
    // dedup above only catches a redefined *destination*; this catches a
    // redefined *operand*. Dropping a fact only removes a hypothesis, so it can
    // introduce a false-FAIL but never a false-PROVE.
    //
    // Trust: 2026-09-16 (round A11) — TWO CHANGES to what `clobbered` holds and
    // whom it may drop, both measured on real MIR (`tests/escaped_local_seam_realmir.rs`,
    // the `rev11*` rows):
    //
    //  1. THE DEF'S OWN SUBJECT IS NOT EXEMPT. The old walk skipped a free variable
    //     equal to the def's lhs (`Some(v) != lhs`), on the argument that an exact
    //     later redefinition is already resolved by the `seen_dests` last-write
    //     dedup. That is true only of EXACT redefinition. A def keyed on a PROJECTED
    //     name is rebound by a later write of any name inside or above it — the
    //     index local embedded by number (`j = k` rebinds `s*[_j]`, through the
    //     fallback `_j` round A10 put into this very set), the prefix ancestor
    //     (`p = q` rebinds `p.0`; `a = q` rebinds `a[0]`), a symbolic-index alias
    //     (`a[_i] = w` rebinds `a[0]`) — and the store def `s*[_4] == 3`, whose
    //     ONLY free variable is its lhs, sailed through the exemption. It then flowed
    //     to the successor through `v2_path_def_fixpoint`, was renamed at the use
    //     point onto the same reaching token as the post-reseat read, and
    //     `s[j] = 3; j = k; t[s[j] as usize]` PROVED kernel-certified while it panics
    //     at runtime (`store_reseat_read_bug`, `-O1`). Now the subject is tested like
    //     every other free variable against every later write. An exact later
    //     write must drop the def too when it emits no replacement definition
    //     (for example, a pointer copy). ONE exemption survives, on the
    //     ESTABLISH-VERSIONED extraction only (`keep_versionable_read_defs`): a
    //     subject the consumer pins at the def's OWN statement (`k`, carried in the
    //     returned index — a plain `Var` lhs with no `#`, not an `arr$` term) names
    //     the value just after that statement, and a later rebinding write mints a
    //     DIFFERENT token for every read after it (`stmt_writes_name` tests the same
    //     `write_rebinds` per statement), so the pinned def and the post-write read
    //     are name-disjoint by construction. Callers of the versioned extraction
    //     therefore MUST pass `k + 1` as the establish search bound (they do:
    //     `extract_block_definitions_until_versioned_indexed`).
    //
    //  2. `clobbered` CARRIES THE WRITE SET OF EVERY LATER STATEMENT, not only
    //     the lhs of every later EMITTED def — the "known residual" this comment
    //     used to record. A declined write (a bare `Mul`, a non-constant `Rem`, an
    //     unsupported cast, a `&mut` borrow, `CheckedBinaryOp`, the catch-all) is a
    //     write all the same; with per-def statement indices in hand the cursor walk
    //     below adds each statement's write names (dest, its derived
    //     `__slice_len` twin, the index fallback `_l`, or a pointer-copy havoc)
    //     exactly as the gen-sets carry them (`generate::stmt_direct_write_names`),
    //     BEFORE any def of an earlier
    //     statement is tested. Dropping more facts is the monotone direction.
    //
    // The clobber set is an incremental rebinder index (`RebindSet`): the staleness
    // test below asks it once per free variable of every def, and a scan of the set
    // per question made this walk quadratic in the block.
    let defs_len = defs.len();
    let mut cursor = end_stmt_exclusive.min(block.stmts.len());
    if defs_len == 1 && cursor <= stmt_of[0] + 1 {
        let mut iter = defs.into_iter();
        return match iter.next() {
            Some(d) => vec![(stmt_of[0], d)],
            None => Vec::new(),
        };
    }
    let mut clobbered = crate::generate::rebind_index::RebindSet::default();
    #[cfg(test)]
    let diff = crate::generate::differential_enabled();
    #[cfg(test)]
    let mut clobbered_reference: Vec<String> = Vec::new();
    #[cfg(test)]
    let mut stmt_writes: FxHashSet<String> = FxHashSet::default();
    // Every statement with index >= `cursor` has had its raw write names added.
    let mut kept: Vec<(usize, Formula)> = Vec::with_capacity(defs_len);
    for (idx, (d, k)) in defs.into_iter().zip(stmt_of).enumerate() {
        while cursor > k + 1 {
            cursor -= 1;
            crate::generate::stmt_direct_write_rebind_set(
                func,
                &block.stmts[cursor],
                &mut clobbered,
            );
            #[cfg(test)]
            if diff {
                stmt_writes.clear();
                crate::generate::stmt_direct_write_names(
                    func,
                    &block.stmts[cursor],
                    &mut stmt_writes,
                );
                clobbered_reference.extend(stmt_writes.iter().cloned());
            }
        }
        let lhs: Option<&str> = match &d {
            Formula::Eq(l, _) => l.var_name(),
            _ => None,
        };
        // Trust (ARM-B, versioned-consumer relax): a PURE PLACE-READ def
        // (`Eq(Var(_t), Var(place))` from `_t = Copy/Move(place)`) survives the
        // staleness kill on the establish-point-versioned path — the consumer
        // stamps the RHS read at the def's own statement, so a later clobber of
        // the read place mints a DIFFERENT token and cannot unify (see
        // `extract_block_definitions_until_versioned`). Computed defs keep the
        // kill: their hazard example (`c = m < 1000; m = BIG`) stays dropped.
        let versionable_read_def = keep_versionable_read_defs
            && matches!(&d, Formula::Eq(l, r)
                if l.var_name().is_some() && r.var_name().is_some());
        // The subject-pin exemption of change (1): only on the versioned extraction,
        // only for a subject `version_block_def_at_establish` will pin at `k`.
        let subject_pinned = keep_versionable_read_defs
            && lhs.is_some_and(|l| !l.contains('#') && !l.starts_with("arr$"));
        // Prefix-aware (soundness round-11): a fact is stale if a free
        // variable OVERLAPS a clobbered place (e.g. clobbering `x` invalidates a
        // fact mentioning `x.0`), not only on exact-name equality.
        // Trust (round A10): `c` is the CLOBBERED (written) name, `v` the read —
        // `write_rebinds` is directional and is called written-first.
        let stale = !versionable_read_def
            && !clobbered.is_empty()
            && trust_types::any_free_variable_name(&d, &mut |v| {
                let is_subject = lhs == Some(v);
                if is_subject && subject_pinned {
                    return false;
                }
                let stale = clobbered.any_rebinder(v);
                #[cfg(test)]
                if diff {
                    assert_eq!(
                        stale,
                        clobbered_reference.iter().any(|c| crate::generate::write_rebinds(c, v)),
                        "RebindSet disagrees with the clobber scan on `{v}`"
                    );
                }
                stale
            });
        if idx + 1 < defs_len
            && let Some(l) = lhs
        {
            // Trust: 2026-09-16 (round A8) — DERIVE-AWARE. A whole write of a slice
            // reference `s` also rebinds its length metadata name `s__slice_len`, which
            // `place_names_overlap` (a place-PREFIX relation) does not reach; the same
            // extension `conservative_snapshot_writes` and the gen-sets already carry.
            // Without it a length tie emitted before the write (`_8__slice_len ==
            // s__slice_len`, then `s = b`) survives this kill on the UNversioned
            // consumer path and reads the post-write length.
            clobbered.insert_with_derived_slice_len(l);
            #[cfg(test)]
            if diff {
                if !l.ends_with(crate::generate::SLICE_LEN_SUFFIX) {
                    clobbered_reference.push(format!("{l}{}", crate::generate::SLICE_LEN_SUFFIX));
                }
                clobbered_reference.push(l.to_string());
            }
            // Trust: 2026-09-16 (round A10) — INDEX-AWARE, the same way. A whole write
            // of an index local `j` (canonical spelling `j`) rebinds every name that
            // embeds it by number (`s*[_3]`); the fallback `_3` is the written
            // spelling `write_rebinds` reaches those names through, so it joins the
            // clobber set beside the canonical name exactly as the gen-sets carry it.
            if !l.bytes().any(crate::is_projection_segment_lead)
                && !l.ends_with(crate::generate::SLICE_LEN_SUFFIX)
                && let Some(local) = crate::fn_memo::whole_local_index_by_base(func, l, |i| {
                    crate::place_to_var_name(func, &trust_types::Place::local(i))
                })
                && crate::generate::local_is_index_operand(func, local)
            {
                let fallback = crate::generate::local_fallback_name(local);
                clobbered.insert(&fallback);
                #[cfg(test)]
                if diff {
                    clobbered_reference.push(fallback);
                }
            }
        }
        if !stale {
            kept.push((k, d));
        }
    }

    kept.reverse();
    kept
}

/// Every name a block may write while a proof snapshot is being transported,
/// or `None` when the statement surface is not known to be value-transparent.
///
/// `generate::block_written_names` supplies the canonical alias-aware set
/// (including opaque dereference havoc and terminator destinations). Add every
/// explicit place destination as a belt-and-suspenders gate because ordinary
/// definition extraction intentionally declines some rvalues. Unknown/future
/// statements fail closed: a newly added write-capable variant must never
/// silently preserve a stale branch or checked-arithmetic snapshot.
fn block_has_transparent_snapshot_stmt_surface(block: &BasicBlock) -> bool {
    block.stmts.iter().all(|stmt| {
        matches!(
            stmt,
            Statement::Assign { .. }
                | Statement::SetDiscriminant { .. }
                | Statement::Deinit { .. }
                | Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Retag { .. }
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop
        )
    })
}

fn conservative_snapshot_writes(
    func: &VerifiableFunction,
    block: &BasicBlock,
) -> Option<FxHashSet<String>> {
    if !block_has_transparent_snapshot_stmt_surface(block) {
        return None;
    }
    // `block_written_names` already runs `extend_with_assigned_place_dests` and
    // `extend_with_derived_slice_len` over `block.stmts`, so every `Assign` /
    // `SetDiscriminant` / `Deinit` destination and its `{dest}__slice_len` twin is
    // included even when definition extraction declined the rvalue.
    Some(crate::generate::block_written_names(func, block))
}

/// Recover the merged-local invariant at an n-arm `SwitchInt` join.
///
/// The path-definition BFS weakens to `true` at any join reached with differing
/// accumulated defs, which turns a branch-merged local (`let x = match e { A =>
/// a, B => b, C => c }`) into a free variable that a solver then false-refutes.
/// When every predecessor of `join` is a single-predecessor `Goto(join)` arm and
/// all those arms descend from the *same* `SwitchInt`, the arms partition every
/// execution reaching `join`: a switch takes exactly one successor, so the arm
/// guards are mutually exclusive and — restricted to paths that actually reach
/// `join` — exhaustive. The equality
/// `x == Ite(g_0, x_0, Ite(g_1, x_1, … x_last))` therefore holds on every
/// incoming path, so emitting it is sound and lets bounded-overflow VCs over `x`
/// discharge. (The two-arm diamond `if c { a } else { b }` is the n=2 instance
/// and is encoded byte-identically to before.)
///
/// Soundness of the catch-all `else`: the last arm's guard is dropped, so the
/// `else` value is claimed whenever no earlier guard fires. On any execution
/// that *reaches* `join` the discriminant equals one arm's value, so the `else`
/// is only reached when the last arm was genuinely taken. The phantom region
/// (discriminant values that route to a divergent/unreachable `otherwise` and so
/// never reach `join`) is unconstrained, but those paths are exactly the ones
/// excluded from `join`, so no reachable join-path is misconstrained.
///
/// The `if`-without-`else` shape is the same partition with one arm elided: the
/// switch jumps *directly* to `join` on the skip edge, so the switch block itself
/// is one of `join`'s predecessors. That edge is the `else` arm whose merged value
/// is the local's value at the switch's own exit (no statement runs between the
/// switch and the join). Modelling it this way is what lets a safe
/// `let mut s = 0; if c { s = K; } s + 1` prove while an unguarded
/// `if c { s = K; } s + b` correctly fails — without it the join keeps a stale,
/// unsound `s == 0` that vacuously discharges the overflow VC.
///
/// Returns one `Eq(Var(local), Ite(..))` per local defined in *every* arm.
/// Any deviation from the strict partition shape yields an empty vec.
///
/// `incoming` is the converged (pre-merge) path-definition map — each block's
/// entry-fact intersection across every path that reaches it. It supplies the
/// skip-edge value of a local the switch block does not itself assign (see the
/// augmentation block below). Pass an empty map to disable that augmentation;
/// clean diamonds and same-block-init shapes are unaffected by it.
///
/// # Two lanes
///
/// This is the dispatcher. [`single_switch_branch_merge_definitions`] handles the
/// original shape — every join arm descends from ONE `SwitchInt`. When it declines
/// (empty vec), [`nested_switch_branch_merge_definitions`] retries the join as a
/// *nested* switch chain (`if / else if / else`, whose arms descend from two or
/// more switches). The nested lane requires at least two distinct switches, so it
/// can never fire on a shape the single-switch lane already models: the two lanes
/// are disjoint and the single-switch lane's behaviour is unchanged.
pub(crate) fn branch_merge_definitions(
    func: &VerifiableFunction,
    join: BlockId,
    incoming: &FxHashMap<BlockId, Vec<Formula>>,
) -> Vec<Formula> {
    if join.0 >= func.body.blocks.len() {
        return Vec::new();
    }
    let preds = crate::generate::block_predecessors_rc_for(func);
    branch_merge_definitions_with_preds(func, join, incoming, &preds)
}

pub(crate) fn branch_merge_definitions_with_preds(
    func: &VerifiableFunction,
    join: BlockId,
    incoming: &FxHashMap<BlockId, Vec<Formula>>,
    preds: &[Vec<BlockId>],
) -> Vec<Formula> {
    if preds.get(join.0).is_none_or(|p| p.len() < 2) {
        return Vec::new();
    }
    // ONE predecessor computation shared by both lanes. It is an O(blocks) scan
    // and this dispatcher runs once per block of the function, so recomputing it
    // per lane doubles a hot loop for no benefit.
    let single = single_switch_branch_merge_definitions(func, join, incoming, preds);
    if !single.is_empty() {
        return single;
    }
    nested_switch_branch_merge_definitions(func, join, preds)
}

/// One join's exact single-`SwitchInt` partition, as admitted by
/// [`single_switch_join_partition`]: every execution reaching the join came from
/// `switch_id` through exactly one def-source, selected by the switch value(s)
/// beside it (`explicit`), or by none of them (`else_source`).
struct SingleSwitchJoinPartition<'a> {
    switch_id: BlockId,
    discr: &'a Operand,
    explicit: Vec<(BlockId, Vec<u128>)>,
    else_source: BlockId,
}

/// The partition half of [`single_switch_branch_merge_definitions`], shared with
/// [`switch_join_variant_arm_definitions`] (Trust, 2026-10-07,
/// MATCH-ARM-CALL-CHAIN). `None` on any deviation from the strict shape.
fn single_switch_join_partition<'a>(
    func: &'a VerifiableFunction,
    join: BlockId,
    preds: &[Vec<BlockId>],
) -> Option<SingleSwitchJoinPartition<'a>> {
    let blocks = &func.body.blocks;
    if join.0 >= blocks.len() {
        return None;
    }
    let join_preds = &preds[join.0];
    // A merge needs at least two incoming arms.
    if join_preds.len() < 2 {
        return None;
    }
    // Classify each join predecessor. A *Goto arm* is a single-predecessor
    // `Goto(join)` block — the body of one switch branch. A *direct* predecessor
    // is the switch block itself flowing straight into the join: the skip edge of
    // an `if` without an `else` (`if c { s = .. } use(s)` lowers the false case to
    // a direct switch→join edge). A clean diamond has only Goto arms; an
    // if-without-else has exactly one direct predecessor (the switch).
    let is_goto_arm = |p: BlockId| {
        matches!(&blocks[p.0].terminator, Terminator::Goto(t) if *t == join)
            && preds[p.0].len() == 1
    };
    let mut goto_arms: Vec<BlockId> = Vec::with_capacity(join_preds.len());
    let mut direct_switch: Option<BlockId> = None;
    for &p in join_preds {
        if is_goto_arm(p) {
            goto_arms.push(p);
        } else if direct_switch.is_none()
            && matches!(blocks[p.0].terminator, Terminator::SwitchInt { .. })
        {
            direct_switch = Some(p);
        } else {
            // More than one non-Goto predecessor (or a non-SwitchInt direct
            // predecessor) is not a switch partition we model.
            return None;
        }
    }
    if goto_arms.is_empty() {
        return None;
    }

    // The nearest switch predecessor of a join arm, through the authenticated
    // straight-line hops [`branch_arm_switch_chain`] admits (none, a checked-op
    // `Assert` success edge, a `Call` normal-return edge, or a short chain of
    // them). Ordinary Goto/Drop hops remain rejected.
    // Identify the single `SwitchInt` every arm descends from, short-circuiting
    // on the first arm that either lacks an admitted chain or descends from a
    // different switch.
    let mut expected_switch = direct_switch;
    let mut arm_chains: FxHashMap<BlockId, (BlockId, Vec<BlockId>)> =
        FxHashMap::with_capacity_and_hasher(goto_arms.len(), Default::default());
    for &arm in &goto_arms {
        let (switch, hops) = branch_arm_switch_chain(func, preds, arm)?;
        match expected_switch {
            Some(s) if s != switch => return None,
            None => expected_switch = Some(switch),
            Some(_) => {}
        }
        arm_chains.insert(arm, (switch, hops));
    }
    let switch_id = expected_switch?;

    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &blocks[switch_id.0].terminator
    else {
        return None;
    };

    // A merge equality needs the switch guard's exact characteristic function,
    // not the precision-oriented guard assumption used by ordinary VCs (that
    // API may deliberately weaken a predicate's false arm to `true`). Validate
    // every raw table value now, including values that may later become the
    // catch-all arm, and reject duplicate values even when malformed TrustIR
    // routes them to different destinations. Also reject an `otherwise` that
    // appears as an explicit target up front before walking arm write sets.
    let mut seen_values = FxHashSet::default();
    if targets.iter().any(|(value, target)| {
        target == otherwise
            || !seen_values.insert(*value)
            || exact_switch_value_guard(func, discr, *value).is_none()
    }) {
        return None;
    }

    // The raw discriminator denotes its value at the switch. Because formulas
    // here are intentionally unversioned, any write to that place (or an
    // alias/ancestor/descendant) before the join would make an Ite guard read a
    // different value and assert a false merge equality. Check every admitted
    // post-switch block: the direct value arm, plus every hop of its admitted
    // chain (`branch_arm_switch_chain`). Unknown statement effects fail closed.
    // Trust (2026-10-07, MATCH-ARM-CALL-CHAIN): a `Call` hop may write memory the
    // block's write set cannot name (through a `&mut` argument or a pointer the
    // callee reaches). Admit a chain with a `Call` hop only when the selector is
    // a bare local that is never mutably borrowed, so no callee can reach it.
    let chain_has_call = goto_arms.iter().any(|a| {
        arm_chains.get(a).is_some_and(|(_, hops)| {
            hops.iter().any(|h| matches!(blocks[h.0].terminator, Terminator::Call { .. }))
        })
    });
    if chain_has_call {
        let selector_is_private_local = match discr {
            Operand::Copy(place) | Operand::Move(place) => {
                place.projections.is_empty() && !local_is_mutably_borrowed(func, place.local)
            }
            _ => false,
        };
        if !selector_is_private_local {
            return None;
        }
    }
    if !goto_arms.is_empty() {
        let discr_formula = operand_to_formula(func, discr);
        let mut discr_vars: Vec<&str> = Vec::new();
        trust_types::for_each_free_variable_name(&discr_formula, &mut |name| {
            if !discr_vars.contains(&name) {
                discr_vars.push(name);
            }
        });
        for arm in &goto_arms {
            let (_, hops) = arm_chains.get(arm)?;
            for path_block in std::iter::once(arm).chain(hops.iter()) {
                let Some(writes) = conservative_snapshot_writes(func, &blocks[path_block.0]) else {
                    return None;
                };
                if discr_vars.iter().any(|name| {
                    writes.iter().any(|written| crate::generate::write_rebinds(written, name))
                }) {
                    return None;
                }
            }
        }
    }

    // The block whose *exit* state supplies an arm's merged value, given a switch
    // destination `tb`: the join reached directly (the skip edge) takes the
    // switch's own exit; a Goto arm takes that arm block's exit; anything else
    // diverges, never reaches the join, and contributes no arm. Modelling the
    // skip edge as `switch_id`'s exit is sound — no statement runs between the
    // switch and the join on that edge, so the local holds its switch-exit value.
    let arm_source = |tb: BlockId| -> Option<BlockId> {
        if tb == join {
            Some(switch_id)
        } else if goto_arms.contains(&tb) {
            Some(tb)
        } else {
            // `tb` heads an admitted hop chain (`switch -> tb -> .. -> arm`).
            goto_arms.iter().copied().find(|arm| {
                arm_chains
                    .get(arm)
                    .is_some_and(|(s, hops)| *s == switch_id && hops.first() == Some(&tb))
            })
        }
    };

    // Group explicit targets by their def-source, preserving first-seen order and
    // accumulating every routing value (an or-pattern sends several values to one
    // arm). Targets that never reach `join` are dropped.
    let mut explicit: Vec<(BlockId, Vec<u128>)> = Vec::new();
    for (value, target) in targets {
        let Some(src) = arm_source(*target) else {
            continue;
        };
        if let Some((_, values)) = explicit.iter_mut().find(|(b, _)| *b == src) {
            values.push(*value);
        } else {
            explicit.push((src, vec![*value]));
        }
    }

    // Choose the catch-all (`else`) arm's def-source. If `otherwise` reaches the
    // join it is the natural else (its guard is the negation of every target
    // value); otherwise the last explicit arm serves as the else under switch
    // totality.
    let else_source = match arm_source(*otherwise) {
        Some(src) => src,
        None => match explicit.pop() {
            Some((b, _)) => b,
            None => return None,
        },
    };

    // Need at least one guarded arm besides the else to constrain anything.
    if explicit.is_empty() {
        return None;
    }

    // Every join predecessor must be accounted for. A Goto-arm predecessor maps to
    // its own block; the direct (switch) predecessor maps to `switch_id`. The set
    // of def-sources we built must match exactly, or the merge isn't this switch's
    // partition.
    let expected: FxHashSet<BlockId> =
        join_preds.iter().map(|p| if is_goto_arm(*p) { *p } else { switch_id }).collect();
    let mut covered: FxHashSet<BlockId> = explicit.iter().map(|(b, _)| *b).collect();
    covered.insert(else_source);
    if covered != expected {
        return None;
    }

    Some(SingleSwitchJoinPartition { switch_id, discr, explicit, else_source })
}

/// The single-`SwitchInt` merge recogniser — see [`branch_merge_definitions`].
fn single_switch_branch_merge_definitions(
    func: &VerifiableFunction,
    join: BlockId,
    incoming: &FxHashMap<BlockId, Vec<Formula>>,
    preds: &[Vec<BlockId>],
) -> Vec<Formula> {
    let Some(SingleSwitchJoinPartition { switch_id, discr, explicit, else_source }) =
        single_switch_join_partition(func, join, preds)
    else {
        return Vec::new();
    };

    // Per-arm `(name, sort, value)` maps; the else arm sits last. For the exact
    // Assert-success extension, the value arm commonly copies the checked
    // tuple's `.0` field:
    //
    //   checked = CheckedAdd(a, b); Assert(!checked.1) -> arm
    //   arm: merged = checked.0; Goto(join)
    //
    // `checked.0` is not defined on the sibling arm, so the ordinary
    // intersection correctly drops its definition and would leave the merged
    // value free. Inline only the semantic equalities authenticated by that
    // unique Assert-success edge (`checked.0 == a + b`, etc.) into that arm's
    // values. This is not a general predecessor walk: it requires the exact
    // parent/target/switch identity already admitted above, and
    // `extract_assert_passed_semantics` itself requires the checked-op tuple
    // and overflow-flag projection shape.
    let arm_definition_map_with_checked_assert =
        |arm: BlockId| arm_definition_map_with_checked_assert_impl(func, &preds, arm, switch_id);
    let mut arm_defs: Vec<Vec<(String, Sort, Formula)>> =
        explicit.iter().map(|(b, _)| arm_definition_map_with_checked_assert(*b)).collect();
    arm_defs.push(arm_definition_map_with_checked_assert(else_source));

    // if-without-else skip edge. The arm whose def-source is the switch
    // block runs no statement between the switch and the join, so a local it does
    // not itself assign keeps the value it held on entry to the switch. Without
    // this, a local assigned only on the *other* arm (`if c { lo = 0 }`) is absent
    // from the skip arm, never merges, and stays a free variable that false-FAILs a
    // safe `hi - lo`. (The pre-existing path covers only the shape where the switch
    // block ITSELF initialises the local — `s = 0; cmp = ..; switch cmp` — but real
    // MIR routinely splits the initialiser into an ancestor block, e.g. when an
    // earlier checked-arith assert ends the init block.) Fill each missing local
    // with its incoming dominating value from `incoming[switch_id]` — the
    // INTERSECTION of every path reaching the switch, hence a fact true on every
    // such path and not stale (the dataflow kills a fact when any variable it
    // mentions is reassigned). Soundness: this adds a genuinely-true equality, which
    // by monotonicity can only turn a FAIL into a PROVE, never a real overflow into
    // a false-PROVE. Only locals the switch block does not assign are filled, and
    // only when the incoming value is unambiguous (exactly one defining equality);
    // an absent or ambiguous value leaves the local free (a sound false-FAIL, no
    // worse than before this fix).
    let skip_idx = explicit
        .iter()
        .position(|(b, _)| *b == switch_id)
        .or_else(|| (else_source == switch_id).then(|| arm_defs.len() - 1));
    // Trust (2026-10-07, SKIP-FILL-STALE): `incoming[switch_id]` is the switch
    // block's ENTRY state, but the skip edge carries its EXIT state. "A local the
    // switch block does not assign" must therefore mean every name the block
    // WRITES, not only the names it has an extracted def for: definition
    // extraction declines some rvalues (unsigned non-constant `Rem`, casts), and a
    // declined write left its entry-state value in the fill. MEASURED (h_stale2,
    // `x = 1; x = a % b; if k == 0 { x = u64::from(small) + 1 } x + 2`): the fill
    // took `_5 == 1` from bb1's entry, the merge claimed `_5 == ite(.., 1)` and the
    // reachable `x + 2` overflow PROVED. A fill whose VALUE mentions a written name
    // is stale the same way. An unknown write surface declines the whole fill.
    let skip_writes = skip_idx.and_then(|_| {
        func.body
            .blocks
            .get(switch_id.0)
            .filter(|b| b.id == switch_id)
            .and_then(|b| conservative_snapshot_writes(func, b))
    });
    if let Some(skip_idx) = skip_idx
        && let Some(skip_writes) = skip_writes
        && let Some(incoming_defs) = incoming.get(&switch_id)
    {
        let rebound =
            |name: &str| skip_writes.iter().any(|w| crate::generate::write_rebinds(w, name));
        let skip_present: FxHashSet<&str> =
            arm_defs[skip_idx].iter().map(|(n, _, _)| n.as_str()).collect();
        // Locals defined on some *other* arm but not on the skip arm, with sort.
        let mut others: Vec<(String, Sort)> = Vec::new();
        for (i, arm) in arm_defs.iter().enumerate() {
            if i == skip_idx {
                continue;
            }
            for (n, s, _) in arm {
                if !skip_present.contains(n.as_str()) && !others.iter().any(|(on, _)| on == n) {
                    others.push((n.clone(), s.clone()));
                }
            }
        }
        for (name, sort) in others {
            // Sole defining equality `name == rhs` in the switch's entry state.
            let mut vals = incoming_defs.iter().filter_map(|f| match f {
                Formula::Eq(lhs, rhs) => match lhs.as_ref() {
                    Formula::Var(n, _) if *n == name => Some(rhs.as_ref()),
                    _ => None,
                },
                _ => None,
            });
            if let Some(rhs) = vals.next()
                && vals.next().is_none()
                && !rebound(&name)
                && !trust_types::any_free_variable_name(rhs, &mut |v| rebound(v))
            {
                arm_defs[skip_idx].push((name, sort, rhs.clone()));
            }
        }
    }

    let else_defs = &arm_defs[arm_defs.len() - 1];

    let mut arm_guards: Vec<Formula> = Vec::with_capacity(arm_defs.len());
    for (_, values) in &explicit {
        let mut guards = Vec::with_capacity(values.len());
        for value in values {
            let Some(guard) = exact_switch_value_guard(func, discr, *value) else {
                return Vec::new();
            };
            guards.push(guard);
        }
        // `pop` decides the shape; no "len == 1 implies Some" panic step.
        let guard = match guards.pop() {
            None => return Vec::new(),
            Some(only) if guards.is_empty() => only,
            Some(last) => {
                guards.push(last);
                Formula::Or(guards)
            }
        };
        arm_guards.push(guard);
    }

    // Only locals defined in *every* arm (including the else) merge into a total
    // Ite; iterate the first arm's locals and require presence in all the rest.
    let mut out = Vec::new();
    let mut total: FxHashSet<&str> = FxHashSet::default();
    for (name, sort, _) in &arm_defs[0] {
        let Some(else_value) = else_defs.iter().find(|(n, _, _)| n == name).map(|(_, _, v)| v)
        else {
            continue;
        };
        let mut per_arm: Vec<&Formula> = Vec::with_capacity(explicit.len());
        let mut complete = true;
        for arm in arm_defs.iter().take(explicit.len()) {
            match arm.iter().find(|(n, _, _)| n == name) {
                Some((_, _, v)) => per_arm.push(v),
                None => {
                    complete = false;
                    break;
                }
            }
        }
        if !complete {
            continue;
        }
        // Fold innermost-last: Ite(g_0, v_0, Ite(g_1, v_1, … else_value)).
        let mut acc = else_value.clone();
        for idx in (0..explicit.len()).rev() {
            acc = Formula::Ite(
                Box::new(arm_guards[idx].clone()),
                Box::new(per_arm[idx].clone()),
                Box::new(acc),
            );
        }
        total.insert(name.as_str());
        out.push(Formula::Eq(Box::new(Formula::Var(name.clone(), sort.clone())), Box::new(acc)));
    }

    if skip_idx.is_none() && arm_defs.len() <= 2 {
        return out;
    }

    // Trust (2026-10-07, MATCH-ARM-CALL-CHAIN): the PARTIAL merge. A place that
    // several arms define but some arm leaves untouched — the payload `_3@1.0` of
    // `let span = match k { A => Some(1), B => Some(f(x) + 1), C => None }` —
    // has no total `Ite` (the `None` arm gives it no value), so it reached the
    // `if let Some(span)` read as a free variable. Each defining arm still fixes
    // its value on that arm's own paths: emit `guard_i => name == v_i` for every
    // arm `i` that defines it, and nothing for the arms that do not.
    //
    // SOUNDNESS. `guard_i` is the exact route predicate of arm `i` (the else arm's
    // is the negation of every explicit arm's), so on an execution reaching the
    // join through arm `i` it holds and `name == v_i` is that arm's exit value; on
    // every other execution the antecedent is false and nothing is claimed. The
    // value names are read at the same arm exits, under the same write checks, as
    // the total `Ite` above. Restricted to places at least TWO arms define — a
    // value genuinely merged at this join, not a temporary of one arm.
    let else_guard = Formula::Not(Box::new(match arm_guards.len() {
        1 => arm_guards[0].clone(),
        _ => Formula::Or(arm_guards.clone()),
    }));
    arm_guards.push(else_guard);
    if arm_defs.len() > 2 {
        let mut seen_partial: FxHashSet<&str> = FxHashSet::default();
        for arm in &arm_defs[..arm_defs.len() - 1] {
            for (name, sort, _) in arm {
                if total.contains(name.as_str()) || !seen_partial.insert(name.as_str()) {
                    continue;
                }
                let defining: Vec<(usize, &Formula)> = arm_defs
                    .iter()
                    .enumerate()
                    .filter_map(|(i, a)| {
                        a.iter()
                            .find(|(n, s, _)| n == name && s == sort)
                            .map(|(_, _, v)| (i, v))
                    })
                    .collect();
                if defining.len() < 2 {
                    continue;
                }
                for (i, value) in defining {
                    out.push(Formula::Implies(
                        Box::new(arm_guards[i].clone()),
                        Box::new(Formula::Eq(
                            Box::new(Formula::Var(name.clone(), sort.clone())),
                            Box::new(value.clone()),
                        )),
                    ));
                }
            }
        }
    }
    // Trust (2026-10-15, TRUST-KI-1015-1): what the skip edge knew about a guard's copy.
    if let Some(skip_idx) = skip_idx {
        let sources: Vec<BlockId> =
            explicit.iter().map(|(b, _)| *b).chain(std::iter::once(else_source)).collect();
        let joined =
            skip_edge_join_definitions(func, incoming, join, &sources, skip_idx, &arm_guards, &out);
        out.extend(joined);
    }
    out
}

/// Trust (2026-10-15, TRUST-KI-1015-1, aterm-digest `Sha256::finalize`) — the facts an
/// `if` without `else` loses at its join about the GUARD'S OWN READ, kept under the
/// skip edge's route guard.
///
/// MIR reads a guard's subject through a copy, and the arm the guard selects rewrites
/// the subject. `ok_finalize` in `tests/data/finalize_tail.rs` (`self` is `_1`, the
/// length its field `.2`):
///
/// ```text
/// bb5:  _1.2 = move _8.0; _10 = copy _1.2; _12 = CheckedSub(const 64, const 8);
///       assert(!move _12.1) -> bb6
/// bb6 (S):  _11 = move _12.0; _9 = Gt(move _10, move _11);
///           switchInt(move _9) -> [0: bb11, otherwise: bb7]
/// bb7..bb10 (A, the arm; index_mut / fill / compress calls): ..; _1.2 = const 0; goto bb11
/// bb11 (J): _26 = copy _1.2; ..   // the slice's start; bb12 calls index_mut(.., _26.._27)
/// ```
///
/// The copy is made in `bb5`, so `_10 == _1.2` is an ENTRY fact of the switch block `S`,
/// not one of its own definitions: it reaches the skip edge `S -> J` only through `S`'s
/// step of the fixpoint, which drops an entry fact that a store through a pointer or a
/// declined definition in `S` invalidates. It does not hold on `A`'s path, so the join's
/// intersection drops it. The branch merge then says what `_1.2` is at `J`
/// (`!_9 => _1.2 == _8.0`, `_9 => _1.2 == 0`) but nothing ties the path guard
/// `!(_10 > _11)` to it: `_10` is free, and the in-process `ay` refuted the row with
/// `_10 = 0`, `_1.2 = 57`. When the subject is a field's ENTRY value (`if pad.buf_len
/// > 56 { pad.buf_len = 0 }`) the skip edge has no definition of it at all, and the
/// partial merge, which wants two defining arms, gives `J` nothing about it either.
///
/// Emitted, with `g_i` the exact route predicate of arm `i` (`g_skip` the skip edge's):
/// * `g_skip => x == y` for every equality between two bare variables that the
///   fixpoint carries along the skip edge (`path_def_base_outflow` of `S`, from `S`'s
///   pass-1 entry facts) and that `J`'s intersection lost, `x` not merged above;
/// * for such a `y` that no merge above defines: `g_i => y == v` for every fact
///   `y == v` the fixpoint carries out of arm `i`'s own def-source block into `J` that
///   `J`'s intersection lost.
///
/// SOUNDNESS. Every emitted conclusion is a fact the path-definition fixpoint itself
/// carries along that edge into `J`, through the same kills (the transfer is the
/// fixpoint's own step, [`crate::generate::path_def_base_outflow`]); the join drops it
/// only because another edge does not carry it. The kills are load-bearing: the copy is
/// usually an entry fact of `S` (above), and an outflow rebuilt from `S`'s own
/// definitions without them restates a copy that a byte store through a `*mut u8` or a
/// declined `%` in `S` has invalidated (`bad_byte_store_in_switch`,
/// `bad_declined_rem_in_switch` in `tests/finalize_tail_realmir.rs` go PROVED; they
/// panic). `g_skip` and `g_i` are the route
/// predicates the total and partial merges above use (`exact_switch_value_guard` over a
/// discriminant no admitted arm block or hop writes, checked when the partition was
/// admitted): on an execution that reaches `J` over edge `i`, `g_i` holds at `J` and so
/// does the fact; on every other execution the antecedent is false. The facts are bare
/// and conjoined pre-rename like every merge fact, and killed downstream by any write of
/// a name they mention, the discriminant's included (`free_variables` reaches inside the
/// `Implies`). This is a path-sensitive reading of facts the fixpoint already holds: it
/// adds no premise. Only bare `Var == Var` facts from the skip edge (a guard's read), and
/// only the arms' values of the names those read, to bound the volume. Each block's
/// outflow is one more run of the fixpoint's step; a spent verify budget stops before the
/// next one and keeps what was already emitted (each fact holds on its own, so fewer of
/// them can only turn PROVE into FAIL).
fn skip_edge_join_definitions(
    func: &VerifiableFunction,
    incoming: &FxHashMap<BlockId, Vec<Formula>>,
    join: BlockId,
    sources: &[BlockId],
    skip_idx: usize,
    arm_guards: &[Formula],
    merged: &[Formula],
) -> Vec<Formula> {
    let (Some(&skip_source), Some(skip_guard)) = (sources.get(skip_idx), arm_guards.get(skip_idx))
    else {
        return Vec::new();
    };
    let Some(skip_entry) = incoming.get(&skip_source) else {
        return Vec::new();
    };
    let at_join: &[Formula] = incoming.get(&join).map_or(&[], Vec::as_slice);
    let merged_names: FxHashSet<&str> = merged
        .iter()
        .filter_map(|f| match f {
            Formula::Eq(lhs, _) => lhs.var_name(),
            Formula::Implies(_, eq) => match eq.as_ref() {
                Formula::Eq(lhs, _) => lhs.var_name(),
                _ => None,
            },
            _ => None,
        })
        .collect();
    fn bare(f: &Formula) -> Option<&str> {
        match f {
            Formula::Var(name, _) if !name.contains('#') => Some(name.as_str()),
            _ => None,
        }
    }
    let mut out = Vec::new();
    if trust_types::verify_budget::budget_exhausted() {
        return out;
    }
    let mut read: Vec<String> = Vec::new();
    for fact in crate::generate::path_def_base_outflow(func, skip_source, skip_entry) {
        let Formula::Eq(lhs, rhs) = &fact else { continue };
        let (Some(x), Some(y)) = (bare(lhs), bare(rhs)) else { continue };
        if x == y || merged_names.contains(x) || at_join.contains(&fact) {
            continue;
        }
        if !merged_names.contains(y) && !read.iter().any(|r| r == y) {
            read.push(y.to_string());
        }
        out.push(Formula::Implies(Box::new(skip_guard.clone()), Box::new(fact)));
    }
    if read.is_empty() {
        return out;
    }
    for (i, (&source, guard)) in sources.iter().zip(arm_guards).enumerate() {
        if i == skip_idx {
            continue;
        }
        let Some(entry) = incoming.get(&source) else { continue };
        if trust_types::verify_budget::budget_exhausted() {
            return out;
        }
        for fact in crate::generate::path_def_base_outflow(func, source, entry) {
            let Formula::Eq(lhs, _) = &fact else { continue };
            if bare(lhs).is_some_and(|y| read.iter().any(|r| r == y)) && !at_join.contains(&fact) {
                out.push(Formula::Implies(Box::new(guard.clone()), Box::new(fact)));
            }
        }
    }
    out
}

/// The VARIANT ROUTE of a branch-merged enum: at each arm of a discriminant
/// switch that sits on a branch-merge join, the disjunction of the merge arms
/// that may have built that variant.
///
/// ```text
///   S:  switchInt(sel) -> [0: A0, 1: A1, 2: A2, ..]   // the merge partition
///   A0: place = Some(1);            goto J
///   A1: place = Some(f(x) + 1);     goto J              // (through hops)
///   A2: place = None;               goto J
///   J:  d = discriminant(place); switchInt(d) -> [1: K, 0: N, ..]
///   K:  .. (place as Some).0 ..                         // seeded: sel == 0 || sel == 1
/// ```
///
/// The merge partition already carries, as join facts, which value each arm
/// gave the payload (`sel == 0 => place@1.0 == 1`, … — the PARTIAL merge of
/// [`single_switch_branch_merge_definitions`]). What it cannot say is that the
/// `Some` arm `K` is reached only from `A0`/`A1`: nothing in the default lane ties
/// `d` to the constructors of a data-carrying enum. Without that, the
/// `None`-building path `sel == 2` reaches `K` with a free payload.
/// [`enum_construction_demux_definitions`] declines here by design — `Some` is
/// built by TWO predecessors, so neither payload is unique.
///
/// SOUNDNESS. `K` is entered by exactly one edge, under exactly one label `l`
/// (`switch_edges_into == 1`, per-EDGE sole predecessor `J`), so on every
/// execution entering `K`, `discriminant(place) == l` at `J`. `J` writes only `d`,
/// and `place` is never mutably borrowed, so `place` at `J` is what the merge arm
/// left in it. An arm whose LAST write to `place` is a whole-place `Aggregate` of
/// a variant whose decoded tag is not `l` therefore cannot have run; every other
/// arm (a different construction, no write, a partial write, an unknown
/// statement) is KEPT. The disjunction of the kept arms' exact route guards holds
/// at `K`'s entry: the guards read the merge selector, which no merge arm, hop or
/// `J` writes (the partition's write check, plus `d` not rebinding it), and a
/// write in `K` itself kills the seeded fact. A label whose arms are all kept, or
/// none, emits nothing.
///
/// Trust (2026-10-07, MATCH-ARM-CALL-CHAIN): `tla-model-ir` `check_vars_and_pool`
/// — `let span = match e.kind { .. => Some(u64::from(e.len) + 1), .. => None };
/// if let Some(span) = span { u64::from(e.index) + span }`.
pub(crate) fn switch_join_variant_arm_definitions(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    let mut out: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    if !crate::generate::terminator_presence_for(func).has_switch_int {
        return out;
    }
    let blocks = &func.body.blocks;
    let mut preds: Option<std::rc::Rc<Vec<Vec<BlockId>>>> = None;
    let mut edges: Option<std::rc::Rc<Vec<Vec<BlockId>>>> = None;
    for (j_idx, j_block) in blocks.iter().enumerate() {
        // Fewer routed facts is the degradation: PROVE can turn into FAIL, never
        // the reverse. Each join is finished before the next starts.
        if trust_types::verify_budget::budget_exhausted() {
            return out;
        }
        let j = BlockId(j_idx);
        let Terminator::SwitchInt { discr: inner, targets, otherwise, .. } = &j_block.terminator
        else {
            continue;
        };
        let Some(d_local) = operand_bare_local(inner) else {
            continue;
        };
        let [Statement::Assign { place: d_place, rvalue: Rvalue::Discriminant(src), .. }] =
            j_block.stmts.as_slice()
        else {
            continue;
        };
        if d_place.local != d_local
            || !d_place.projections.is_empty()
            || !src.projections.is_empty()
        {
            continue;
        }
        let place_local = src.local;
        let Some(Ty::Adt { variants, .. }) = crate::local_ty_ref(func, place_local) else {
            continue;
        };
        let Some(d_ty) = crate::local_ty_ref(func, d_local) else {
            continue;
        };
        if variants.is_empty() {
            continue;
        }
        let preds = preds
            .get_or_insert_with(|| crate::generate::block_predecessors_rc_for(func))
            .as_slice();
        let Some(partition) = single_switch_join_partition(func, j, preds) else {
            continue;
        };
        if local_is_mutably_borrowed(func, place_local) {
            continue;
        }
        let d_name = crate::place_to_var_name(func, d_place);
        if trust_types::any_free_variable_name(
            &operand_to_formula(func, partition.discr),
            &mut |name| crate::generate::write_rebinds(&d_name, name),
        ) {
            continue;
        }

        // Exact route guard per def-source; the else source's is the negation of
        // every explicit one.
        let mut sources: Vec<(BlockId, Formula)> = Vec::with_capacity(partition.explicit.len() + 1);
        let mut route_ok = true;
        for (source, values) in &partition.explicit {
            let mut guards = Vec::with_capacity(values.len());
            for value in values {
                match exact_switch_value_guard(func, partition.discr, *value) {
                    Some(guard) => guards.push(guard),
                    None => {
                        route_ok = false;
                        break;
                    }
                }
            }
            if !route_ok {
                break;
            }
            let guard = match guards.len() {
                1 => guards.swap_remove(0),
                _ => Formula::Or(guards),
            };
            sources.push((*source, guard));
        }
        if !route_ok || sources.is_empty() {
            continue;
        }
        let else_guard = Formula::Not(Box::new(if sources.len() == 1 {
            sources[0].1.clone()
        } else {
            Formula::Or(sources.iter().map(|(_, g)| g.clone()).collect())
        }));
        sources.push((partition.else_source, else_guard));

        // The variant each source PROVABLY leaves in `place`, or `None`.
        let built_variant = |source: BlockId| -> Option<usize> {
            if source == partition.switch_id {
                return None;
            }
            let block = &blocks[source.0];
            if !block_has_transparent_snapshot_stmt_surface(block) {
                return None;
            }
            let mut last: Option<usize> = None;
            for stmt in &block.stmts {
                match stmt {
                    Statement::Assign { place, rvalue, .. } if place.local == place_local => {
                        last = match rvalue {
                            Rvalue::Aggregate(
                                AggregateKind::Adt { variant, active_field: None, .. },
                                _,
                            ) if place.projections.is_empty() => Some(*variant),
                            _ => None,
                        };
                    }
                    Statement::SetDiscriminant { place, .. } | Statement::Deinit { place }
                        if place.local == place_local =>
                    {
                        last = None;
                    }
                    _ => {}
                }
            }
            last
        };
        let built: Vec<Option<i128>> = sources
            .iter()
            .map(|(s, _)| built_variant(*s).and_then(|v| variants.get(v)).map(|v| v.discriminant))
            .collect();

        for (label, arm) in targets {
            if switch_edges_into(targets, *otherwise, *arm) != 1 {
                continue;
            }
            let edges = edges
                .get_or_insert_with(|| crate::generate::block_predecessor_edges_rc_for(func))
                .as_slice();
            if !sole_predecessor_is(edges, *arm, j) {
                continue;
            }
            let Some(tag) = d_ty.decode_switch_label(*label) else {
                continue;
            };
            let kept_count = built.iter().filter(|b| b.is_none_or(|t| t == tag)).count();
            if kept_count == 0 || kept_count == sources.len() {
                continue;
            }
            let mut kept: Vec<Formula> = Vec::with_capacity(kept_count);
            for ((_, g), b) in sources.iter().zip(&built) {
                if b.is_none_or(|t| t == tag) {
                    kept.push(g.clone());
                }
            }
            let fact = match kept.len() {
                1 => kept.into_iter().next().unwrap_or(Formula::Bool(true)),
                _ => Formula::Or(kept),
            };
            out.entry(*arm).or_default().push(fact);
        }
    }
    out
}

/// Cap on the straight-line hops between a branch switch and its value arm.
/// Hitting it declines the arm (and so the join); it never approximates.
const BRANCH_ARM_MAX_HOPS: usize = 4;

/// The `SwitchInt` a join arm descends from, and the straight-line HOPS between
/// them (top-down: `hops[0]` is the switch's successor, `hops.last()` is `arm`'s
/// unique predecessor), or `None` when the arm does not hang off a switch
/// through admitted hops only.
///
/// A hop is a block with exactly ONE predecessor whose terminator passes control
/// to the next block along an edge that every execution reaching `arm` must
/// take and that observes nothing the switch did not already decide:
///
///  * `Assert { target: next }` — the checked-op success edge. rustc emits it
///    when a branch computes a checked integer value; the failure edge never
///    reaches the join.
///  * `Call { target: Some(next) }` — the normal-return edge. rustc emits it
///    when a branch calls a function (`u64::from(e.len) + 1` is a `Call` hop
///    followed by an `Assert` hop). The unwind edge never reaches the join.
///
/// Either way the hop's other edge must not be `next`, so `next` is entered only
/// by the authenticated edge. Every block on the chain has a single
/// predecessor, so each execution reaching `arm` came from the switch through
/// exactly these blocks, and the switch still partitions the join's incoming
/// paths. The CALLER owns the effect side: it checks every hop's write set
/// against the selector, and refuses `Call` hops unless the selector is a
/// private local no callee can reach.
///
/// Trust (2026-10-07, MATCH-ARM-CALL-CHAIN): before this the recogniser admitted
/// at most ONE `Assert` hop, so a `Call` in an arm (`Kind::Set =>
/// u64::from(e.len) + 1`) declined the whole join and the merged local reached
/// the use as a free variable (`tla-model-ir` `check_vars_and_pool`).
fn branch_arm_switch_chain(
    func: &VerifiableFunction,
    preds: &[Vec<BlockId>],
    arm: BlockId,
) -> Option<(BlockId, Vec<BlockId>)> {
    let blocks = &func.body.blocks;
    let mut hops: Vec<BlockId> = Vec::new();
    let mut next = arm;
    loop {
        let [parent] = preds.get(next.0)?.as_slice() else {
            return None;
        };
        let parent_block = blocks.get(parent.0)?;
        let admitted = match &parent_block.terminator {
            Terminator::SwitchInt { .. } => {
                hops.reverse();
                return Some((*parent, hops));
            }
            Terminator::Assert { target, unwind, .. } => {
                *target == next && unwind.cleanup_target() != Some(next)
            }
            Terminator::Call { target: Some(target), unwind, .. } => {
                *target == next && unwind.cleanup_target() != Some(next)
            }
            _ => false,
        };
        if !admitted || hops.len() >= BRANCH_ARM_MAX_HOPS || hops.contains(parent) {
            return None;
        }
        hops.push(*parent);
        next = *parent;
    }
}

/// An arm's `(name, sort, value)` map, with the checked-arithmetic
/// `Assert`-success semantics inlined when the arm hangs off `switch_id` through
/// exactly one successful `Assert`.
///
///   checked = CheckedAdd(a, b); Assert(!checked.1) -> arm
///   arm: merged = checked.0; Goto(join)
///
/// `checked.0` is not defined on the sibling arm, so the ordinary intersection
/// correctly drops its definition and would leave the merged value free. Inline
/// only the semantic equalities authenticated by that unique Assert-success edge
/// (`checked.0 == a + b`, etc.) into that arm's values. This is not a general
/// predecessor walk: it requires the exact parent/target/switch identity, and
/// `extract_assert_passed_semantics` itself requires the checked-op tuple and
/// overflow-flag projection shape.
fn arm_definition_map_with_checked_assert_impl(
    func: &VerifiableFunction,
    preds: &[Vec<BlockId>],
    arm: BlockId,
    switch_id: BlockId,
) -> Vec<(String, Sort, Formula)> {
    let blocks = &func.body.blocks;
    let mut defs = arm_definition_map(func, arm);
    if defs.is_empty() {
        return defs;
    }
    let [parent] = preds[arm.0].as_slice() else {
        return defs;
    };
    let Terminator::Assert { target, unwind, .. } = &blocks[parent.0].terminator else {
        return defs;
    };
    // The Assert must be the LAST hop of the arm's admitted chain down from
    // `switch_id` (directly under the switch, or below further authenticated
    // hops — `branch_arm_switch_chain`). The success-edge semantics inlined
    // below hold at `arm` either way: `arm`'s only entry is that success edge.
    let parent_is_last_hop = branch_arm_switch_chain(func, preds, arm)
        .is_some_and(|(switch, hops)| switch == switch_id && hops.last() == Some(parent));
    if *target != arm || unwind.cleanup_target() == Some(arm) || !parent_is_last_hop {
        return defs;
    }

    let Some((tuple_local, op, lhs, rhs, value_ty)) =
        exact_asserted_checked_binary_op(func, &blocks[parent.0])
    else {
        return defs;
    };
    if value_ty.int_width().is_none() {
        return defs;
    }
    let result_name = match func
        .body
        .locals
        .get(tuple_local)
        .and_then(|decl| decl.name.as_deref())
    {
        Some(name) => format!("{name}.0"),
        None => format!("_{tuple_local}.0"),
    };
    if !defs.iter().any(|(_, _, value)| {
        trust_types::any_free_variable_name(value, &mut |name| name == result_name)
    }) {
        return defs;
    }
    let lhs_f = Box::new(operand_to_formula(func, lhs));
    let rhs_f = Box::new(operand_to_formula(func, rhs));
    let result_rhs = match op {
        BinOp::Add => Formula::Add(lhs_f, rhs_f),
        BinOp::Sub => Formula::Sub(lhs_f, rhs_f),
        BinOp::Mul => Formula::Mul(lhs_f, rhs_f),
        _ => return defs,
    };

    // Substitution must preserve the value snapshot taken by CheckedBinaryOp.
    // If the success arm writes either the checked field or any operand used
    // by its mathematical RHS, replacing `checked.0` with the arm-exit name
    // would read the *new* value and could manufacture a false proof. Use the
    // canonical alias-aware write set, plus every explicit place destination
    // (including rvalues the definition extractor intentionally declines).
    let Some(arm_writes) = conservative_snapshot_writes(func, &blocks[arm.0]) else {
        return defs;
    };
    if arm_writes.iter().any(|written| crate::generate::write_rebinds(written, &result_name))
        || trust_types::any_free_variable_name(&result_rhs, &mut |name| {
            arm_writes.iter().any(|written| crate::generate::write_rebinds(written, name))
        })
    {
        return defs;
    }

    for (_, _, value) in &mut defs {
        if trust_types::any_free_variable_name(value, &mut |name| name == result_name) {
            *value = crate::quantifier_tiers::substitute(value, &result_name, &result_rhs);
        }
    }
    defs
}

// ─────────────────────────────────────────────────────────────────────────────
// Nested-`SwitchInt` branch merge — the `if / else if / else` partition
// ─────────────────────────────────────────────────────────────────────────────

/// Depth cap on the nested-switch decision tree. Hitting it DECLINES the join
/// (no facts emitted); it never approximates the partition.
const NESTED_MERGE_MAX_DEPTH: usize = 8;

/// One arm of an admitted nested decision tree.
enum MergeArm {
    /// A block whose EXIT state supplies this arm's merged values.
    ///
    /// `source` is that block — a `Goto(join)` arm, or (for a switch's direct
    /// skip edge to the join) the switch block itself. `parent_switch` is the
    /// switch this arm hangs off; the checked-arithmetic `Assert`-success
    /// inlining is authenticated against exactly that switch.
    Leaf { source: BlockId, parent_switch: BlockId },
    /// A further `SwitchInt` that partitions this arm.
    Node(Box<MergeNode>),
}

/// One `SwitchInt` level of an admitted nested decision tree. EVERY table entry
/// and the `otherwise` resolve to an arm — the nested lane never drops a
/// destination, so its arms are a total partition of the switch by construction.
struct MergeNode {
    /// `(route guard, arm)` grouped by destination, in first-seen table order.
    /// The guard is the exact characteristic function of that destination's
    /// routing values, resolved ONCE during the walk (see
    /// [`nested_switch_route_guard`]) so the write-set checks and the emitted
    /// `Ite` can never disagree about which symbols the selector reads.
    explicit: Vec<(Formula, MergeArm)>,
    otherwise: MergeArm,
}

/// `[b, pred(b), pred(pred(b)), …]` while every step has exactly one
/// predecessor. Stops at the first block with zero or several predecessors, at a
/// repeat (so a back edge terminates), and at the depth cap.
fn unique_predecessor_chain(preds: &[Vec<BlockId>], start: BlockId) -> Vec<BlockId> {
    let mut chain = vec![start];
    let mut seen: FxHashSet<BlockId> = FxHashSet::default();
    seen.insert(start);
    let mut cur = start;
    while let [p] = preds[cur.0].as_slice() {
        if !seen.insert(*p) || chain.len() > 2 * NESTED_MERGE_MAX_DEPTH + 2 {
            break;
        }
        chain.push(*p);
        cur = *p;
    }
    chain
}

/// Builder for one join's nested decision tree. Every field is accumulated
/// during the walk and inspected by the driver *after* it, so a partial walk can
/// never leak facts: [`nested_switch_branch_merge_definitions`] returns an empty
/// vec unless the completed tree passes every side condition.
struct NestedMergeBuilder<'a> {
    func: &'a VerifiableFunction,
    preds: &'a [Vec<BlockId>],
    join: BlockId,
    /// Every block admitted into the tree. A repeat means the region is not a
    /// tree (shared arm or back edge) and declines the join.
    visited: FxHashSet<BlockId>,
    /// Union of `conservative_snapshot_writes` across every block admitted
    /// STRICTLY BELOW the root switch, accumulated as each block is validated.
    region_writes: FxHashSet<String>,
    switch_count: usize,
    /// Every `SwitchInt` block admitted as a node, the root included.
    switches: Vec<BlockId>,
    /// `Goto(join)` leaves entered from MORE THAN ONE switch of the tree (see
    /// [`NestedMergeBuilder::build_arm`]).
    shared_leaves: FxHashSet<BlockId>,
}

impl NestedMergeBuilder<'_> {
    fn build_node(
        &mut self,
        switch: BlockId,
        discrs_above: &[String],
        depth: usize,
    ) -> Option<MergeNode> {
        if depth > NESTED_MERGE_MAX_DEPTH {
            return None;
        }
        let func = self.func;
        let blocks = &func.body.blocks;
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &blocks[switch.0].terminator
        else {
            return None;
        };
        let otherwise_target = *otherwise;
        // An `otherwise` that also appears as an explicit target tangles the
        // partition (one block reached by a value *and* the complement).
        if targets.iter().any(|(_, t)| *t == otherwise_target) {
            return None;
        }
        // A duplicate table value is malformed however TrustIR routes it.
        let mut seen_values = FxHashSet::default();
        if targets.iter().any(|(value, _)| !seen_values.insert(*value)) {
            return None;
        }
        // Group by destination, preserving first-seen order (an or-pattern routes
        // several values to one arm), resolving each routing value's exact guard.
        // A value with no exact guard declines the whole join.
        let mut grouped: Vec<(BlockId, Vec<Formula>)> = Vec::new();
        for (value, target) in targets {
            let guard = nested_switch_route_guard(func, &blocks[switch.0], discr, *value)?;
            if let Some((_, guards)) = grouped.iter_mut().find(|(b, _)| b == target) {
                guards.push(guard);
            } else {
                grouped.push((*target, vec![guard]));
            }
        }
        if grouped.is_empty() {
            return None;
        }
        // Blocks BELOW this switch must not clobber its discriminant either. The
        // switch block's own write of it is fine: that write precedes the
        // terminator that reads it, which is why `discrs_above` excludes it here.
        // Both spellings are pinned: the raw discriminant place AND every symbol
        // the resolved guards actually read (they differ once a boolean
        // discriminant's defining comparison is inlined — see
        // `nested_switch_route_guard`).
        let mut discrs_below = discrs_above.to_vec();
        let discr_formula = operand_to_formula(func, discr);
        trust_types::for_each_free_variable_name(&discr_formula, &mut |name| {
            if !discrs_below.iter().any(|existing| existing == name) {
                discrs_below.push(name.to_string());
            }
        });
        for (_, guards) in &grouped {
            for guard in guards {
                trust_types::for_each_free_variable_name(guard, &mut |name| {
                    if !discrs_below.iter().any(|existing| existing == name) {
                        discrs_below.push(name.to_string());
                    }
                });
            }
        }

        self.switch_count += 1;
        self.switches.push(switch);
        let mut explicit = Vec::with_capacity(grouped.len());
        for (target, mut guards) in grouped {
            // One destination, one guard: a single routing value, or the
            // disjunction of an or-pattern's values (they are distinct, so the
            // disjunction is still exactly this destination's characteristic
            // function).
            let guard = match guards.len() {
                0 => return None,
                1 => guards.pop()?,
                _ => Formula::Or(guards),
            };
            explicit.push((guard, self.build_arm(switch, target, &discrs_below, depth)?));
        }
        let otherwise = self.build_arm(switch, otherwise_target, &discrs_below, depth)?;
        Some(MergeNode { explicit, otherwise })
    }

    fn build_arm(
        &mut self,
        parent_switch: BlockId,
        target: BlockId,
        discrs_above: &[String],
        depth: usize,
    ) -> Option<MergeArm> {
        let func = self.func;
        let preds = self.preds;
        let blocks = &func.body.blocks;

        // The switch's own direct edge to the join — the skip edge of an `if`
        // without an `else`. No statement runs between the switch and the join, so
        // the switch block's exit state supplies this arm's values.
        if target == self.join {
            return Some(MergeArm::Leaf { source: parent_switch, parent_switch });
        }
        if target.0 >= blocks.len() {
            return None;
        }
        // Trust (2026-09-29): a SHARED leaf — a `Goto(join)` block entered from
        // several switches of the tree. `matches!(c, b'a'..=b'z')` lowers to two
        // chained comparisons whose FALSE edges both reach one `_b = false` block,
        // so the tree walk below refused it and `if matches!(..) { c - 32 }` was
        // refuted with `c = 0`. The leaf's merged values are its OWN block's
        // definitions (`arm_definition_map` reads no predecessor for a block with
        // several), so every occurrence in the tree denotes the same value, and the
        // driver admits the join only if EVERY predecessor of the leaf is a switch of
        // this tree — then each execution still reaches the join along exactly one
        // route of the tree. The write check against the discriminants read above
        // runs on EVERY route that reaches the leaf.
        let shared_leaf = preds[target.0].len() > 1
            && preds[target.0].contains(&parent_switch)
            && matches!(blocks[target.0].terminator, Terminator::Goto(t) if t == self.join);
        if shared_leaf {
            let writes = conservative_snapshot_writes(func, &blocks[target.0])?;
            if discrs_above
                .iter()
                .any(|d| writes.iter().any(|w| crate::generate::write_rebinds(w, d)))
            {
                return None;
            }
            if self.shared_leaves.insert(target) {
                if self.visited.contains(&target) {
                    return None;
                }
                self.region_writes.extend(writes);
            }
            return Some(MergeArm::Leaf { source: target, parent_switch });
        }
        // Tree, not DAG: this block is entered only from its parent switch, and
        // only once anywhere in the region.
        if !matches!(preds[target.0].as_slice(), [p] if *p == parent_switch)
            || !self.visited.insert(target)
        {
            return None;
        }
        // No discriminant read above this block may be clobbered by it. Unknown
        // statement effects fail closed.
        let writes = conservative_snapshot_writes(func, &blocks[target.0])?;
        if discrs_above.iter().any(|d| writes.iter().any(|w| crate::generate::write_rebinds(w, d)))
        {
            return None;
        }
        self.region_writes.extend(writes);

        match &blocks[target.0].terminator {
            Terminator::Goto(t) if *t == self.join => {
                Some(MergeArm::Leaf { source: target, parent_switch })
            }
            Terminator::SwitchInt { .. } => {
                Some(MergeArm::Node(Box::new(self.build_node(target, discrs_above, depth + 1)?)))
            }
            // The exact `SwitchInt -> checked-op/Assert -> value arm -> Goto(join)`
            // extension the single-switch lane already admits: the Assert's failure
            // edge does not reach the join, so every execution that does reach it
            // through this branch took the authenticated success edge.
            Terminator::Assert { target: success, unwind, .. } => {
                let success = *success;
                if unwind.cleanup_target() == Some(success) || success.0 >= blocks.len() {
                    return None;
                }
                if !matches!(preds[success.0].as_slice(), [p] if *p == target)
                    || !self.visited.insert(success)
                {
                    return None;
                }
                if !matches!(blocks[success.0].terminator, Terminator::Goto(t) if t == self.join) {
                    return None;
                }
                let arm_writes = conservative_snapshot_writes(func, &blocks[success.0])?;
                if discrs_above
                    .iter()
                    .any(|d| arm_writes.iter().any(|w| crate::generate::write_rebinds(w, d)))
                {
                    return None;
                }
                self.region_writes.extend(arm_writes);
                Some(MergeArm::Leaf { source: success, parent_switch })
            }
            _ => None,
        }
    }
}

/// Every leaf of an admitted tree as `(def-source block, its parent switch)`, in
/// tree order.
fn nested_merge_leaves(node: &MergeNode, out: &mut Vec<(BlockId, BlockId)>) {
    fn walk(arm: &MergeArm, out: &mut Vec<(BlockId, BlockId)>) {
        match arm {
            MergeArm::Leaf { source, parent_switch } => out.push((*source, *parent_switch)),
            MergeArm::Node(node) => nested_merge_leaves(node, out),
        }
    }
    for (_, arm) in &node.explicit {
        walk(arm, out);
    }
    walk(&node.otherwise, out);
}

/// The exact route guard for one `SwitchInt` table value, with a BOOLEAN
/// discriminant's same-block defining comparison inlined.
///
/// [`exact_switch_value_guard`] renders a boolean discriminant as the opaque
/// temp itself (`_4` / `Not(_4)`). That is exact, and the refute lane separately
/// pins `_4 == (col < width)`, so the two spellings are interderivable — but only
/// for a consumer that propagates boolean definitions. MEASURED: with the opaque
/// spelling, `trust_certify::certify_violation` refuses two of
/// `proved/cursor_clamp_assert.rs`'s three grounded path residuals AND their
/// disjunction (the catch-all's residual), so the kernel mints no certificate
/// and a `Proved` without a kernel token reports `Unknown`
/// (`convert_result`). With the comparison inlined, all three parts and the
/// disjunction certify. The `Ite`-definition case-split fragment reasons about
/// the selector it is GIVEN, so handing it the arithmetic predicate rather than
/// a boolean alias is what closes the fixture.
///
/// # Exactness
///
/// [`latest_same_block_bool_definition`] is the same resolver
/// [`guard_to_formula`] already uses, and it is *definitional*, not
/// assumption-strengthening: it lowers a comparison (or a single-block
/// `BitAnd`/`BitOr` of comparisons) to its exact truth condition and returns
/// `None` for every other rvalue.
///
/// Its own staleness gates, however, are NOT sufficient here and are not relied
/// on. Both are PLAIN-LOCAL gates: `compared_operand_reassigned_after` collects
/// only projection-free comparison operands and matches only projection-free
/// writes, and `value_local_is_unstable` is consulted only for projection-free
/// operands. A switch block that rewrites a PROJECTED operand between the
/// comparison and its own terminator —
///
/// ```text
///   bb0: _4 = col < t.0;   t.0 = 0;   SwitchInt(_4) -> [0: …] otherwise …
/// ```
///
/// — therefore slips past every one of them, and the inlined `col < t.0` read at
/// the JOIN denotes a `t.0` the switch never compared against. That is a FALSE
/// merge equality, and a false equality manufactures a spurious UNSAT: a false
/// proof of panic-freedom on exactly the safe-looking shapes this lane serves.
/// (An earlier revision of this lane shipped without the check below and was
/// rejected for precisely that reason.)
///
/// Three restrictions are therefore imposed HERE, because this guard is read at
/// the JOIN rather than at the switch:
///
///  * the defining assignment must live in the SWITCH BLOCK itself (checked
///    below), so the resolver can never take its cross-block fallback and the
///    value read by the terminator is exactly the one inlined;
///  * [`switch_block_preserves_inlined_guard`] REFUSES the inlining whenever the
///    switch block writes anything that overlaps a symbol the resolved
///    comparison reads — projected writes and projected reads included, on both
///    sides, via the canonical alias-aware write set and
///    `place_names_overlap`; and
///  * the caller adds every free variable of the returned guard to the
///    `discrs_below` clobber set, so no block STRICTLY BELOW the switch may
///    rewrite a symbol the selector reads either.
///
/// Together those cover every program point between the comparison and the join:
/// writes in the switch block (second bullet, conservatively the whole block),
/// and writes on the way down to the join (third). A write that PRECEDES the
/// comparison needs no treatment — the comparison already reads its result — but
/// is refused anyway, since refusing is always safe.
///
/// Falls back to [`exact_switch_value_guard`] whenever the discriminant is not a
/// same-block-defined boolean local, or whenever the switch block could have
/// disturbed the comparison — never to a weaker predicate. The fallback spelling
/// is the opaque SSA temp itself, which the `discrs_below` clobber set pins
/// directly, so declining costs precision and never soundness.
fn nested_switch_route_guard(
    func: &VerifiableFunction,
    switch_block: &BasicBlock,
    discr: &Operand,
    value: u128,
) -> Option<Formula> {
    let plain_local = match discr {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => {
            Some(place.local)
        }
        _ => None,
    };
    if value <= 1
        && let Some(local) = plain_local
        && matches!(crate::operand_ty_cow(func, discr).as_deref(), Some(Ty::Bool))
        // Defined in the switch block itself: no cross-block fallback, and the
        // resolver's `.rev()` scan finds exactly the def the terminator reads.
        && switch_block.stmts.iter().any(|stmt| {
            matches!(stmt, Statement::Assign { place, .. }
                if place.local == local && place.projections.is_empty())
        })
        && bool_definition_is_switch_block_local(func, switch_block, local, 8)
        && let Some(definition) = latest_same_block_bool_definition(func, switch_block, local)
        && switch_block_preserves_inlined_guard(func, switch_block, &definition)
    {
        return Some(if value == 0 { Formula::Not(Box::new(definition)) } else { definition });
    }
    exact_switch_value_guard(func, discr, value)
}

/// May the comparison resolved out of `switch_block` be read at the JOIN?
///
/// Only if the block itself writes NOTHING the comparison reads. This is the
/// staleness check the plain-local gates inside
/// [`latest_same_block_bool_definition`] cannot make (see its call site above):
/// it is stated over the RESOLVED formula's free variables — so a `BitAnd`
/// leaf's operands are covered as well as the top comparison's — and it uses
/// [`conservative_snapshot_writes`] + `place_names_overlap`, which see PROJECTED
/// places on BOTH sides (`t.0 = 0` is a write that overlaps a read of `t.0`, and
/// a write of the whole `t` overlaps it too).
///
/// Deliberately whole-block rather than "after the defining statement": with the
/// `BitAnd`/`BitOr` recursion the leaf comparisons sit at EARLIER indices than
/// the definition of the switch's own discriminant, so a cut point taken at that
/// definition would miss a write that is after a leaf but before it. A write
/// that precedes every read is harmless, so this is strictly conservative — and
/// conservative here means falling back to the opaque bool temp, never a weaker
/// predicate.
///
/// Fails closed (`false`) when the block has an effect
/// [`conservative_snapshot_writes`] cannot bound.
fn switch_block_preserves_inlined_guard(
    func: &VerifiableFunction,
    switch_block: &BasicBlock,
    definition: &Formula,
) -> bool {
    let Some(writes) = conservative_snapshot_writes(func, switch_block) else {
        return false;
    };
    !trust_types::any_free_variable_name(definition, &mut |read| {
        writes.iter().any(|written| crate::generate::write_rebinds(written, read))
    })
}

/// Was every leaf of this switch discriminant resolved WITHIN the switch block?
///
/// SWITCH-BLOCK WRITE-DISJOINTNESS IS NOT ENOUGH — this lever leaked twice.
/// [`switch_block_preserves_inlined_guard`] checks the switch block's own writes, but
/// [`latest_same_block_bool_definition`] recurses through `BitAnd`/`BitOr` leaves via
/// [`resolve_same_block_bool_operand`], which may take the CROSS-BLOCK unique-defining
/// -block fallback. That fallback's soundness argument is about the BOOL local — a
/// single static definition dominates its uses — and says nothing about the
/// comparison's OPERANDS. Adversarial review measured the resulting false equality:
///
/// ```text
/// bb0: _7.0 = width; _8 = col < _7.0;   Goto bb1
/// bb1: _7.0 = 0;                        Goto bb2
/// bb2: _9 = width > 0; _4 = _8 & _9;    SwitchInt(_4)
/// ```
///
/// `_8` is uniquely defined in bb0 and flows forward, so the leaf resolves — but `_7.0`
/// is rewritten in bb1, so inlining `col < _7.0` at bb2 reads a value the program no
/// longer holds. At `col=0 width=2` the emitted `Ite` evaluates to 1 where the program
/// computes 0: a FALSE merge equality, hence a spurious UNSAT and a false proof of
/// panic-freedom.
///
/// Two attempts to bound this by SCOPE both leaked (writes after the defining statement;
/// then writes anywhere in the switch block), and bounding it by VARIABLES is too blunt —
/// it refuses the defining block's own initializing write, which establishes the value
/// rather than staling it. So bound it at the RESOLVER: every bool leaf must be defined
/// in the switch block itself. Then every read is same-block and
/// [`switch_block_preserves_inlined_guard`]'s whole-block check is exactly sufficient.
///
/// Refusing costs precision only — the caller falls back to `exact_switch_value_guard`'s
/// opaque SSA temp, which `discrs_below` already pins directly.
fn bool_definition_is_switch_block_local(
    func: &VerifiableFunction,
    switch_block: &BasicBlock,
    local: usize,
    fuel: usize,
) -> bool {
    bool_definition_reaching_is_block_local(
        func,
        switch_block,
        switch_block.stmts.len(),
        local,
        fuel,
    )
}

/// [`bool_definition_is_switch_block_local`] for the definition REACHING
/// `block.stmts[end]` — the same lookup [`bool_definition_reaching`] makes, so the
/// two can never disagree about which statement defines a leaf (and, like it, a
/// self-update `c = c | t` looks for the OLD `c` strictly before itself).
fn bool_definition_reaching_is_block_local(
    func: &VerifiableFunction,
    switch_block: &BasicBlock,
    end: usize,
    local: usize,
    fuel: usize,
) -> bool {
    if fuel == 0 {
        return false;
    }
    let Some((def_index, stmt)) =
        switch_block.stmts.get(..end).unwrap_or(&[]).iter().enumerate().rev().find(|(_, stmt)| {
            matches!(stmt, Statement::Assign { place, .. }
                if place.local == local && place.projections.is_empty())
        })
    else {
        // Not defined here at all — the resolver would have gone cross-block.
        return false;
    };
    let Statement::Assign { rvalue, .. } = stmt else { return false };
    match rvalue {
        Rvalue::BinaryOp(BinOp::BitAnd | BinOp::BitOr, lhs, rhs) => {
            [lhs, rhs].into_iter().all(|operand| match operand {
                Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => {
                    bool_definition_reaching_is_block_local(
                        func,
                        switch_block,
                        def_index,
                        place.local,
                        fuel - 1,
                    )
                }
                // A constant or projected leaf is not resolved through the bool
                // resolver, so it cannot carry a cross-block comparison.
                _ => true,
            })
        }
        // Any other rvalue (a comparison, a cast, a use) is read directly out of this
        // block by the resolver, so it is same-block by construction.
        _ => true,
    }
}

/// The nested `Ite` for one merged local, or `None` if some arm does not define
/// it. The guards were resolved during the walk and are reused verbatim, so the
/// selector the caller checked for clobbering is the selector emitted.
fn nested_merge_value(
    func: &VerifiableFunction,
    node: &MergeNode,
    name: &str,
    values: &FxHashMap<BlockId, Vec<(String, Sort, Formula)>>,
) -> Option<Formula> {
    let mut acc = nested_merge_arm_value(func, &node.otherwise, name, values)?;
    for (guard, arm) in node.explicit.iter().rev() {
        let arm_value = nested_merge_arm_value(func, arm, name, values)?;
        acc = Formula::Ite(Box::new(guard.clone()), Box::new(arm_value), Box::new(acc));
    }
    Some(acc)
}

fn nested_merge_arm_value(
    func: &VerifiableFunction,
    arm: &MergeArm,
    name: &str,
    values: &FxHashMap<BlockId, Vec<(String, Sort, Formula)>>,
) -> Option<Formula> {
    match arm {
        MergeArm::Leaf { source, .. } => {
            values.get(source)?.iter().find(|(n, _, _)| n == name).map(|(_, _, v)| v.clone())
        }
        MergeArm::Node(node) => nested_merge_value(func, node, name, values),
    }
}

/// Recover the merged-local invariant at a join whose arms descend from a
/// *chain* of `SwitchInt`s — `if c { a } else if d { b } else { e }`, which
/// lowers to a NESTED partition (arm `a` under the outer switch, `b`/`e` under an
/// inner one). [`single_switch_branch_merge_definitions`] requires all arms to
/// share one switch, so it declines this shape and the merged local stays a free
/// variable that false-refutes a safe assert over it.
///
/// The emitted fact is the nested Ite
/// `x == Ite(g_outer, x_0, Ite(g_inner, x_1, x_2))`, one per local defined at the
/// exit of *every* leaf.
///
/// # Why this is sound in both directions
///
/// The fact is a genuinely-true equality on every execution that reaches `join`,
/// so conjoining it only SHRINKS the model set:
///  * proving (UNSAT) — a true fact cannot turn a real violation into a proof;
///  * refuting (SAT) — every surviving model still corresponds to a reachable
///    execution, so a counterexample stays real.
///
/// That is the same argument the single-switch lane rests on, and it holds only
/// if the equality really is true on every reaching path. The side conditions are
/// RE-DERIVED for the chain, not inherited from the single-switch lane:
///
///  1. **Tree, not DAG.** Every admitted block's predecessor list is exactly
///     `[its parent switch]`, and no block is admitted twice (`visited`). So each
///     leaf is reached by exactly one route and no path enters the region from
///     outside it.
///  2. **Total partition at every level.** Per switch: the `otherwise` must not
///     also be an explicit target, every raw table value must have an exact
///     characteristic guard, duplicate values are rejected, and — unlike the
///     single-switch lane — EVERY destination must resolve to an arm. Because no
///     destination is dropped, the "switch totality" reasoning the single-switch
///     lane needs for its catch-all does not arise: the explicit guards are
///     mutually exclusive and the `otherwise` guard is their exact complement.
///  3. **Every join predecessor is a leaf.** `covered == expected` over the
///     join's predecessor set, with distinct leaf sources. With (1), the tree
///     therefore describes *every* way to reach `join`.
///  4. **No discriminant is clobbered after its switch reads it.** Formulas here
///     are unversioned, so an Ite guard read at the JOIN must denote what the
///     switch actually branched on. Each admitted block is checked against the
///     discriminants of every switch STRICTLY ABOVE it in the chain — the
///     single-switch lane's check covers only the arm block and its unique
///     `Assert` parent, which is NOT enough once there are intermediate switch
///     blocks on the path. The pinned set is BOTH spellings: the raw
///     discriminant place AND every free variable of the RESOLVED guard, which
///     differ once a boolean discriminant's defining comparison is inlined (see
///     [`nested_switch_route_guard`]). A switch computing its own discriminant is
///     fine (that write precedes its own terminator), so a switch block is never
///     checked against itself.
///  5. **No merged value reads a variable the region rewrites.** A leaf's value
///     is an expression over that leaf's own block, but in a chain the blocks
///     between the root switch and the leaf can reassign a variable the value
///     mentions — and then the two spellings of that symbol denote different
///     values and the Ite is a FALSE equality. A false equality is unsound in
///     BOTH directions (it can manufacture a spurious UNSAT, i.e. a false proof
///     of panic-freedom, on exactly the safe shapes this lane is meant to serve).
///     So every free variable of every emitted arm value must be unwritten by
///     every block of the region. The check runs AFTER the checked-arithmetic
///     substitution, so the `Assert`-authenticated `t.0 -> a - b` rewrite is
///     judged on its result rather than on the intermediate tuple. Switch
///     discriminants need no such treatment: (4) already pins them, and they
///     appear only in guards, where reading the switch's own routing value is
///     exactly what selects the arm.
///
/// Any deviation yields an empty vec.
fn nested_switch_branch_merge_definitions(
    func: &VerifiableFunction,
    join: BlockId,
    preds: &[Vec<BlockId>],
) -> Vec<Formula> {
    let blocks = &func.body.blocks;
    if join.0 >= blocks.len() {
        return Vec::new();
    }
    let join_preds = &preds[join.0];
    if join_preds.len() < 2 {
        return Vec::new();
    }

    // The root: the OUTERMOST `SwitchInt` on the unique-predecessor ancestor
    // chain of EVERY join predecessor. `unique_predecessor_chain` runs
    // outermost-last, so scan it in reverse. A candidate SHARED leaf (a
    // `Goto(join)` block with several predecessors) has no such chain; it is
    // left out here and validated after the walk.
    let chains: Vec<Vec<BlockId>> = join_preds
        .iter()
        .filter(|p| {
            !(preds[p.0].len() > 1
                && matches!(blocks[p.0].terminator, Terminator::Goto(t) if t == join))
        })
        .map(|p| unique_predecessor_chain(preds, *p))
        .collect();
    let Some(first_chain) = chains.first() else {
        return Vec::new();
    };
    let Some(root) = first_chain.iter().rev().copied().find(|cand| {
        matches!(blocks[cand.0].terminator, Terminator::SwitchInt { .. })
            && chains.iter().all(|c| c.contains(cand))
    }) else {
        return Vec::new();
    };

    let mut builder = NestedMergeBuilder {
        func,
        preds,
        join,
        visited: FxHashSet::default(),
        region_writes: FxHashSet::default(),
        switch_count: 0,
        switches: Vec::new(),
        shared_leaves: FxHashSet::default(),
    };
    let Some(tree) = builder.build_node(root, &[], 0) else {
        return Vec::new();
    };
    // Strictly disjoint from the single-switch lane, which models exactly one
    // switch: this lane never re-decides a shape that one already models.
    if builder.switch_count < 2 {
        return Vec::new();
    }

    // (3) every join predecessor is a leaf, and the leaves are distinct — except a
    // SHARED leaf, which may recur, and only when every one of its predecessors is
    // a switch of this tree (so no execution reaches it from outside the tree).
    let mut leaves: Vec<(BlockId, BlockId)> = Vec::new();
    nested_merge_leaves(&tree, &mut leaves);
    let expected: FxHashSet<BlockId> = join_preds.iter().copied().collect();
    let covered: FxHashSet<BlockId> = leaves.iter().map(|(source, _)| *source).collect();
    let distinct =
        leaves.iter().filter(|(source, _)| !builder.shared_leaves.contains(source)).count()
            + builder.shared_leaves.len();
    if covered.len() != distinct || covered != expected {
        return Vec::new();
    }
    if builder
        .shared_leaves
        .iter()
        .any(|leaf| !preds[leaf.0].iter().all(|p| builder.switches.contains(p)))
    {
        return Vec::new();
    }
    // Leaves that are not shared still occur exactly once.
    let mut seen_leaves: FxHashSet<BlockId> = FxHashSet::default();
    if leaves
        .iter()
        .any(|(source, _)| !builder.shared_leaves.contains(source) && !seen_leaves.insert(*source))
    {
        return Vec::new();
    }

    // (5) the region's write set, accumulated as each admitted block passed
    // `conservative_snapshot_writes` during `build_arm`.
    let region_writes = &builder.region_writes;

    let mut values: FxHashMap<BlockId, Vec<(String, Sort, Formula)>> = FxHashMap::default();
    for (source, parent_switch) in &leaves {
        values.insert(
            *source,
            arm_definition_map_with_checked_assert_impl(func, preds, *source, *parent_switch),
        );
    }

    let Some((first_source, _)) = leaves.first() else {
        return Vec::new();
    };
    let Some(first_defs) = values.get(first_source) else {
        return Vec::new();
    };

    let mut out = Vec::new();
    'name: for (name, sort, _) in first_defs {
        for (source, _) in &leaves {
            // Defined at the exit of EVERY leaf, or it does not merge.
            let Some(defs) = values.get(source) else {
                continue 'name;
            };
            let Some((_, _, value)) = defs.iter().find(|(n, _, _)| n == name) else {
                continue 'name;
            };
            // (5) every free variable of the arm value survives the region intact.
            if trust_types::any_free_variable_name(value, &mut |v| {
                region_writes.iter().any(|w| crate::generate::write_rebinds(w, v))
            }) {
                continue 'name;
            }
        }
        let Some(ite) = nested_merge_value(func, &tree, name, &values) else {
            continue 'name;
        };
        out.push(Formula::Eq(Box::new(Formula::Var(name.clone(), sort.clone())), Box::new(ite)));
    }
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// Per-path split of a grounded panic-path feasibility formula
// ─────────────────────────────────────────────────────────────────────────────

/// Above this many paths the split is declined and the caller keeps the single
/// combined obligation — the pre-split behaviour, never a weaker one.
const MAX_SPLIT_PATHS: usize = 32;

/// Split a grounded panic-path feasibility formula into ONE FORMULA PER PATH.
///
/// The assert-refutation lane builds the failure block's feasibility formula as
/// `And(defs…, Or(path_0, …, path_n))` — the shared definitional facts, plus the
/// disjunction of every control-flow path that reaches the failure block. This
/// returns `[And(defs…, path_0), …, And(defs…, path_n)]`.
///
/// # This is an EXACT rewriting, not an approximation
///
/// `And(C ∪ {Or(d_0 … d_n)})` and `Or_i And(C ∪ {d_i})` are the same predicate
/// (distributivity of `∧` over `∨`), so for the two verdicts the lane consumes:
///
///  * **UNSAT / proof.** The combined formula is UNSAT **iff** every part is
///    UNSAT. The caller must therefore require ALL parts to be proved before it
///    treats the assert as discharged — proving a subset proves nothing, and
///    `refute_full_assert_obligations` already demands `refuted == 0 &&
///    left_unknown == 0`, i.e. a definite verdict on every emitted VC.
///  * **SAT / refutation.** Any model of `And(C ∪ {d_i})` satisfies
///    `And(C ∪ {Or(d…)})` verbatim — the same assignment, no relaxation. So a
///    part's counterexample is a counterexample of the whole: splitting can
///    never manufacture a SPURIOUS refutation, and it never drops a genuine one
///    (a model of the whole satisfies at least one `d_i`).
///
/// Nothing about grounding changes: the caller splits only a formula it has
/// already accepted as grounded, and every part carries the same `C`.
///
/// # Why the lane needs it
///
/// The parts are not merely easier — for this shape they are the difference
/// between a certificate and none. MEASURED on
/// `proved/cursor_clamp_assert.rs`'s real MIR: the combined 3-path formula
/// makes the in-process ay compute UNSAT and then REJECT its own proof
/// (`strict UNSAT proof validation failed: step t3 uses unverified trust rule`
/// -> `Unknown`), while each of the three parts is `Proved` with an SmtBacked
/// certificate. An uncertified UNSAT is not a proof, so without the split the
/// assert stays undischarged.
///
/// Declines (returning the input unchanged, so the caller behaves exactly as
/// before) when there is no top-level `Or` conjunct to split, when the
/// disjunction is trivial, or when it would produce more than
/// [`MAX_SPLIT_PATHS`] obligations.
pub(crate) fn split_path_feasibility_disjuncts(formula: &Formula) -> Vec<Formula> {
    // A bare `Or` — no definitional conjuncts to redistribute.
    split_on_first_conjoined_or(formula).unwrap_or_else(|| vec![formula.clone()])
}

/// Rebuild `formula` once per disjunct of its first `Or` reachable through
/// `And` nodes only, leaving every other node byte-identical.
///
/// Descending through `And` is what makes the rewriting exact: `And(…, X, …)`
/// with `X = Or(d…)` equals `Or_i And(…, d_i, …)` by distributivity, and that
/// identity composes up an arbitrarily nested `And` spine. It deliberately does
/// NOT descend through `Or`, `Not`, `Ite` or any atom — distributivity does not
/// apply there, so a disjunction under one is left alone.
fn split_on_first_conjoined_or(formula: &Formula) -> Option<Vec<Formula>> {
    match formula {
        Formula::Or(paths) if paths.len() >= 2 && paths.len() <= MAX_SPLIT_PATHS => {
            Some(paths.clone())
        }
        Formula::And(conjuncts) => {
            for (index, conjunct) in conjuncts.iter().enumerate() {
                let Some(parts) = split_on_first_conjoined_or(conjunct) else {
                    continue;
                };
                return Some(
                    parts
                        .into_iter()
                        .map(|part| {
                            let mut rebuilt = conjuncts.clone();
                            rebuilt[index] = part;
                            Formula::And(rebuilt)
                        })
                        .collect(),
                );
            }
            None
        }
        _ => None,
    }
}

/// Exact route guard for one `SwitchInt` table value.
///
/// Do not call [`guard_to_formula`] here: it is an assumption-strengthening API
/// and deliberately returns one-way facts for some boolean predicates. An Ite
/// selector requires an EXACT equality with the arm's constant.
///
/// SIGNED discriminators are now modeled, through the shared typed decode
/// [`crate::switch_label_to_formula`]. They previously had no arm at all, and
/// the caller ([`single_switch_branch_merge_definitions`]) abandons the ENTIRE
/// branch merge when any table value fails to resolve — so every `match` on
/// `Option` / `Result` / `Ordering` / a no-`repr` enum (rustc types those
/// discriminant temps `i8`/`i64`, always SIGNED) silently lost its arm constants
/// and false-FAILed obligations the arm constant was what made safe. Shipping
/// that arm WITHOUT the decode would have been worse than the gap: the merge
/// would then resolve targets at the raw value, so an `Ite` selector would carry
/// `d == 255` where the arm means `d == -1`.
///
/// Exact in both directions: the decode is a bijection on the labels it accepts,
/// and it returns `None` (fail closed — the whole merge is abandoned) for a
/// malformed label, a non-scalar `char`, or a type whose width it cannot
/// establish.
fn exact_switch_value_guard(
    func: &VerifiableFunction,
    discr: &Operand,
    value: u128,
) -> Option<Formula> {
    let ty = crate::operand_ty_cow(func, discr)?;
    let raw = operand_to_formula(func, discr);
    if matches!(ty.as_ref(), Ty::Bool) {
        // A bool switch is a POLARITY, not an equality: `Eq(raw, 0/1)` would mix
        // the Bool and Int sorts. Anything but 0/1 is a malformed bool label.
        return match value {
            0 => Some(Formula::Not(Box::new(raw))),
            1 => Some(raw),
            _ => None,
        };
    }
    Some(Formula::Eq(Box::new(raw), Box::new(crate::switch_label_to_formula(ty.as_ref(), value)?)))
}

/// Predecessor lists for every block, covering both guarded
/// (`SwitchInt`/`Assert`) and unguarded (`Goto`/`Call`/`Drop`/`Opaque`) edges.
pub(crate) fn block_predecessors(func: &VerifiableFunction) -> Vec<Vec<BlockId>> {
    let rc = crate::generate::block_predecessors_rc_for(func);
    std::rc::Rc::try_unwrap(rc).unwrap_or_else(|rc| (*rc).clone())
}

pub(crate) fn block_predecessors_uncached(func: &VerifiableFunction) -> Vec<Vec<BlockId>> {
    let n = func.body.blocks.len();
    let mut preds: Vec<Vec<BlockId>> = vec![Vec::new(); n];
    for block in &func.body.blocks {
        block.terminator.for_each_in_cfg_successor(|t| {
            if t.0 < n && !preds[t.0].contains(&block.id) {
                preds[t.0].push(block.id);
            }
        });
    }
    preds
}

/// Trust (2026-10-06, VARIANT-ARM-DUP-EDGE-1): predecessor lists for every block with ONE
/// ENTRY PER CFG EDGE — the same edges as [`block_predecessors`] (guarded and unguarded,
/// unwind included), NOT deduplicated. A block that one switch reaches under two labels
/// lists that switch twice, so a `[p]` "sole predecessor" match means exactly one
/// incoming EDGE. Every sole-predecessor gate that backs a VARIANT/ARM fact (a fact true
/// only because control came in under one label) reads this relation:
/// [`block_predecessors`] deduplicates, and under it `switchInt(d) -> [0: bbJ, 1: bbJ,
/// otherwise: bbU]` — what rustc -O0 emits for `match a.get(i) { Some(_) => {}, None =>
/// {} }` followed by code — made `bbJ`, which `None` also enters, the `Some` arm.
pub(crate) fn block_predecessor_edges(func: &VerifiableFunction) -> Vec<Vec<BlockId>> {
    let rc = crate::generate::block_predecessor_edges_rc_for(func);
    std::rc::Rc::try_unwrap(rc).unwrap_or_else(|rc| (*rc).clone())
}

pub(crate) fn block_predecessor_edges_uncached(func: &VerifiableFunction) -> Vec<Vec<BlockId>> {
    let n = func.body.blocks.len();
    let mut preds: Vec<Vec<BlockId>> = vec![Vec::new(); n];
    for block in &func.body.blocks {
        block.terminator.for_each_in_cfg_successor(|t| {
            if t.0 < n {
                preds[t.0].push(block.id);
            }
        });
    }
    preds
}

/// Trust (2026-10-06, VARIANT-ARM-DUP-EDGE-1): how many of a `SwitchInt`'s successor
/// edges (every `(value, target)` row and the `otherwise` edge) lead to `arm`. A
/// variant/arm fact may be seeded at `arm` only when this is exactly 1: no other value
/// maps to it and it is not the `otherwise` target.
fn switch_edges_into(targets: &[(u128, BlockId)], otherwise: BlockId, arm: BlockId) -> usize {
    targets.iter().filter(|(_, t)| *t == arm).count() + usize::from(otherwise == arm)
}

/// Per-local `(name, sort, value)` defined by an arm's assignments, each value
/// valid when read at the arm's EXIT.
///
/// Trust (2026-10-08, ARM-VALUE-SELF-READ-1): the merge consumers
/// (`single_switch_branch_merge_definitions`, its PARTIAL merge, and the nested
/// lane) spell every arm value UNVERSIONED and claim it at the join, i.e. they
/// read each free variable at the arm's exit. The extraction already drops a def
/// whose operand a LATER statement of the block rewrites, but not one whose
/// operand its OWN statement rewrites: such an rvalue reads the PRE-statement
/// value. `acc ^= 1` is `acc == acc ^ 1` (a recurrence: UNSAT, which would
/// vacuously discharge every row of the join — caught downstream only by the
/// `SelfReferentialDefinition` net, which then refuses the row), and the tuple
/// swap `t = (t.1, t.0)` is `t.0 == t.1 /\ t.1 == t.0`, which no single-equation
/// net sees: on origin/main 85c8c21eeb `t = (0, y0); if c { t = (t.1, t.0) } else
/// { t = (0, 0) }; assert!(t.1 < 8 && c); buf[t.0]` PROVED its index row while
/// the program panics at `c, y0 = 100` (`tests/arm_value_self_read_merge.rs`).
/// Such a def is dropped here: its subject then has no value on this arm, so the
/// total merge declines it — the monotone direction (fewer hypotheses).
fn arm_definition_map(func: &VerifiableFunction, arm: BlockId) -> Vec<(String, Sort, Formula)> {
    let block = &func.body.blocks[arm.0];
    let mut own_writes: FxHashSet<String> = FxHashSet::default();
    let mut cached_stmt_idx: Option<usize> = None;
    extract_block_definitions_indexed(func, block)
        .into_iter()
        .filter_map(|(stmt_idx, f)| match f {
            Formula::Eq(lhs, rhs) => match *lhs {
                Formula::Var(name, sort) => {
                    let reads_own_write = trust_types::any_free_variable_name(&rhs, &mut |read| {
                        if cached_stmt_idx != Some(stmt_idx) {
                            own_writes.clear();
                            if let Some(stmt) = block.stmts.get(stmt_idx) {
                                crate::generate::stmt_direct_write_names(
                                    func,
                                    stmt,
                                    &mut own_writes,
                                );
                            }
                            cached_stmt_idx = Some(stmt_idx);
                        }
                        own_writes
                            .iter()
                            .any(|written| crate::generate::dest_write_rebinds(written, read))
                    });
                    (!reads_own_write).then_some((name, sort, *rhs))
                }
                _ => None,
            },
            _ => None,
        })
        .collect()
}

/// Route enum-payload facts across a construction join into the
/// matching discriminant-switch arm — a "de-mux" of the join.
///
/// `match` on a freshly-constructed enum lowers to:
/// ```text
///   bbA: place = Aggregate(Adt variant kA, [payloadsA]); Goto J
///   bbB: place = Aggregate(Adt variant kB, [payloadsB]); Goto J
///   J:   d = Discriminant(place); SwitchInt(d) -> [.. -> arm] otherwise ow
///   arm: .. reads place.downcast(k).field(i) ..        // k = the arm's variant
/// ```
/// Each construction block emits payload field facts `place@k.i == payload_i`
/// (`aggregate_field_definitions`), but a fact established on one arm is absent
/// on the others, so the intersection at `J` drops it; the consuming arm then
/// reads an unconstrained payload and a safe `payload + 1` false-FAILs
/// (`flag_result`, `flag_some`). `const_some` proves only because its single
/// straight-line construction has no join to intersect across.
///
/// The discriminant switch DE-MUXes the join: an arm that downcasts `place` to
/// variant `k` is reachable only when `discr(place)` selects variant `k`, i.e.
/// only when `place` was constructed as variant `k`. With EXACTLY ONE predecessor
/// constructing variant `k`, that predecessor ran on every path reaching the arm,
/// so its payload facts hold there. We route each construction's `place@k.*`
/// facts to the arm that downcasts variant `k`, bypassing the lossy join, and
/// return them per-ARM for the seed machinery (seeded into the arm's
/// outflow so a same-arm operand reassignment kills them via
/// `extend_killing_redefs`, and re-attached to the arm's entry so the arm's own
/// VCs see them).
///
/// Soundness — any deviation yields no facts for the join:
///  * `place@k.i` is read ONLY in the variant-`k` arm, reached ONLY when `place`
///    is variant `k`; the routed equality is therefore true wherever it can be
///    read, and an inert dangling variable anywhere it cannot.
///  * `J` must define the switch discriminant as `d = Discriminant(place)` and
///    assign nothing else, so neither `place` nor a payload operand is clobbered
///    between construction and the switch.
///  * every predecessor of `J` must be a `Goto(J)` block whose whole-`place`
///    assignment is an ADT `Aggregate`, with no variant built by two predecessors
///    (a non-unique payload could vacuously discharge a real overflow — see the
///    `demux_two_constructions_same_variant` probe test). The constructor's OWN
///    predecessor count is irrelevant to payload soundness (the payload is the
///    constructor's own aggregate, valid whenever it runs), so a variant whose
///    constructor is reached by several paths still routes — this is what lets
///    `flag_some`, whose None constructor is shared, de-mux at all.
///  * each routed-to arm must have `J` as its sole predecessor (so `place` cannot
///    arrive via another path) and must not itself reassign `place`.
///
/// Guard routing (follow-on): when a variant-`k` constructor `P_k` has a
/// UNIQUE predecessor `Q`, every path reaching the arm traverses the `Q→P_k` edge,
/// so that edge's guard (resolved through `guard_to_formula`, e.g. `v < 100`) is
/// true at the arm. It is routed alongside the payload, gated on `P_k` being
/// single-pred and on the guard's free variables not being reassigned by `P_k` or
/// `J`. The path-guard enumerator cannot supply this: it weakens the guard under a
/// disjunction with the (infeasible) other-variant→arm path.
///
/// Adding a genuinely-true equality or guard is monotone: it can turn a false-FAIL
/// into a PROVE for safe code, never make a real overflow PROVE.
/// True iff `local` is mutably borrowed anywhere in the function — a `Rvalue::Ref{mutable:true}`
/// or a raw `Rvalue::AddressOf(_, ..)` of `local`. NB: `o.as_mut()` (and any call taking `&mut o`)
/// materializes a `&mut o` borrow statement, so this catches the indirect mutation vector too.
/// Used to fail-close enum-payload routing whose construction-time value such a borrow can
/// reassign (`if let Some(r) = o.as_mut() { *r = b; }`).
pub(crate) fn local_is_mutably_borrowed(func: &VerifiableFunction, local: usize) -> bool {
    crate::fn_memo::local_is_mutably_borrowed(func, local, || {
        crate::any_local_write_stmt(func, &func.body.blocks, local, |_b, s| {
            matches!(
                s,
                Statement::Assign {
                    rvalue: Rvalue::Ref { mutable: true, place } | Rvalue::AddressOf(_, place),
                    ..
                } if place.local == local
            )
        })
    })
}

/// LENGTH-stability refinement of [`local_is_mutably_borrowed`]: true iff a mutable
/// borrow of `local` may RESIZE the container it points at. std's OWN `Index`/
/// `IndexMut` impls on its containers never change the length (std contract), so a
/// `&mut` reborrow consumed SOLELY as the receiver of one of those calls
/// ([`crate::generate::is_std_container_index_call`] — std's self type AND std's
/// index argument; a user impl of std's trait on std's `Vec` is not one) is
/// length-benign. This is what lets
/// the dominant WRITE idiom `v[i] = x` (whose `IndexMut::index_mut` call reborrows
/// `&mut (*v)`, tripping the coarse gate and formerly VANISHING the bounds
/// obligation — a silent false-accept) recover the abstract length: the guarded
/// write PROVES, the unguarded write REFUTES.
///
/// SOUNDNESS (fail-closed direction):
/// - a raw `&raw`/`AddressOf` borrow escapes all tracking → may-resize;
/// - a borrow stored through a projection (`s.f = &mut v`) escapes → may-resize;
/// - the borrow temp's uses are counted with the EXHAUSTIVE place walk
///   (`for_each_stmt/terminator_copy_move_place` — every operand AND place-valued
///   position); any mention beyond its definition and recognized benign call
///   receivers (a resize like `Vec::push`, a reborrow chain, an escape as a non-
///   receiver argument) → may-resize. Over-counting is conservative: it can only
///   DECLINE a recovery, never mint a stale length.
///
/// Callers: use this (not the coarse gate) ONLY where the fact at stake is the
/// container's LENGTH. Element-VALUE stability (enum-payload routing, demux) must
/// keep [`local_is_mutably_borrowed`]: `index_mut` hands out `&mut` to an element,
/// so values ARE reassignable through a length-benign borrow.
pub(crate) fn local_mut_borrows_may_resize(func: &VerifiableFunction, local: usize) -> bool {
    crate::fn_memo::local_mut_borrows_may_resize(func, local, || {
        // Trust (VEC-AS-SLICE, 2026-09-25): ask over the base's whole ALIAS CLOSURE, not
        // the base local alone. `base_collection_local_unique` resolves a receiver
        // THROUGH a whole-local move/copy/reborrow (`let w = v; w[i]` traces to `v`), so a
        // resize through that alias (`w.clear()`, which borrows `&mut (*w)`, never
        // `&mut (*v)`) changes the SAME collection the `coll_len(v)` ties and the index
        // recovery speak about — and a per-local scan of `v` never saw it
        // (`let n = v.len(); let w = v; w.clear(); w[n - 1]`). Every local the trace can
        // resolve to this base is in the closure below; a resize of any of them is a
        // resize of the base. Fail-closed by construction: a larger closure can only
        // answer `true` more often.
        let non_sole_mut_param = |alias: usize| {
            crate::local_defs::is_parameter(func, alias)
                && matches!(crate::local_ty_ref(func, alias), Some(Ty::Ref { mutable: true, .. }))
                && !crate::generate::param_is_sole_channel_to_its_pointee(func, alias)
        };
        if non_sole_mut_param(local) {
            return true;
        }
        let closure = base_alias_closure(func, local);
        // Trust (2026-10-15, DECISION_QUEUE D101): the scan below sees the borrows that NAME
        // the base. When the base (or a member of its alias closure) is a REFERENCE
        // PARAMETER, a second argument that aliased its pointee could resize the collection
        // without naming it, and `coll_len(base)` is one unversioned symbol for the whole
        // body: a tie or recovery past such a resize trusts the two arguments disjoint,
        // which D96 admits only disclosed and demoted. Measured on the stage 1 of the
        // 2026-10-14 merge: `for i in 0..v.len() { w.clear(); v[i] = 0 }` over `v, w: &mut
        // Vec<u32>` proved its `v[i]` row (kernel-certified) from `_5 == v` and `i < _5`
        // (`tests/ui/trust/vec_param_length_invariant_loop_refused.rs`). The same predicate
        // as the `Vec` region and the length-invariant tie
        // (`generate::param_is_sole_channel_to_its_pointee`); fail-closed: `true` only
        // declines a tie or a recovery. Asked of an `&mut` parameter only: D96 is the
        // question of two live `&mut` ARGUMENTS. A SHARED reference parameter's pointee is
        // immutable for the call (no `UnsafeCell` in a `Vec`/`String`/slice header), which
        // both lines already relied on for `&Vec` bases before the merge, so two `&Vec`
        // parameters keep their ties (`if i < b.len() { b[i] }` over `a, b: &Vec<u32>`).
        if closure[1..].iter().copied().any(non_sole_mut_param) {
            return true;
        }
        closure.into_iter().any(|alias| local_mut_borrows_may_resize_one(func, alias))
    })
}

/// Every local whose value is a whole-local move/copy/reborrow/address of `base` or
/// of another member (a forward fixpoint over the same hop shapes
/// [`base_collection_step`] follows backwards, minus the slice VIEW a deref call
/// returns: a slice has no operation that changes its `Vec`'s length).
fn base_alias_closure(func: &VerifiableFunction, base: usize) -> Vec<usize> {
    let mut closure = vec![base];
    loop {
        let before = closure.len();
        for b in &func.body.blocks {
            for s in &b.stmts {
                let Statement::Assign { place: dest, rvalue, .. } = s else { continue };
                if !dest.projections.is_empty() {
                    continue;
                }
                let (Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                | Rvalue::CopyForDeref(p)
                | Rvalue::Ref { place: p, .. }
                | Rvalue::AddressOf(_, p)) = rvalue
                else {
                    continue;
                };
                if closure.contains(&p.local) && !closure.contains(&dest.local) {
                    closure.push(dest.local);
                }
            }
        }
        if closure.len() == before {
            return closure;
        }
    }
}

fn local_mut_borrows_may_resize_one(func: &VerifiableFunction, local: usize) -> bool {
    if trust_types::verify_budget::budget_exhausted() {
        return true;
    }
    let mut temps: Vec<usize> = Vec::new();
    if local_is_mutably_borrowed(func, local)
        && crate::find_local_write_stmt(func, &func.body.blocks, local, |_b, s| {
            // BUDGET POLL: `true` (`Some(())`) is the CONSERVATIVE answer this predicate
            // already returns for every escape it cannot rule out (a raw borrow, a
            // projected borrow, an unaccounted mention): it means "the borrow MAY resize",
            // so every caller — `coll_base_len_stable` and
            // `collection_abstract_len_with_base` — DECLINES to tie or recover the
            // container's abstract length.
            if trust_types::verify_budget::budget_exhausted() {
                return Some(());
            }
            let Statement::Assign { place: dest, rvalue, .. } = s else { return None };
            match rvalue {
                Rvalue::Ref { mutable: true, place } if place.local == local => {
                    if !dest.projections.is_empty() {
                        return Some(());
                    }
                    temps.push(dest.local);
                    None
                }
                Rvalue::AddressOf(_, place) if place.local == local => Some(()),
                _ => None,
            }
        })
        .is_some()
    {
        return true;
    }
    for t in temps {
        // Total mentions of the temp anywhere in the body (exhaustive walk), and
        // accounted-for mentions: the defining assign's dest, plus each use as the
        // projection-free RECEIVER (arg 0) of a length-preserving container call.
        let mut mentions = 0usize;
        let mut benign = 1usize;
        for b in &func.body.blocks {
            // BUDGET POLL, per BLOCK: the per-temp loop above cannot interrupt ONE
            // temp's exhaustive place walk, which visits every operand and
            // place-valued position of every statement and terminator in the body.
            // Same conservative `true` as above — abandoning the count must not be
            // read as "no unaccounted mention", which is the answer that would ADMIT
            // a stale length tie.
            if trust_types::verify_budget::budget_exhausted() {
                return true;
            }
            let mut record = |p: &trust_types::Place| {
                if p.local == t {
                    mentions += 1;
                }
            };
            for s in &b.stmts {
                crate::generate::for_each_stmt_copy_move_place(s, &mut record);
            }
            crate::generate::for_each_terminator_copy_move_place(&b.terminator, &mut record);
            // The length-benign receiver set ([`is_length_benign_receiver_call`]):
            // Trust (STD-RECEIVER-ANCHOR-1, 2026-10-04): a `&mut` reborrow is
            // length-benign ONLY when consumed by std's OWN `Index`/`IndexMut` impl
            // on a std container (which never resizes — std contract). The trait
            // path alone (`callee_is_std_ops_method`, round 5) was not that: a
            // downstream `impl IndexMut<dep::K> for Vec<u32>` renders
            // `<alloc::vec::Vec<u32> as core::ops::index::IndexMut<dep::K>>::index_mut`,
            // and its body may truncate the `Vec`; counting it benign kept a stale
            // `.len()` tie (`overflow:sub proved`, check removed). The predicate pins
            // the self type AND the index argument to std's (see its doc). A user free
            // fn `mycrate::index_mut` and the unqualified `core::ops::…::index_mut`
            // (which names no impl) answer false too.
            // Trust (2026-09-25, std-range-family): the `VecDeque` `&mut self`
            // methods that never change the length (std contract), anchored
            // on the authenticated `VecDeque` owner, so `d.swap(i, j)` and
            // `d.range_mut(..)` keep the deque's length tie.
            // Trust (VEC-AS-SLICE, 2026-09-25): a `&mut v` consumed solely as the
            // receiver of std `Vec`'s OWN `DerefMut::deref_mut` / `as_mut_slice` is
            // length-benign too — the `v.sort()` / `v.reverse()` / `v.iter_mut()`
            // idiom. That view is `from_raw_parts_mut(ptr, self.len)`: it writes no
            // field of the `Vec`, and the `&mut [T]` it returns reaches only the
            // ELEMENTS, never the `Vec`'s length (a slice has no resize operation;
            // the borrow checker keeps every other access out while it is live).
            // What happens to the returned slice is therefore irrelevant to the
            // LENGTH — element VALUES are another matter, which is why callers that
            // need value stability keep `local_is_mutably_borrowed`.
            // Trust (SLICE-VIEW-ANCHOR-1, 2026-10-04): `callee_is_std_vec_slice_view` now
            // splits the callee at its top-level ` as ` (a user `Shrink<F>::deref_mut` on
            // std's `Vec` carried the `DerefMut` needle in its fn-item argument and was
            // counted benign here), and the receiver's MIR type must be std's `Vec`.
            if let Terminator::Call { func: callee, args, .. } = &b.terminator
                && is_length_benign_receiver_call(func, callee, args, t)
            {
                benign += 1;
            }
        }
        if mentions > benign {
            return true;
        }
    }
    // Trust (VEC-LEN-PARAM-COPY-1, 2026-10-07): `local` may itself BE a mutable pointer
    // to the container — a `&mut Vec` parameter, or a local the alias closure reached
    // through `_3 = copy _1`. Real MIR hands such a pointer to a callee as `copy _1` /
    // `move _3`, with no `&mut (*_1)` reborrow, so the scan above (which sees only
    // borrows OF `local`) never saw `v.truncate(i)` on a `&mut Vec` parameter and
    // called its length stable. The pointer's own uses are now accounted exactly like
    // a reborrow temp's.
    if local_is_mut_pointer(func, local) && mut_pointer_uses_may_resize(func, local) {
        return true;
    }
    false
}

/// Is `local`'s type a mutable pointer AT TOP LEVEL (`&mut T`, or any raw pointer —
/// a `*const` can be cast to `*mut`, so both count)? Only such a local can carry the
/// container's identity through a whole-local copy into a callee (a `&&mut Vec`
/// cannot resize: a unique path to the `Vec` does not go through a shared one).
fn local_is_mut_pointer(func: &VerifiableFunction, local: usize) -> bool {
    func.body
        .locals
        .get(local)
        .is_some_and(|d| matches!(d.ty, Ty::Ref { mutable: true, .. } | Ty::RawPtr { .. }))
}

/// Is `callee(args)` a call whose arg 0 is the projection-free `t` and which std
/// guarantees leaves the length of the container `t` points at unchanged: std's own
/// container `Index`/`IndexMut`, a listed `VecDeque` `&mut self` method, or std
/// `Vec`'s own slice view (`deref_mut`/`as_mut_slice`) on a std `Vec` receiver?
/// The one length-benign receiver set, shared by a reborrow temp and by a pointer
/// local itself.
fn is_length_benign_receiver_call(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
    t: usize,
) -> bool {
    let Some(Operand::Copy(p) | Operand::Move(p)) = args.first() else { return false };
    if p.local != t || !p.projections.is_empty() {
        return false;
    }
    crate::generate::is_std_container_index_call(callee)
        || crate::generate::collection_range::is_std_vecdeque_method(
            callee,
            &["swap", "range_mut", "iter_mut", "get_mut", "front_mut", "back_mut"],
        )
        || (matches!(crate::generate::method_tail(callee), "deref_mut" | "as_mut_slice")
            && callee_is_std_vec_slice_view(callee)
            && receiver_is_std_vec(func, p))
}

/// Trust (VEC-LEN-PARAM-COPY-1, 2026-10-07): may a use of the mutable POINTER `local`
/// itself resize the container it points at? Counts every mention of `local` with the
/// exhaustive place walk and admits only these, each of which leaves the pointee's
/// length alone or hands the question to an oracle that answers it:
///
/// * a reborrow `&(*local)` / `&mut (*local)` (`Rvalue::Ref` of a place rooted at
///   `local`): a shared one cannot resize; a mutable one is a temp the scan in
///   [`local_mut_borrows_may_resize_one`] already accounts use by use;
/// * a whole-local copy/move into a projection-free local (`_3 = copy _1`), or a
///   `CopyForDeref` into one: the destination is in [`base_alias_closure`], whose
///   every member is asked the same question;
/// * a `Len`/`Discriminant` read, a `Retag`, a `PlaceMention`;
/// * at most ONE whole-local definition of a non-parameter `local` by one of the
///   aliasing rvalues above (its own birth as an alias);
/// * the projection-free arg 0 of a length-benign call
///   ([`is_length_benign_receiver_call`]).
///
/// Every other mention answers "may resize": the pointer passed to any other callee
/// (`Vec::truncate(copy _1)`, `opaque(move _3)`), stored into a field or aggregate,
/// cast (`_1 as *mut _`, a laundering), a write through it (`(*_1) = move _5`), a
/// `Drop` of its pointee, a call writing the pointer itself. Over-counting only
/// declines a tie (PROVE -> FAIL/Unknown), never mints one.
fn mut_pointer_uses_may_resize(func: &VerifiableFunction, local: usize) -> bool {
    let is_param = local >= 1 && local <= func.body.arg_count;
    let mut mentions = 0usize;
    let mut benign = 0usize;
    let mut own_defs = 0usize;
    for b in &func.body.blocks {
        // BUDGET POLL, per BLOCK: same conservative `true` as the scan above.
        if trust_types::verify_budget::budget_exhausted() {
            return true;
        }
        let mut record = |p: &trust_types::Place| {
            if p.local == local {
                mentions += 1;
            }
        };
        for s in &b.stmts {
            crate::generate::for_each_stmt_copy_move_place(s, &mut record);
        }
        crate::generate::for_each_terminator_copy_move_place(&b.terminator, &mut record);
        for s in &b.stmts {
            match s {
                Statement::Assign { place: dest, rvalue, .. } => {
                    let aliasing = match rvalue {
                        Rvalue::Ref { place, .. } => {
                            if place.local == local {
                                benign += 1;
                            }
                            true
                        }
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                        | Rvalue::CopyForDeref(p) => {
                            let whole = matches!(rvalue, Rvalue::CopyForDeref(_))
                                || p.projections.is_empty();
                            if p.local == local && whole && dest.projections.is_empty() {
                                benign += 1;
                            }
                            whole
                        }
                        Rvalue::Len(p) | Rvalue::Discriminant(p) => {
                            if p.local == local {
                                benign += 1;
                            }
                            false
                        }
                        _ => false,
                    };
                    if dest.local == local
                        && dest.projections.is_empty()
                        && aliasing
                        && !is_param
                        && own_defs == 0
                    {
                        own_defs += 1;
                        benign += 1;
                    }
                }
                Statement::Retag { place } | Statement::PlaceMention(place)
                    if place.local == local =>
                {
                    benign += 1;
                }
                _ => {}
            }
        }
        if let Terminator::Call { func: callee, args, .. } = &b.terminator
            && is_length_benign_receiver_call(func, callee, args, local)
        {
            benign += 1;
        }
    }
    mentions > benign
}

/// One step of the base-collection trace: the whole-local `cur` defined from a
/// projection-free `Use`/`&x`/`&raw x`/`CopyForDeref`, or a length-preserving deref
/// call ([`callee_is_length_preserving_deref`]: std's own `Vec`/`String` `Deref` on a
/// std `Vec`/`String` receiver, or `as_slice`). `None` when `cur` is a leaf (the base
/// itself) — including the result of any other `deref`, a user type's among them.
fn base_collection_step(func: &VerifiableFunction, cur: usize) -> Option<usize> {
    crate::find_local_write_candidate(func, &func.body.blocks, cur, |b, item| match item {
        Some(s) => {
            let Statement::Assign { place, rvalue, .. } = s else { return None };
            if place.local != cur || !place.projections.is_empty() {
                return None;
            }
            match rvalue {
                Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                | Rvalue::CopyForDeref(p)
                | Rvalue::Ref { place: p, .. }
                | Rvalue::AddressOf(_, p)
                    if p.projections.is_empty() =>
                {
                    Some(p.local)
                }
                // Trust (2026-07-06, `&mut Vec` length unification): a reborrow of a
                // DEREF — `_dst = &(*_src)` / `&mut (*_src)` / `&raw (*_src)` — where
                // `_src` is a REFERENCE to the container. `*_dst` and `*_src` denote the
                // SAME container, so its length is identical; trace through to `_src`.
                // This makes a `&mut Vec` receiver's `.len()` (auto-reborrowed to
                // `&(*v)` since `Vec::len` takes `&self`) and its `v[i]` resolve to the
                // SAME base local (the param `v`), so both tie to one `coll_len(v)`. SOUND:
                // a resize still reborrows `&mut (*v)`, which `local_is_mutably_borrowed`
                // (checked by the tie/recovery sites on the traced base) detects → they
                // decline → a resized Vec's guarded index stays refutable (no false-PROVE).
                Rvalue::Ref { place: p, .. } | Rvalue::AddressOf(_, p)
                    if p.projections.as_slice() == [trust_types::Projection::Deref] =>
                {
                    Some(p.local)
                }
                _ => None,
            }
        }
        None => {
            // Trust (2026-10-04, DEREF-ANCHOR-1): the deref arm reads the receiver's MIR
            // type, so the receiver is resolved before the callee test.
            if let Terminator::Call { func: callee, args, dest, .. } = &b.terminator
                && dest.local == cur
                && dest.projections.is_empty()
                && let Some(Operand::Copy(p) | Operand::Move(p)) = args.first()
                && p.projections.is_empty()
                && callee_is_length_preserving_deref(callee, func, p)
            {
                Some(p.local)
            } else {
                None
            }
        }
    })
}

/// May a REFERENCE or raw-pointer local on a base trace be reseated through an alias?
/// `value_count` counts an escape (`&mut s`) as no extra value (its documented open
/// residual), so `let mut s: &Vec<u8> = a; let p = &mut s; *p = b;` traced `s` to `a`
/// and `!s.is_empty()` became `len(a) >= 1`: `a[0]` was kernel-certified on an empty
/// `a` (review round 108). A whole-place `&mut`/`&raw` of the pointer local refuses. An
/// OWNED container leaf is not a pointer: a `&mut v` of it (`v[i] = x`, `v.push(..)`) is
/// a resize question, which `local_mut_borrows_may_resize` answers at the tie sites.
fn pointer_local_reseatable(func: &VerifiableFunction, local: usize) -> bool {
    let is_pointer = crate::local_ty_ref(func, local)
        .is_none_or(|ty| matches!(ty, Ty::Ref { .. } | Ty::RawPtr { .. }));
    is_pointer
        && crate::any_local_write_stmt(func, &func.body.blocks, local, |_b, s| {
            matches!(
                s,
                Statement::Assign {
                    rvalue: Rvalue::Ref { mutable: true, place } | Rvalue::AddressOf(_, place),
                    ..
                } if place.local == local && place.projections.is_empty()
            )
        })
}

/// Trace to the base collection local, returning `None` if ANY local on the trace
/// chain (start..base inclusive) has more than one whole-local definition — i.e. is a
/// conditional merge `let v = if c { a } else { b }`. Tying a length to such a local
/// could resolve to the WRONG collection on the other branch — a false-PROVE. Used at
/// BOTH the len-tie mint site and the slice-bound length recovery so they stay in sync
/// (resolve to the same base, or both fail closed).
pub(crate) fn base_collection_local_unique(
    func: &VerifiableFunction,
    start: usize,
) -> Option<usize> {
    crate::fn_memo::base_collection_local(func, start, || {
        let mut cur = start;
        if crate::local_defs::value_count(func, cur).may_exceed(1)
            || pointer_local_reseatable(func, cur)
        {
            return None;
        }
        for _ in 0..(func.body.locals.len() + 4) {
            match base_collection_step(func, cur) {
                Some(n) if n != cur => {
                    if crate::local_defs::value_count(func, n).may_exceed(1)
                        || pointer_local_reseatable(func, n)
                    {
                        return None;
                    }
                    cur = n;
                }
                _ => return Some(cur),
            }
        }
        Some(cur)
    })
}

/// The canonical length var for a base collection local. Trust abstracts a
/// `Vec`/`String` to an integer (its length) under the local's OWN name — the slice
/// index bound `i <= units` and the slice-ref length carriers all reference it — so
/// we tie into THAT existing var (versioned at the use site), not a fresh synthetic
/// one. (A `__coll_len` synthetic would connect `Vec::len`'s result but leave the
/// index bound's length disconnected, the exact gap that left `[slice]` unproved.)
pub(crate) fn coll_len_var(func: &VerifiableFunction, base: usize) -> Formula {
    coll_len_var_place(func, &trust_types::Place::local(base))
}

/// Trust (struct-field Vec length identity, 2026-07-08): PLACE-keyed twin of
/// [`coll_len_var`] — mints the container's abstract length var from the canonical
/// place's `place_to_var_name`. For `Place::local(l)` this is byte-identical to
/// `coll_len_var(func, l)` (same name-minting code path), so the whole-local
/// vocabulary is unchanged; a FIELD place (`(*self).history` → `self*.0`) gives
/// every fresh reborrow temp of the SAME field ONE shared length identity, which is
/// what lets a length guard through one temp discharge an index bound built through
/// another. Field-place names already participate in the overlap-union havoc
/// (`place_names_overlap`), so a Call/Drop that could touch the root versions the
/// field length var exactly like any other place fact — no staleness channel is
/// opened that whole-local names do not already have.
pub(crate) fn coll_len_var_place(func: &VerifiableFunction, base: &trust_types::Place) -> Formula {
    Formula::var_owned(crate::place_to_var_name(func, base), Sort::Int)
}

/// Trust (struct-field Vec length identity, 2026-07-08): PLACE-keyed sibling of
/// [`base_collection_local_unique`]. A whole-local trace result embeds unchanged as
/// `Place::local(leaf)`; additionally, when the traced leaf temp is a gated SHARED
/// reborrow of a struct FIELD (`_t = &((*root).f0.f1…)` with a `&root` SHARED-ref
/// root — see [`shared_stable_field_reborrow_place`] for every gate), the canonical
/// FIELD PLACE is returned instead, so `self.history.is_empty()` (one reborrow
/// temp) and `self.history[..]` (another) resolve to ONE length identity instead of
/// two disconnected per-temp vars (the pre-fix FALSE-REFUTE).
///
/// SOUNDNESS (0 false-PROVE — the key must never name two different collections,
/// and the named collection's length must be stable for the whole body):
///  * FIELDS STAY DISTINCT BY CONSTRUCTION: the key is the full projected place
///    (`(*self).0` vs `(*self).1` mint different `place_to_var_name`s), so a guard
///    on `self.a` can never discharge an index on `self.b`. The rejected "key field
///    shapes by the struct local" design — under which `if !self.a.is_empty() {
///    self.b[0] }` would falsely PROVE — is structurally impossible here.
///  * hop uniqueness: the underlying local trace already fails closed on any hop
///    with more than one whole-local definition (conditional merge / reassignment,
///    call dests included via `local_defs::value_count`).
///  * hop reseat exclusion: NO local on the trace chain may be mutably or raw
///    borrowed ([`local_is_mutably_borrowed`] — covers a `*p = other_ref` reseat
///    through a `&mut`-to-the-temp that leaves the whole-local def count at 1) nor
///    written through a projection ([`local_has_projected_write`] — covers `*t = v`
///    / projected call dests that `local_defs::value_count` does not count).
///  * root immutability & stability: the field-reborrow gates (root is a SHARED
///    reference, root storage is stable, the path is `[Deref, Field+]` only, and no
///    interior-mutability wrapper is crossed) guarantee the field place denotes ONE
///    collection whose length cannot change between guard and index. A `&mut self`
///    root — under which the field could be resized in the span — FAILS CLOSED to
///    the per-temp identity by construction (the shared-ref match declines it).
/// Every ungated shape falls back to `Place::local(leaf)` — byte-identical to the
/// existing whole-local behavior — so this helper is a strict additive extension:
/// existing callers of the LOCAL trace are untouched, and the two sides of the new
/// key (guard fact mint and index-bound recovery) share these gates by calling this
/// ONE function, which is what keeps them symmetric.
pub(crate) fn base_collection_place_unique(
    func: &VerifiableFunction,
    start: usize,
) -> Option<trust_types::Place> {
    crate::fn_memo::base_collection_place(func, start, || {
        let leaf = base_collection_local_unique(func, start)?;
        let Some(field_place) = shared_stable_field_reborrow_place(func, leaf) else {
            return Some(trust_types::Place::local(leaf));
        };
        // Re-walk the deterministic step chain to verify every hop local (mirrors
        // the local-only trace exactly, so it terminates at `leaf`).
        if local_is_mutably_borrowed(func, start) || local_has_projected_write(func, start) {
            return Some(trust_types::Place::local(leaf));
        }
        if start == leaf {
            return Some(field_place);
        }
        let mut cur = start;
        for _ in 0..(func.body.locals.len() + 4) {
            match base_collection_step(func, cur) {
                Some(n) if n != cur => {
                    if local_is_mutably_borrowed(func, n) || local_has_projected_write(func, n) {
                        return Some(trust_types::Place::local(leaf));
                    }
                    cur = n;
                }
                _ => break,
            }
        }
        if cur == leaf {
            return Some(field_place);
        }
        Some(trust_types::Place::local(leaf))
    })
}

/// The gated field-place extraction behind [`base_collection_place_unique`]:
/// `leaf`'s unique whole-local def must be a SHARED (`&`, never `&mut`/`&raw`)
/// reborrow of `(*root).f0.f1…` — a leading `Deref` followed by one or more
/// `Field`s and NOTHING else (an `Index` hop varies at runtime; a `Downcast`
/// re-views enum memory under a switchable tag; either would let one key name two
/// collections) — where the ROOT is:
///  * a SHARED reference (`Ty::Ref { mutable: false }`, the `&self` shape): the
///    borrow checker guarantees the whole pointee — the field `Vec` included — is
///    immutable while the ref is live, so the field's LENGTH is a stable bound for
///    the whole body. This is the same type-level argument
///    [`owned_container_len_var`] documents for whole-local `&Vec` receivers. A
///    `&mut self` root (resizable between guard and index) returns `None` — FAIL
///    CLOSED. (A `&mut` root that is provably never written through could be
///    admitted later; it is deliberately out of scope here.)
///  * a place that holds one value for the whole body
///    ([`crate::place_is_body_stable`], the one statement of that rule, shared with
///    `container_len`'s field-length guard fact): the root's slot is never
///    reseated, projected-into or aliased by a slot-write channel; no pointer that
///    can write under the root is minted (`&mut`, `&raw mut`, `&raw const` of any
///    place rooted at it — for a shared root that is defense in depth, a raw
///    pointer launders past every later check); and no `Field` hop steps into an
///    `UnsafeCell`-family wrapper, because a shared ref does NOT freeze one (only
///    reachable via privacy-bypassing/std-internal MIR, but the exclusion is cheap
///    and closes the hole outright). Until 2026-09-30 this function spelled those
///    three scans by hand; they are the rule's, verbatim, for a shared root.
fn shared_stable_field_reborrow_place(
    func: &VerifiableFunction,
    leaf: usize,
) -> Option<trust_types::Place> {
    if crate::local_defs::is_parameter(func, leaf) {
        return None;
    }
    let Rvalue::Ref { mutable: false, place } = crate::local_defs::unique_value_def(func, leaf)?
    else {
        return None;
    };
    let (first, fields) = place.projections.split_first()?;
    if !matches!(first, trust_types::Projection::Deref)
        || fields.is_empty()
        || !fields.iter().all(|pr| matches!(pr, trust_types::Projection::Field(_)))
    {
        return None;
    }
    let root_ty = crate::local_ty_ref(func, place.local)?;
    if !matches!(root_ty, Ty::Ref { mutable: false, .. }) {
        return None;
    }
    crate::place_is_body_stable(func, place).then(|| place.clone())
}

/// ADT name-tail of an interior-mutability wrapper — a shared `&` does NOT make its
/// contents immutable, so the field-place key's stability argument does not survive
/// crossing one. Matched on the generic-stripped path tail. That is the fail-closed
/// direction here: a user type that merely shares a wrapper's name only makes the
/// field key decline. (`is_owned_slice_container_name`, whose match ADMITS a fact,
/// takes the exact std path instead: OWNED-VEC-NAME-1.)
///
/// Trust: 2026-10-14 (INTERIOR-MUT-CHANNEL-1): the name list is the one
/// `generate::type_name_is_interior_mutable` states (a superset of the ten exact tails
/// this listed: every `*Cell`, the atomics, `Condvar`, `Once`), and a by-name
/// `Ty::Datatype` is judged by it too, as `sep_engine` judged it.
pub(crate) fn ty_is_interior_mut_wrapper(ty: &Ty) -> bool {
    let (Ty::Adt { name, .. } | Ty::Datatype { name, .. }) = ty else { return false };
    crate::generate::type_name_is_interior_mutable(name)
}

/// Any store through a PROJECTION of `local` (`(*l).f = v`, `l.f = v`, a projected
/// call dest, `SetDiscriminant`/`Deinit`) — writes `local_defs::value_count` does NOT
/// count, but which can change what a place rooted at (or reborrowed from) `local`
/// denotes. Used by [`base_collection_place_unique`] to fail closed on
/// reseat-through-deref of a trace-chain temp.
fn local_has_projected_write(func: &VerifiableFunction, local: usize) -> bool {
    crate::any_local_write_candidate(func, &func.body.blocks, local, |b, item| match item {
        Some(s) => {
            matches!(
                s,
                Statement::Assign { place, .. }
                | Statement::SetDiscriminant { place, .. }
                | Statement::Deinit { place }
                    if place.local == local && !place.projections.is_empty()
            )
        }
        None => {
            matches!(
                &b.terminator,
                Terminator::Call { dest, .. }
                    if dest.local == local && !dest.projections.is_empty()
            )
        }
    })
}

/// Trust: `slice.last()/.first()` (and `_mut`) returns `Some` IFF the collection is
/// NON-EMPTY. In the `Some`-discriminant arm of `match coll.last() { Some(..) => .. }`
/// the collection has `len >= 1`, which discharges the ubiquitous `coll.len() - 1`
/// (underflow) the verifier otherwise FALSE-REFUTES (it never connects the Some-arm
/// to the length, and Trust has no unified Vec length model). We mint a canonical
/// `{base}__coll_len`: (a) define EVERY `_len = Y.len()` as `_len == coll_len(base(Y))`
/// (always true), and (b) seed `coll_len(base) >= 1` at the Some-target block (true
/// only there), which the path-def fixpoint propagates forward to the `len()` site.
/// Sound: receivers are traced to the SAME base collection (a `.len()` on a DIFFERENT
/// collection ties to its own var), and a mutably-borrowed (resizable) base is
/// skipped (its length could change between the `last()` and the use).
///
/// EVERY FACT HERE HOLDS ON ONE EDGE, AND IS SEEDED AT A BLOCK (LEN-TIE-JOIN-SEED-1 and
/// LAST-SOME-ARM-SEED-1, 2026-10-12). Each is an ENTRY fact of the block it is keyed by,
/// so it is read on every edge into that block. A call-result tie (`_len ==
/// coll_len`, the view, `to_vec` and `clone` ties) holds on the call's RETURN edge and is
/// minted only when the call's block is the target's sole predecessor: rustc's
/// `SimplifyCfg` returns `let n = if c { v.len() } else { 100 }`'s `len` straight into the
/// join the `else` arm also enters, and `v.len() - n` was proved there (measured on the
/// stage 1 of `46e9afaf95`; it panics for `c == false`, `v.len() < 100`). The
/// `coll_len >= 1` non-emptiness fact holds on the `Some` edge of the switch and is
/// minted only when that edge is the arm's ONLY edge (VARIANT-ARM-DUP-EDGE-1's
/// relation): rustc -O0 spells `match v.last() { Some(_) => {}, None => {} }` as
/// `switchInt(d) -> [0: bbJ, 1: bbJ, ..]`, and `v.len() - 1` after it was
/// kernel-certified with its overflow check ELIDED, returning `usize::MAX` for an empty
/// `v` under the default policy (same stage 1). It also needs the `Option` local to hold
/// the `last()` call's value at the switch: one definition in the whole body, that call,
/// and no `&mut`/raw escape (`let mut o = v.last(); if c { o = Some(&5) }` was proved).
pub(crate) fn slice_last_some_nonempty_definitions(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    let mut out: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    if !crate::generate::terminator_presence_for(func).has_bare_dest_call {
        return out;
    }
    let blocks = &func.body.blocks;
    // One entry per CFG EDGE (unwind included), the relation every sole-edge gate reads.
    let mut preds: Option<std::rc::Rc<Vec<Vec<BlockId>>>> = None;

    let mut last_opt_base: FxHashMap<usize, trust_types::Place> = FxHashMap::default();
    for (block_index, b) in blocks.iter().enumerate() {
        let Terminator::Call { func: callee, args, dest, target, callee_key, .. } = &b.terminator
        else {
            continue;
        };
        if !dest.projections.is_empty() {
            continue;
        }
        let Some(Operand::Copy(p) | Operand::Move(p)) = args.first() else { continue };
        if !p.projections.is_empty() {
            continue;
        }
        let tail = crate::generate::method_tail(callee);
        let is_candidate_tail = matches!(
            tail,
            "last"
                | "first"
                | "last_mut"
                | "first_mut"
                | "len"
                | "deref"
                | "deref_mut"
                | "as_slice"
                | "as_mut_slice"
        );
        let is_to_vec = tail == "to_vec" && callee_is_std_slice_to_vec(callee);
        let is_clone = callee_key.as_ref().is_some_and(|key| {
            key.krate_is_real_sysroot
                && key.sysroot_item == Some(trust_types::SysrootItem::CloneClone)
        });
        if !is_candidate_tail && !is_to_vec && !is_clone {
            continue;
        }
        // Unique-definition trace: a conditionally-merged receiver (`v = if c {a} else
        // {b}`) has an ambiguous base, so tying its length to one branch's collection
        // would be unsound — decline (no coll_len minted). Must match the slice-bound
        // recovery's tracer (`collection_abstract_len_with_base`) so they stay synced.
        // Trust (struct-field Vec length identity, 2026-07-08): the trace is
        // PLACE-keyed — a whole-local receiver keys byte-identically to before
        // (`Place::local(leaf)`), while a gated shared-field reborrow receiver
        // (`_len = self.history.len()` under a `&self` root) ties to the canonical
        // FIELD place's var: the SAME var the guard fact (`owned_container_len_var`)
        // and the index bound (`collection_abstract_len_with_base_opts`) mint —
        // closing the `self.history[self.history.len() - 1]` false-refute (the
        // `_len - 1` underflow and the index bound both need `_len == coll_len`).
        let mut cached_base: Option<Option<trust_types::Place>> = None;
        let mut get_base = || -> Option<trust_types::Place> {
            cached_base.get_or_insert_with(|| base_collection_place_unique(func, p.local)).clone()
        };
        // The call's own return edge is the only way into `target` (LEN-TIE-JOIN-SEED-1).
        let mut returns_solely_into = |tgt: &BlockId| {
            let preds = preds
                .get_or_insert_with(|| crate::generate::block_predecessor_edges_rc_for(func))
                .as_slice();
            sole_predecessor_is(preds, *tgt, b.id)
        };
        match tail {
            // CRATE-ANCHOR (round-5 false-proof close): `first`/`last`(`_mut`) are
            // INHERENT `[T]` methods (a `Vec`/array receiver derefs to the slice, so the
            // genuine callee is `core::slice::<impl [T]>::first` etc.). A user free fn
            // `fn first(v:&Vec<i32>)->Option<i32>{Some(0)}` renders `mycrate::first` and is
            // DECLINED — else its `Some` in the match arm seeds `coll_len >= 1` and
            // discharges `v[0]` on an actually-empty collection (OOB).
            // LAST-SOME-ARM-SEED-1: the `Option` local must hold THIS call's value at
            // every read — its one definition in the body, never escaped — or a later
            // `o = Some(..)` makes the `Some` arm say nothing about the collection.
            "last" | "first" | "last_mut" | "first_mut"
                if callee_is_std_slice_inherent(
                    callee,
                    &["::last", "::first", "::last_mut", "::first_mut"],
                ) && !crate::local_defs::is_parameter(func, dest.local)
                    && crate::local_defs::is_single_static_assignment(func, dest.local)
                    && crate::local_defs::body_unique_defining_block(&func.body, dest.local)
                        == Some(block_index)
                    && crate::place_source_is_stable(func, dest.local) =>
            {
                // Trust (2026-10-10, review round 101): the seed below reads ANY switch on
                // `discriminant(dest)`, so `dest` must hold this call's result and
                // nothing else: `let o = if c { v.last() } else { Some(r) }` seeded
                // `len(v) >= 1` for `Some(r)` (`v.len() - 1` kernel-certified on an empty
                // `v`), and two calls into one dest kept the last base inserted.
                if let Some(base) = get_base() {
                    last_opt_base.insert(dest.local, base);
                }
            }
            // `_len = Y.len()` is a Call whose result is live in the RETURN target;
            // tie it there (NOT in this block, where `_len` is not yet defined and the
            // var would version-mismatch the eventual `_len - 1` use site). SOUND only
            // when the base's LENGTH is stable — otherwise two `.len()` calls
            // straddling a resize (`a=v.len(); v.push(x); b=v.len()`) would both tie to
            // one `coll_len` and falsely force `a == b`. Length-benign `&mut` reborrows
            // (`index_mut` receivers — the `v[i] = x` write idiom) never resize, so
            // they keep the tie; MUST stay synced with the recovery gate
            // (`collection_abstract_len_with_base_opts`), else a guarded write would
            // emit its bounds VC without the `_len == coll_len` fact and false-refute.
            // CRATE-ANCHOR (round-5 false-proof close): only a GENUINE std container
            // `len` mints the `_len == coll_len(base)` tie. A user free fn
            // `fn len(v:&Vec<i32>)->usize{1_000_000}` renders `mycrate::len` and is
            // DECLINED by the shared `total_summary_len_call` matcher — else the tie ties
            // the container's abstract length var to a forged huge value → discharges
            // `v[k]` for a large `k` (OOB). `total_summary_len_call` is the shared
            // canonical-call matcher; it rejects the same-prefixed impostors
            // (`std::vec::VecEvil::len`, `core::slice::Iter::len`) too.
            "len"
                if (trust_types::total_call_summaries::total_summary_len_call(callee)
                    // Trust (2026-10-06, LEN-KEY-1): or std's inherent `len` by its
                    // DefId key, which the `::<__trust_args@…>` tag of a
                    // duplicate-crate-name graph (an ordinary Cargo graph) does not
                    // hide from it the way it hides the `::len` leaf from the string.
                    || crate::generate::callee_key_is_std_inherent_len(callee_key.as_ref())
                    // Trust (2026-09-25, std-range-family): the genuine
                    // `VecDeque::len` ties to the deque's `coll_len(base)`, the var
                    // its index/range/swap bounds read. Kept OUT of the shared
                    // `total_summary_len_call` (whose other consumers lower the
                    // call) — this tie is the only thing the deque lane needs.
                    || crate::generate::collection_range::is_std_vecdeque_method(
                        callee,
                        &["len"],
                    )) =>
            {
                let Some(base) = get_base() else { continue };
                if !coll_base_len_stable(func, &base) {
                    continue;
                }
                let Some(tgt) = target.as_ref().filter(|t| returns_solely_into(t)) else {
                    continue;
                };
                // Trust (2026-10-10, review round 100; kept beside upstream's
                // LEN-TIE-JOIN-SEED-1 sole-edge filter above, which also covers it): the
                // tie is a definition of the TARGET block, so it must hold on EVERY entry
                // to it. A multiply-written
                // dest whose return target is a JOIN (`let k = if c { v.len() } else
                // { n }`: the call returns into the block the `k = n` arm also enters)
                // got `k#join == coll_len(v)` on the `k = n` path too, and `if k > 0 {
                // v[k - 1] }` PROVED kernel-certified while `f(&vec![1, 2, 3], 10,
                // false)` panics. A single-valued dest is the call's value wherever it
                // is read; otherwise the call block must be the target's only entry.
                if (tgt.0 == 0 || !block_has_sole_predecessor(func, *tgt, b.id))
                    && !crate::local_defs::is_single_static_assignment(func, dest.local)
                {
                    continue;
                }
                let dest_var = Formula::var_owned(
                    crate::place_to_var_name(func, &trust_types::Place::local(dest.local)),
                    Sort::Int,
                );
                out.entry(*tgt).or_default().push(Formula::Eq(
                    Box::new(dest_var),
                    Box::new(coll_len_var_place(func, &base)),
                ));
            }
            // Trust (VEC-AS-SLICE, 2026-09-25): `_s = <Vec<T> as Deref>::deref(&v)`
            // (and `deref_mut` / `as_slice` / `as_mut_slice`) IS the `Vec`'s element
            // slice, `from_raw_parts(ptr, v.len)`, so its length EQUALS the `Vec`'s:
            // tie `_s__slice_len == coll_len(base)` where `_s` is live (the return
            // target), under exactly the `.len()` arm's gates — a uniquely-traced
            // base whose LENGTH is stable for the whole body — plus a std-`Vec` base
            // and std-`Vec`'s own view impl (never another `Deref` type's, whose view
            // may be any length). Without it `for (i, x) in v.iter().enumerate()`
            // bounds `i` by a slice length nothing relates to `v.len()` (d5/p11:
            // `v.len() == 3` beside an iterated `__slice_len == 4`).
            // Trust (SLICE-VIEW-ANCHOR-1, 2026-10-04): the receiver `p` itself must be a
            // std `Vec` by MIR type too, not only its traced base.
            "deref" | "deref_mut" | "as_slice" | "as_mut_slice"
                if callee_is_std_vec_slice_view(callee) && receiver_is_std_vec(func, p) =>
            {
                let Some(base) = get_base() else { continue };
                if !place_is_std_vec(func, &base) || !coll_base_len_stable(func, &base) {
                    continue;
                }
                let Some(tgt) = target.as_ref().filter(|t| returns_solely_into(t)) else {
                    continue;
                };
                let Some(view_len) = crate::slice_len_formula(
                    func,
                    &Operand::Copy(trust_types::Place::local(dest.local)),
                ) else {
                    continue;
                };
                out.entry(*tgt).or_default().push(Formula::Eq(
                    Box::new(view_len),
                    Box::new(coll_len_var_place(func, &base)),
                ));
            }
            // Trust (2026-10-15, STRING-AS-STR): the `String` twin of the view tie above.
            // `_s = <String as Deref>::deref(&s)` (and `deref_mut`) IS
            // `str::from_utf8_unchecked(&self.vec)`: its byte length EQUALS the
            // `String`'s, the value every `s.len()` ties to `coll_len(base)` in the `len`
            // arm. The str-length rewrite (`rewrite_str_len_calls`) turns a later
            // `t.len()` on that `&str` into `PtrMetadata(_s)`, so without this equation
            // the guard `s.len() == 0` said nothing about `_s`'s length and the correct
            // `if s.len() == 0 { return 0 } let t: &str = s; t.len() - 1` was refuted
            // (measured on the stage 1 of the 2026-10-14 merge,
            // `tests/ui/trust/deref_len_tie_requires_std_self.rs`, `std_string_view`).
            // Same gates as the `Vec` view: std's OWN `String` `Deref`/`DerefMut` by the
            // exact top-level split (`std_container_deref_self`), a receiver that is std's
            // `String` by MIR type (DEREF-ANCHOR-1's receiver test), a base that is std's
            // `String`, a length stable for the whole body, and the call's sole return edge.
            "deref" | "deref_mut"
                if std_container_deref_self(callee) == Some(StdDerefSelf::String)
                    && deref_receiver_is_std_container(func, p, StdDerefSelf::String) =>
            {
                let Some(base) = get_base() else { continue };
                if !place_is_std_string(func, &base) || !coll_base_len_stable(func, &base) {
                    continue;
                }
                let Some(tgt) = target.as_ref().filter(|t| returns_solely_into(t)) else {
                    continue;
                };
                let Some(view_len) = crate::slice_len_formula(
                    func,
                    &Operand::Copy(trust_types::Place::local(dest.local)),
                ) else {
                    continue;
                };
                out.entry(*tgt).or_default().push(Formula::Eq(
                    Box::new(view_len),
                    Box::new(coll_len_var_place(func, &base)),
                ));
            }
            _ => {}
        }
        // Trust (VEC-AS-SLICE, 2026-09-25): `v = xs.to_vec()` — a fresh `Vec` with
        // EXACTLY the source slice's length (`<[T]>::to_vec` clones each element into
        // a `Vec::with_capacity(len)`; a panicking `Clone` unwinds, it never returns
        // short). Tie `coll_len(v) == len(xs)` at the return target when `v` is its
        // own unique base (one definition, this call) with a stable length. Keyed on
        // the DESTINATION's base, so it is independent of the receiver trace above.
        if is_to_vec
            && let Some(tgt) = target
            && get_base().is_some()
            && returns_solely_into(tgt)
            && base_collection_local_unique(func, dest.local) == Some(dest.local)
            && crate::local_defs::has_one_explicit_def(func, dest.local)
        {
            let dest_place = trust_types::Place::local(dest.local);
            if place_is_std_vec(func, &dest_place)
                && coll_base_len_stable(func, &dest_place)
                && let Some(src_len) = crate::slice_len_formula(func, &Operand::Copy(p.clone()))
            {
                out.entry(*tgt)
                    .or_default()
                    .push(Formula::Eq(Box::new(coll_len_var(func, dest.local)), Box::new(src_len)));
            }
        }
        // Trust (VEC_CLONE_LEN, 2026-10-05): `w = <Vec<T, A> as Clone>::clone(&v)` — a
        // fresh `Vec` with EXACTLY `v`'s length (alloc's impl is `<[T]>::to_vec_in`; a
        // panicking element `Clone` unwinds, it never returns short). The callee is the
        // real `Clone::clone` by DefId (the extractor renders it as the shared
        // `__trust_total_clone` sentinel, so the string cannot tell it from a comparison);
        // `clone` returns `Self`, so a std-`Vec` destination fixes the impl to alloc's
        // (coherence). Tie `coll_len(w) == coll_len(base(v))` under the `to_vec` arm's
        // destination gates, plus a std-`Vec` receiver whose traced base has a stable
        // length for the whole body (the same var every `v.len()` ties to).
        if is_clone
            && args.len() == 1
            && let Some(tgt) = target
            && receiver_is_std_vec(func, p)
            && let Some(base) = get_base()
            && returns_solely_into(tgt)
            && base_collection_local_unique(func, dest.local) == Some(dest.local)
            && crate::local_defs::has_one_explicit_def(func, dest.local)
        {
            let dest_place = trust_types::Place::local(dest.local);
            if place_is_std_vec(func, &dest_place)
                && coll_base_len_stable(func, &dest_place)
                && place_is_std_vec(func, &base)
                && coll_base_len_stable(func, &base)
            {
                out.entry(*tgt).or_default().push(Formula::Eq(
                    Box::new(coll_len_var(func, dest.local)),
                    Box::new(coll_len_var_place(func, &base)),
                ));
            }
        }
    }
    // UNGATE: keep the accumulated `_len == coll_len(base)` ties even when there is no
    // last()/first() — they connect a `k <= v.len()` guard to the slice-bound recovery
    // so guarded owned-Vec indexing PROVES. The non-emptiness `Ge(coll_len,1)` loop
    // below is a structural no-op when `last_opt_base` is empty, so this leaks no
    // non-emptiness fact. (The ties are true facts — `v.len()` IS the abstract length
    // for a uniquely-traced, non-mut-borrowed base — so they cannot cause a false-PROVE,
    // once each is seeded only where the call's return edge is the target's one entry:
    // LEN-TIE-JOIN-SEED-1, 2026-10-12.)
    if last_opt_base.is_empty() {
        return out;
    }

    for b in blocks {
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &b.terminator else {
            continue;
        };
        let Some(d_local) = operand_bare_local(discr) else { continue };
        let mut opt_local = None;
        for s in &b.stmts {
            if let Statement::Assign { place: p, rvalue: Rvalue::Discriminant(src), .. } = s
                && p.local == d_local
                && p.projections.is_empty()
                && src.projections.is_empty()
            {
                opt_local = Some(src.local);
            }
        }
        let Some(opt_local) = opt_local else { continue };
        let Some(base) = last_opt_base.get(&opt_local) else { continue };
        // Length-stability gate (same refinement as the len-tie arm above): a
        // non-emptiness fact `coll_len >= 1` survives length-benign `index`/
        // `index_mut` reborrows; a genuine resize still declines it.
        if !coll_base_len_stable(func, base) {
            continue;
        }
        let Some(some_bb) = targets.iter().find(|(v, _)| *v == 1).map(|(_, t)| *t) else {
            continue;
        };
        // The `Some` block must be entered only through this switch's `Some` edge (and
        // is not the entry block, whose implicit entry is no edge).
        // LAST-SOME-ARM-SEED-1 (upstream, same defect): no other label of this switch,
        // not its `otherwise`, and no other block's edge (edge-counted, unwind included).
        let preds = preds
            .get_or_insert_with(|| crate::generate::block_predecessor_edges_rc_for(func))
            .as_slice();
        if some_bb.0 == 0
            || !sole_predecessor_is(preds, some_bb, b.id)
            || !switch_edge_is_sole(targets, *otherwise, some_bb)
            || switch_edges_into(targets, *otherwise, some_bb) != 1
            || !block_has_sole_predecessor(func, some_bb, b.id)
        {
            continue;
        }
        let facts = out.entry(some_bb).or_default();
        facts
            .push(Formula::Ge(Box::new(coll_len_var_place(func, base)), Box::new(Formula::Int(1))));
        // Trust (2026-10-11, sweep2 p13/a12): for a slice or `str` reference base
        // (`fn f(v: &[i32]) { match v.first() { Some(_) => v[0], .. } }`) the bounds and
        // range rows read the reference's LENGTH METADATA, `{v}__slice_len`
        // (`slice_len_formula`), not the abstract `coll_len` var named after the place,
        // so the seed above never reached them (counterexample `v = 1, v__slice_len =
        // 0`). The same `Some` proves that length non-zero; `slice_len_formula` names
        // it exactly as the bounds rows do. A Vec base has no such name (it declines),
        // and an array base answers its constant length, which needs no fact.
        if base.projections.is_empty()
            && matches!(
                crate::local_ty_ref(func, base.local),
                Some(Ty::Ref { inner, .. }) if matches!(inner.as_ref(), Ty::Slice { .. } | Ty::Str)
            )
            && let Some(len) = crate::slice_len_formula(func, &Operand::Copy(base.clone()))
            && !matches!(len, Formula::Int(_))
        {
            facts.push(Formula::Ge(Box::new(len), Box::new(Formula::Int(1))));
        }
    }
    out
}

/// Length-stability gate for a traced base KEY. A WHOLE-LOCAL key keeps the exact
/// [`local_mut_borrows_may_resize`] refinement it had before the place-keying (a
/// length-benign `index`/`index_mut` reborrow keeps the tie; a genuine resize
/// declines) — byte-identical behavior. A FIELD-PLACE key was already proven
/// length-stable BY CONSTRUCTION when it was minted: [`base_collection_place_unique`]
/// only returns a projected place under a SHARED, stable root, and while a `&self`
/// is live no `&mut` to the field (hence no resize) can coexist — so it passes
/// unconditionally. Keeping the gate derived from the KEY (not re-derived ad hoc at
/// each site) keeps the mint sites and the recovery sites in sync — the same
/// stay-synced requirement the local gate documents.
fn coll_base_len_stable(func: &VerifiableFunction, base: &trust_types::Place) -> bool {
    if base.projections.is_empty() { !local_mut_borrows_may_resize(func, base.local) } else { true }
}

/// Trust (R2 corpus family 2 — get-Some index bound): `slice.get(idx) == Some(..)`
/// implies `idx < slice.len()` — the `<[T]>::get` CONTRACT. In the `Some`-arm of
/// `while let Some(x) = flags.get(idx) { idx += 1; … }` (bitflags `IterNames::next`,
/// semver `numeric_identifier`) the increment `idx + 1` cannot overflow: the seeded
/// `idx < {recv}__slice_len` plus the allocation-size axiom
/// (`conjoin_slice_len_bounds`: `len <= isize::MAX` for non-ZST elements) bound it
/// away from `usize::MAX`. Without this fact the verifier FALSE-REFUTES the most
/// common get-guarded scan loops in battle-tested crates.
///
/// SOUNDNESS (each gate prevents a concrete false proof):
///  * callee anchored to `core::slice::`/`std::slice::` + tail `get` — a user
///    `MyColl::get` with different semantics never matches;
///  * the receiver arg must be a SHARED `&[T]`/`&[T; N]` (`Ref { mutable: false }`)
///    and the index a by-value unsigned integer — so the CALLEE provably cannot
///    mutate the index source or the collection (the call-arg `&mut`-staleness
///    channel, hunt-5/7/w0z class);
///  * the fact is seeded ONLY at the `Some`-discriminant target of a switch in the
///    call's DIRECT target block, which must contain no assignment other than the
///    discriminant read of the call dest — no path from the call to the seed block
///    can rewrite the index;
///  * downstream staleness (`idx += 1`, `self.flags = shorter`) is handled by the
///    consumers: `v2_live_path_defs` drops the fact in any block that redefines one
///    of its variables, and the path-def fixpoint kills it across redefining paths
///    (the S2c version rename makes a surviving stale copy name-disjoint);
///  * a traced copy source (`_t = Copy((*self).idx)` feeding `get(.., _t)`) is only
///    credited when that copy is IN the call block with no later same-block write
///    overlapping the source base — the fact then names the value the call actually
///    read (in reality unchanged across the call: the callee has no mutable access,
///    see the shared-receiver gate).
///
/// The facts are TRUE point-invariants of the Some arm; a dropped/killed fact only
/// costs precision (a false-FAIL at worst), never soundness.
pub(crate) fn slice_get_some_index_bound_definitions(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    let mut out: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    if !crate::generate::terminator_presence_for(func).has_bare_dest_call {
        return out;
    }
    let blocks = &func.body.blocks;
    // VARIANT-ARM-DUP-EDGE-1: per-EDGE predecessors (see `block_predecessor_edges_uncached`).
    let mut preds: Option<std::rc::Rc<Vec<Vec<BlockId>>>> = None;

    for b in blocks {
        // `_opt = <[T]>::get(recv, idx)` terminating this block.
        let Terminator::Call { func: callee, args, dest, target: Some(target), .. } = &b.terminator
        else {
            continue;
        };
        if !dest.projections.is_empty() || args.len() != 2 || target.0 == 0 {
            continue;
        }
        if crate::generate::method_tail(callee) != "get"
            || !(callee.starts_with("core::slice::") || callee.starts_with("std::slice::"))
        {
            continue;
        }
        // Receiver: a SHARED reference to a slice / fixed array. This is both the
        // length-model gate and the no-mutable-access gate (see the doc comment).
        let recv = &args[0];
        let recv_shared_slice = matches!(
            crate::operand_ty_cow(func, recv).as_deref(),
            Some(Ty::Ref { mutable: false, inner })
                if matches!(inner.as_ref(), Ty::Slice { .. } | Ty::Array { .. } | Ty::SymArray { .. })
        );
        if !recv_shared_slice {
            continue;
        }
        // Index: a by-value UNSIGNED integer (`usize`). A range-typed `get(a..b)` or
        // any non-integer index is skipped — its "value" has no Int-sorted meaning.
        let idx = &args[1];

        // The call's DIRECT target must read the discriminant of `dest` and switch on
        // it, with no other assignment in between (mirror the demux `j_clean` gate);
        // `Option::Some` is variant 1. Or — the `?` spelling, `get(..)?` — the direct
        // target is an EMPTY block whose call is core's authenticated `Try::branch`
        // on `move dest`, and ITS direct target switches cleanly on the branch result:
        // `<Option<T> as Try>::branch(Some(x))` is `Continue(x)` and `branch(None)` is
        // `Break(None)`, so the `Continue` arm is reached only from `Some`. The
        // `Continue` tag is read off the destination's own `ControlFlow` variants.
        //
        // Trust (2026-10-04, false proof): EVERY hop block — the switch block, the
        // `branch` block, the arm the fact is seeded at — must be entered ONLY from the
        // previous hop. The fact is seeded at the arm's ENTRY, for every path into it,
        // and rustc routes `let o = if c { a.get(i) } else { b.get(j) }; match o`
        // through ONE switch block that both calls target directly: the arm then carried
        // `i < len(a)` AND `j < len(b)`, and `Some(_) => a[i]` PROVED at -O0 although
        // `c = false, a = [], b = [1]` panics (tests/ui/trust/slice_get_try_index_bound.rs
        // `join_match`, `join_try`).
        //
        // Trust (TINV-21, 2026-10-06): or — `get(..).copied()`, the P1 `peek` spelling —
        // the direct target is core's authenticated `Option::copied` on `move dest`
        // ([`option_copied_hop`]), and ITS result reaches a clean switch or `branch` hop
        // the same way. `copied` (`T: Copy`) runs no user code, writes only its
        // destination and keeps the variant, so the `Some` arm after it is reached only
        // when `get` returned `Some`. `cloned` is NOT a hop: it runs a user `Clone`.
        let preds = preds
            .get_or_insert_with(|| crate::generate::block_predecessor_edges_rc_for(func))
            .as_slice();
        let direct = clean_variant_switch_target(blocks, preds, b.id, *target, dest.local, 1);
        let Some(some_bb) = direct
            .or_else(|| try_branch_continue_target(func, blocks, preds, b.id, *target, dest.local))
            .or_else(|| {
                let (copied_bb, copied_dest, next) =
                    option_copied_hop(func, blocks, preds, b.id, *target, dest.local)?;
                option_some_arm(func, blocks, preds, copied_bb, next, copied_dest)
            })
        else {
            continue;
        };
        // Trust (2026-10-10, review round 101): the seed is a definition of the `Some`
        // block, so it must hold on EVERY entry to it: `let o = if c { s.get(i) } else {
        // Some(&0) }; match o { Some(_) => s[i], .. }` returns into a JOIN, and `i <
        // len(s)` was seeded for the `Some(&0)` path too (kernel-certified; panics at
        // `f(&[1, 2, 3], 10, false)`). Upstream's hop walk above
        // (`clean_variant_switch_target` and its `?`/`copied` twins) already requires
        // every hop block and the arm to be entered only from the previous hop; the
        // entry block, whose implicit entry is no edge, is refused here as before.
        if some_bb.0 == 0 {
            continue;
        }
        let Some(len_f) = slice_len_formula(func, recv) else { continue };

        let mut facts: Vec<Formula> = Vec::new();
        match idx {
            Operand::Constant(ConstValue::Uint(v, _)) => {
                facts
                    .push(Formula::Lt(Box::new(Formula::Int(*v as i128)), Box::new(len_f.clone())));
            }
            Operand::Copy(p) | Operand::Move(p)
                if matches!(
                    crate::operand_ty_cow(func, idx).as_deref(),
                    Some(Ty::Int { signed: false, .. })
                ) =>
            {
                // Only Deref/Field projections keep a stable, version-renameable
                // place name (an Index projection embeds another local's value).
                let stable_place = p.projections.iter().all(|pr| {
                    matches!(pr, trust_types::Projection::Deref | trust_types::Projection::Field(_))
                });
                if stable_place {
                    facts.push(Formula::Lt(
                        Box::new(Formula::var_owned(crate::place_to_var_name(func, p), Sort::Int)),
                        Box::new(len_f.clone()),
                    ));
                }
                // Trace one Use-copy: `_t = Copy(src); … get(recv, _t)` — credit the
                // SOURCE place too (the overflowing `self.idx + 1` reads the FIELD,
                // not the arg temp). Gated: the copy must be in the CALL block with
                // no later same-block write overlapping the source base.
                if p.projections.is_empty()
                    && crate::local_defs::has_one_explicit_def(func, p.local)
                    && let Some((src_stmt_idx, src)) =
                        b.stmts.iter().enumerate().find_map(|(i, s)| match s {
                            Statement::Assign {
                                place,
                                rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
                                ..
                            } if place.local == p.local && place.projections.is_empty() => {
                                Some((i, src))
                            }
                            _ => None,
                        })
                    && src.projections.iter().all(|pr| {
                        matches!(
                            pr,
                            trust_types::Projection::Deref | trust_types::Projection::Field(_)
                        )
                    })
                    && !b.stmts.iter().skip(src_stmt_idx + 1).any(|s| {
                        matches!(
                            s,
                            Statement::Assign { place, .. } if place.local == src.local
                        )
                    })
                    // Trust (2026-10-10, review round 104): a write THROUGH a borrow of the
                    // source names the pointer, not `src`: `let t = i; let p = &mut i; *p =
                    // 100; s.get(t)` credited `i < len(s)` to the new `i` (kernel-certified,
                    // indexed 100). A mutably borrowed source gets no credit.
                    && !value_local_is_mut_borrowed(func, src.local)
                {
                    facts.push(Formula::Lt(
                        Box::new(Formula::var_owned(
                            crate::place_to_var_name(func, src),
                            Sort::Int,
                        )),
                        Box::new(len_f.clone()),
                    ));
                }
            }
            // Trust (2026-09-29): `get(a..b)` on a slice returns `Some` exactly when
            // `a <= b <= len`, and then the sub-slice `[a, b)`, of length `b - a`.
            // Measured on the ordinary-Rust sweep: `if let Some(s) = v.get(1..3) {
            // s[0].max(s[1]) }` was refuted with `s__slice_len = 0`. The bounds must
            // each be a constant or a local holding ONE value for the whole body, so
            // the fact seeded at the `Some` arm reads the values the call saw.
            Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                if let Some((start, end)) = exclusive_usize_range_bounds(func, p.local) {
                    let payload = trust_types::Place {
                        local: dest.local,
                        projections: vec![
                            trust_types::Projection::Downcast(1),
                            trust_types::Projection::Field(0),
                        ],
                    };
                    if let Some(sub_len) = slice_len_formula(func, &Operand::Copy(payload)) {
                        facts.push(Formula::Le(Box::new(start.clone()), Box::new(end.clone())));
                        facts.push(Formula::Le(Box::new(end.clone()), Box::new(len_f.clone())));
                        facts.push(Formula::Eq(
                            Box::new(sub_len),
                            Box::new(Formula::Sub(Box::new(end), Box::new(start))),
                        ));
                    }
                }
            }
            _ => {}
        }
        if !facts.is_empty() {
            out.entry(some_bb).or_default().extend(facts);
        }
    }
    out
}

/// `(start, end)` of the `core::ops::Range<usize>` aggregate that is `local`'s one
/// value, each a constant or a whole local holding one value for the whole body.
fn exclusive_usize_range_bounds(
    func: &VerifiableFunction,
    local: usize,
) -> Option<(Formula, Formula)> {
    if crate::local_defs::is_parameter(func, local) {
        return None;
    }
    let Some(Ty::Adt { name, .. }) = crate::local_ty_ref(func, local) else { return None };
    if name.split('<').next() != Some("core::ops::range::Range") {
        return None;
    }
    let Rvalue::Aggregate(_, ops) = crate::local_defs::unique_value_def(func, local)? else {
        return None;
    };
    let [start, end] = ops.as_slice() else { return None };
    let bound = |op: &Operand| match op {
        Operand::Constant(ConstValue::Uint(v, _)) => i128::try_from(*v).ok().map(Formula::Int),
        Operand::Copy(q) | Operand::Move(q)
            if q.projections.is_empty()
                && matches!(
                    crate::local_ty_ref(func, q.local),
                    Some(Ty::Int { signed: false, .. })
                )
                && crate::local_defs::is_single_static_assignment(func, q.local) =>
        {
            Some(Formula::var_owned(crate::place_to_var_name(func, q), Sort::Int))
        }
        _ => None,
    };
    Some((bound(start)?, bound(end)?))
}

/// Whether `bid` is entered by exactly ONE edge, from `from`. `preds` must be the per-EDGE
/// relation ([`block_predecessor_edges`]): over the deduplicated one, two edges from one
/// switch read as one (VARIANT-ARM-DUP-EDGE-1). `bb0` never qualifies: it also has the
/// implicit function-entry edge.
fn sole_predecessor_is(preds: &[Vec<BlockId>], bid: BlockId, from: BlockId) -> bool {
    bid.0 != 0 && preds.get(bid.0).is_some_and(|p| p.as_slice() == [from])
}

/// Trust (TINV-21, 2026-10-06): whether `s` is a statement a hop block may carry beside
/// its one value-carrying step — a `StorageLive`/`StorageDead` of a local NOT in `hop`,
/// or a `Nop` — and nothing else.
///
/// WHY ONLY THESE. A hop carries the `Some`-ness of a call's result to an arm through
/// the VALUE of one local per block (the local it switches on, or the argument it moves
/// into the next call, and that call's destination or the discriminant temp). A storage
/// marker writes no value, so one naming any OTHER local cannot change what the hop
/// reads (rustc's own MIR puts `StorageDead` of the call's already-moved arguments, and
/// of the previous hop's consumed destination, exactly there: the P1 fixture's `peek`
/// and `bump`). A marker naming a hop local is refused: `StorageDead` and `StorageLive`
/// both leave it uninitialized. Every other statement kind is refused — `Assign`,
/// `SetDiscriminant`, `Deinit`, `Retag`, `PlaceMention`, an intrinsic, anything added
/// later.
fn hop_marker_ok(s: &Statement, hop: &[usize]) -> bool {
    match s {
        Statement::StorageLive(l) | Statement::StorageDead(l) => !hop.contains(l),
        Statement::Nop => true,
        _ => false,
    }
}

/// The target of variant tag `tag` when block `bid` — entered only from `from` — reads
/// `discriminant(local)` into a temp and switches on it, with no other statement in
/// the block but [`hop_marker_ok`] markers (none naming `local` or the temp), and that
/// target is entered only from `bid`.
fn clean_variant_switch_target(
    blocks: &[trust_types::BasicBlock],
    preds: &[Vec<BlockId>],
    from: BlockId,
    bid: BlockId,
    local: usize,
    tag: u128,
) -> Option<BlockId> {
    if !sole_predecessor_is(preds, bid, from) {
        return None;
    }
    let tb = blocks.get(bid.0).filter(|tb| tb.id == bid)?;
    // Exactly ONE statement is the discriminant read of `local` into a whole temp.
    let mut disc: Option<(usize, usize)> = None;
    for (i, s) in tb.stmts.iter().enumerate() {
        if let Statement::Assign { place, rvalue: Rvalue::Discriminant(src), .. } = s
            && place.projections.is_empty()
            && src.projections.is_empty()
            && src.local == local
        {
            if disc.is_some() {
                return None;
            }
            disc = Some((i, place.local));
        }
    }
    let (disc_at, disc_local) = disc?;
    if disc_local == local {
        return None;
    }
    // Every other statement is a marker naming neither `local` nor the temp.
    if !tb
        .stmts
        .iter()
        .enumerate()
        .all(|(i, s)| i == disc_at || hop_marker_ok(s, &[local, disc_local]))
    {
        return None;
    }
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &tb.terminator else {
        return None;
    };
    if operand_bare_local(discr) != Some(disc_local) {
        return None;
    }
    let arm = targets.iter().find(|(v, _)| *v == tag).map(|(_, t)| *t)?;
    // Trust (2026-10-06, VARIANT-ARM-DUP-EDGE-1, false proof): the arm must be reached
    // by THIS label alone — the only one of the switch's edges into it (no other value
    // maps to it, and it is not `otherwise`) — and by no edge from anywhere else. rustc
    // -O0 lowers `match a.get(i) { Some(_) => {}, None => {} }; a[i]` to
    // `switchInt(d) -> [0: bb3, 1: bb3, otherwise: bb2]`: over deduplicated predecessors
    // `bb3` was "entered only from the switch", the `Some` fact `i < len(a)` was seeded
    // at the join both arms reach, and `a[i]` PROVED although `a = [], i = 0` panics
    // (tests/ui/trust/slice_get_try_index_bound.rs `dup_target`).
    if switch_edges_into(targets, *otherwise, arm) != 1 {
        return None;
    }
    sole_predecessor_is(preds, arm, bid).then_some(arm)
}

/// The `Continue` arm of `br = <Option<_> as Try>::branch(move opt)` when block `bid`
/// is exactly that call (no statements) and its direct target switches cleanly on
/// `br`'s discriminant. The callee must carry the authenticated
/// `SysrootItem::TryBranch` tag from the real sysroot; its `Self` is fixed by the
/// argument, whose type is a modeled core `Option`.
fn try_branch_continue_target(
    func: &VerifiableFunction,
    blocks: &[trust_types::BasicBlock],
    preds: &[Vec<BlockId>],
    from: BlockId,
    bid: BlockId,
    opt: usize,
) -> Option<BlockId> {
    if !sole_predecessor_is(preds, bid, from) {
        return None;
    }
    let tb = blocks.get(bid.0).filter(|tb| tb.id == bid)?;
    let Terminator::Call { callee_key: Some(key), args, dest, target: Some(next), .. } =
        &tb.terminator
    else {
        return None;
    };
    if !key.krate_is_real_sysroot
        || key.sysroot_item != Some(trust_types::SysrootItem::TryBranch)
        || !dest.projections.is_empty()
        || dest.local == opt
    {
        return None;
    }
    // TINV-21: storage markers only, none naming `opt` or the `branch` result.
    if !tb.stmts.iter().all(|s| hop_marker_ok(s, &[opt, dest.local])) {
        return None;
    }
    let [Operand::Move(arg)] = args.as_slice() else { return None };
    if arg.local != opt || !arg.projections.is_empty() {
        return None;
    }
    if !matches!(crate::local_ty_ref(func, opt)?, Ty::Adt { name, .. } if name == "core::option::Option")
    {
        return None;
    }
    let Ty::Adt { name, variants, .. } = crate::local_ty_ref(func, dest.local)? else {
        return None;
    };
    if name != "core::ops::control_flow::ControlFlow" {
        return None;
    }
    let tag = variants.iter().find(|v| v.name == "Continue")?.discriminant;
    clean_variant_switch_target(blocks, preds, bid, *next, dest.local, u128::try_from(tag).ok()?)
}

/// Trust (TINV-21, 2026-10-06): the declared discriminant of `Some` in `local`'s type,
/// when that type is the modeled core/std `Option` (`modeled_std_enum_shape`: the
/// std path, a `__tag` field and exactly the `None`/`Some` variants). READ OFF THE
/// TYPE, never assumed: a crate-local `enum Option { Some(u8), None }` has `Some = 0`
/// and is refused by the shape gate, so a `None`-arm fact can never be minted under the
/// `Some` label.
pub(crate) fn option_some_tag(func: &VerifiableFunction, local: usize) -> Option<u128> {
    let ty = crate::local_ty_ref(func, local)?;
    let (name, variants) = crate::generate::modeled_std_enum_shape(ty)?;
    if name != "core::option::Option" && name != "std::option::Option" {
        return None;
    }
    u128::try_from(variants.iter().find(|v| v.name == "Some")?.discriminant).ok()
}

/// Trust (TINV-21, 2026-10-06): the `Some` arm of an `Option` value `opt` written by the
/// terminator of `from`, whose direct target is `bid`: either `bid` switches cleanly on
/// `opt` ([`clean_variant_switch_target`], the `Some` tag from [`option_some_tag`]), or
/// `bid` is core's authenticated `Try::branch` on `move opt` and its `Continue` arm
/// ([`try_branch_continue_target`]). Every hop is entered only from the previous one and
/// carries only [`hop_marker_ok`] markers beside its step. Shared by the `get`-`Some`
/// recognizer and the TINV arm-fact sites (`type_invariant::obligations::arm_fact_sites`).
/// `preds` MUST be the per-edge relation ([`block_predecessor_edges`];
/// VARIANT-ARM-DUP-EDGE-1).
pub(crate) fn option_some_arm(
    func: &VerifiableFunction,
    blocks: &[trust_types::BasicBlock],
    preds: &[Vec<BlockId>],
    from: BlockId,
    bid: BlockId,
    opt: usize,
) -> Option<BlockId> {
    option_some_tag(func, opt)
        .and_then(|tag| clean_variant_switch_target(blocks, preds, from, bid, opt, tag))
        .or_else(|| try_branch_continue_target(func, blocks, preds, from, bid, opt))
}

/// [`option_some_arm`] over the body's own predecessor relation.
pub(crate) fn option_some_arm_of_call(
    func: &VerifiableFunction,
    from: BlockId,
    bid: BlockId,
    opt: usize,
) -> Option<BlockId> {
    // VARIANT-ARM-DUP-EDGE-1: per-EDGE predecessors (see `block_predecessor_edges_uncached`).
    let preds = crate::generate::block_predecessor_edges_rc_for(func);
    option_some_arm(func, &func.body.blocks, &preds, from, bid, opt)
}

/// Trust (TINV-21, 2026-10-06): the `copied` hop. Block `bid` — entered only from
/// `from` — is `out = Option::copied(move opt) -> next`, authenticated as core's
/// `SysrootItem::OptionCopied` from the real sysroot (never by name), with only
/// [`hop_marker_ok`] markers beside it (none naming `opt` or `out`), `opt` and `out` both
/// the modeled core `Option`, and `out` a whole local other than `opt`. Returns
/// `(bid, out, next)`.
///
/// WHY THE FACT SURVIVES IT. `Option::<&T>::copied` / `Option::<&mut T>::copied` require
/// `T: Copy`: the body is `match self { Some(&v) => Some(v), None => None }`, a bitwise
/// copy that runs no user code, writes nothing but `out`, and maps `Some` to `Some` and
/// `None` to `None`. So `out` is `Some` exactly when `opt` was, and no index source or
/// slice a `get`-`Some` fact names can change across the call. (A model havoc of other
/// names at the call only makes them fresh; a true fact about the arm's real values stays
/// true.) `cloned` runs a user `Clone::clone`, which can write through a stash or a
/// global (CALL-HAVOC-ESCAPE-1): it is not declared and never a hop.
fn option_copied_hop(
    func: &VerifiableFunction,
    blocks: &[trust_types::BasicBlock],
    preds: &[Vec<BlockId>],
    from: BlockId,
    bid: BlockId,
    opt: usize,
) -> Option<(BlockId, usize, BlockId)> {
    if !sole_predecessor_is(preds, bid, from) {
        return None;
    }
    let tb = blocks.get(bid.0).filter(|tb| tb.id == bid)?;
    let Terminator::Call { callee_key: Some(key), args, dest, target: Some(next), .. } =
        &tb.terminator
    else {
        return None;
    };
    if !key.krate_is_real_sysroot
        || key.sysroot_item != Some(trust_types::SysrootItem::OptionCopied)
        || !dest.projections.is_empty()
        || dest.local == opt
    {
        return None;
    }
    let [Operand::Move(arg)] = args.as_slice() else { return None };
    if arg.local != opt || !arg.projections.is_empty() {
        return None;
    }
    if !tb.stmts.iter().all(|s| hop_marker_ok(s, &[opt, dest.local])) {
        return None;
    }
    option_some_tag(func, opt)?;
    option_some_tag(func, dest.local)?;
    Some((bid, dest.local, *next))
}

pub(crate) fn enum_construction_demux_definitions(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    let mut out: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    if !crate::generate::terminator_presence_for(func).has_switch_int {
        return out;
    }
    let blocks = &func.body.blocks;
    let mut preds: Option<std::rc::Rc<Vec<Vec<BlockId>>>> = None;

    for (j_idx, j_block) in blocks.iter().enumerate() {
        // BUDGET POLL, per CANDIDATE JOIN: every block is probed as a join, and a
        // surviving candidate then costs a `local_is_mutably_borrowed` whole-function
        // walk plus one `extract_block_definitions` per predecessor, so this scan is
        // quadratic in a wide CFG and polled nothing. `out` as-is is the degradation:
        // the joins already routed keep their COMPLETE fact sets (each join is
        // finished before the next begins), and the remaining joins route nothing.
        // These facts are hypotheses seeded into the path-definition map
        // (`v2_build_path_definition_map`), so an arm that loses them sees an
        // unconstrained payload — PROVE turns into FAIL, never FAIL into PROVE.
        if trust_types::verify_budget::budget_exhausted() {
            return out;
        }
        let j = BlockId(j_idx);
        // J ends in a SwitchInt on a discriminant temp defined within J itself.
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &j_block.terminator else {
            continue;
        };
        let Some(d_local) = operand_bare_local(discr) else {
            continue;
        };
        // Locate `d = Discriminant(place)` and require J assigns ONLY `d` (no
        // statement may clobber `place` or a payload operand before the switch).
        let mut place_local: Option<usize> = None;
        let mut j_clean = true;
        for stmt in &j_block.stmts {
            match stmt {
                Statement::Assign { place: p, rvalue, .. } => {
                    if p.local != d_local || !p.projections.is_empty() {
                        j_clean = false;
                        break;
                    }
                    if let Rvalue::Discriminant(src) = rvalue
                        && src.projections.is_empty()
                    {
                        place_local = Some(src.local);
                    }
                }
                Statement::SetDiscriminant { .. } | Statement::Deinit { .. } => {
                    j_clean = false;
                    break;
                }
                _ => {}
            }
        }
        if !j_clean {
            continue;
        }
        let Some(place_local) = place_local else {
            continue;
        };

        // Every predecessor of J must be a single-pred `Goto(J)` block whose
        // whole-`place` assignment is an ADT aggregate. Collect payload facts per
        // variant; bail on any non-conforming predecessor, and disable any variant
        // built by more than one predecessor (its payload is not unique).
        let preds = preds
            .get_or_insert_with(|| crate::generate::block_predecessors_rc_for(func))
            .as_slice();
        let j_preds = &preds[j_idx];
        if j_preds.len() < 2 {
            continue;
        }
        // Fast structural pre-check: before scanning the whole function in
        // `local_is_mutably_borrowed` or running `extract_block_definitions` on
        // predecessors, verify that every J-predecessor is a `Goto(J)` block
        // containing a whole-`place` ADT aggregate construction.
        let all_preds_construct = j_preds.iter().all(|&p| {
            let pb = &blocks[p.0];
            matches!(&pb.terminator, Terminator::Goto(t) if *t == j)
                && pb.stmts.iter().any(|stmt| {
                    matches!(
                        stmt,
                        Statement::Assign {
                            place: p2,
                            rvalue: Rvalue::Aggregate(
                                AggregateKind::Adt { active_field: None, .. },
                                _
                            ),
                            ..
                        } if p2.local == place_local && p2.projections.is_empty()
                    )
                })
        });
        if !all_preds_construct {
            continue;
        }

        // SOUNDNESS (P0 false proof, 2026-06-17 hunt-7): if the enum local is mutably borrowed
        // anywhere — `&mut o` / `&raw mut o`, OR a call taking `&mut o` such as `o.as_mut()` —
        // its payload can be REASSIGNED after construction (`if let Some(r) = o.as_mut() { *r = b; }`
        // then `match o { Some(i) => arr[i] }`), so routing the CONSTRUCTION-time payload fact
        // `o@field == V` into the match arm is STALE and vacuously discharges a bounds/overflow
        // obligation on the mutated payload (`arr[i]` PROVED in-bounds while `i` became `b`). The
        // demux re-injects the fact past the normal mutable-borrow kill, so guard it HERE. (The
        // mutating `&mut o` materializes as a `Ref{mutable:true}` statement even for `o.as_mut()`.)
        if local_is_mutably_borrowed(func, place_local) {
            continue;
        }
        let mut by_variant: FxHashMap<usize, Vec<Formula>> = FxHashMap::default();
        let mut duplicate_variants: FxHashSet<usize> = FxHashSet::default();
        let mut all_conform = true;
        for &p in j_preds {
            // BUDGET POLL, per PREDECESSOR: the per-join poll above cannot interrupt
            // ONE join, and this is where the join's cost is — `extract_block_
            // definitions` (a whole-block extraction with its own array-version
            // prepass) plus `expand_nested_payload_facts` for every incoming
            // construction arm.
            //
            // Returning `out` ABANDONS this join entirely instead of routing what was
            // collected: `by_variant` is only sound once EVERY predecessor has been
            // seen, because a variant built by two of them is disabled by
            // `duplicate_variants` — bailing mid-loop would leave the second
            // constructor unseen, the variant un-disabled, and ONE arm's payload fact
            // routed as if it were unique (a fact FALSE on the other path, hence a
            // false PROVE). Dropping the whole join is the same "fewer facts routed"
            // degradation, and it is the only fail-closed one here.
            if trust_types::verify_budget::budget_exhausted() {
                return out;
            }
            let pb = &blocks[p.0];
            // Payload routing needs every J-predecessor to be a `Goto(J)` block that
            // overwrites `place` wholesale (the construction check below). P_k's OWN
            // predecessor count is irrelevant to payload soundness: the payload fact
            // is P_k's own aggregate, valid whenever P_k runs, and reaching the arm
            // implies P_k ran (variant uniqueness). Guard routing, which DOES need a
            // unique incoming edge, gates on `preds[p.0].len() == 1` separately below.
            // Requiring single-pred here would wrongly bail whole joins like `flag_some`
            // whose None constructor is shared by the flag-false and guard-false paths.
            let is_construction_arm = matches!(&pb.terminator, Terminator::Goto(t) if *t == j);
            if !is_construction_arm {
                all_conform = false;
                break;
            }
            // Last whole-`place` ADT aggregate assignment in the block.
            let mut construction: Option<(usize, &AggregateKind, usize)> = None;
            for stmt in &pb.stmts {
                if let Statement::Assign { place: p2, rvalue: Rvalue::Aggregate(kind, ops), .. } =
                    stmt
                    && p2.local == place_local
                    && p2.projections.is_empty()
                    && let AggregateKind::Adt { variant, active_field: None, .. } = kind
                {
                    construction = Some((*variant, kind, ops.len()));
                }
            }
            let Some((variant, kind, arity)) = construction else {
                all_conform = false;
                break;
            };
            // The variant-downcast payload field names this construction defines.
            let synth = trust_types::Place::local(place_local);
            let expected: FxHashSet<String> = (0..arity)
                .filter_map(|i| crate::aggregate_variant_field_place(&synth, kind, i))
                .map(|fp| crate::place_to_var_name(func, &fp))
                .collect();
            // Source the equalities from the block's own definitions so the
            // existing last-write / operand-clobber discipline already applies.
            let block_defs = extract_block_definitions(func, pb);
            let top_facts: Vec<Formula> = block_defs
                .iter()
                .filter(|f| match f {
                    Formula::Eq(lhs, _) => lhs.var_name().is_some_and(|n| expected.contains(n)),
                    _ => false,
                })
                .cloned()
                .collect();
            // (nested aggregate payloads): a tuple/struct-valued payload
            // field — `Some((a, b))` builds `_t = (a, b); place = Some(_t)` — routes
            // only the whole-aggregate equality `place@1.0 == _t`, but a destructuring
            // arm `Some((x, _))` reads the nested leaf `place@1.0.0`. Rewrite each
            // aggregate-valued payload equality into its leaf equalities by renaming
            // the temp's own field defs (`_t.0 == a` ⇒ `place@1.0.0 == a`). The
            // children come from `block_defs`, which already dropped any stale-operand
            // fact, so the leaves inherit that discipline; the rewrite is purely
            // additive (the whole-aggregate equality is kept) and each leaf is a
            // genuinely-true congruence consequence, hence monotone-safe.
            let facts = expand_nested_payload_facts(top_facts, &block_defs);
            // (guard routing): when P_k has a UNIQUE predecessor Q, every
            // path reaching this arm traverses the Q→P_k edge (the de-mux proves the
            // arm is reachable only via this unique variant-k constructor, and P_k is
            // entered only from Q), so that edge's guard is TRUE at the arm. Route the
            // resolved guard (e.g. `v < 100`) alongside the payload. The path-guard
            // enumerator instead weakens this guard under a disjunction with the
            // infeasible other-variant→arm path, which is exactly why it must be routed
            // here as an unconditional arm fact. Soundness: a genuinely-true fact, and
            // the clobber check drops it if P_k or J reassigns any of its free
            // variables (the arm's own reassignments are dropped later by
            // v2_live_path_defs) — so it can only turn a false-FAIL into a PROVE for
            // safe code, never make a real overflow PROVE.
            let mut guard_facts: Vec<Formula> = Vec::new();
            if let [q] = preds[p.0].as_slice() {
                let q_block = &blocks[q.0];
                let mut matched_gf: Option<Formula> = None;
                let mut multiple = false;
                for c in q_block.terminator.discovered_clauses(*q) {
                    if c.target != trust_types::ClauseTarget::Block(p) {
                        continue;
                    }
                    let gf = guard_to_formula(func, &c.guard);
                    if matches!(gf, Formula::Bool(true)) {
                        continue;
                    }
                    if matched_gf.is_some() {
                        multiple = true;
                        break;
                    }
                    matched_gf = Some(gf);
                }
                // Exactly one routable edge guard, else fail-closed: multiple clauses
                // (e.g. `0 | 1 => P_k`) would conjoin to a contradiction.
                if !multiple
                    && let Some(gf) = matched_gf
                {
                    let clobbered = guard_edge_clobbered_names(func, pb, j_block);
                    if trust_types::all_free_variable_names(&gf, &mut |fv| {
                        !name_clobbered(fv, &clobbered)
                    }) {
                        guard_facts.push(gf);
                    }
                }
            }
            if by_variant.contains_key(&variant) {
                duplicate_variants.insert(variant);
            }
            let entry = by_variant.entry(variant).or_default();
            entry.extend(facts);
            entry.extend(guard_facts);
        }
        if !all_conform {
            continue;
        }
        for v in &duplicate_variants {
            by_variant.remove(v);
        }
        if by_variant.is_empty() {
            continue;
        }

        // Route each variant's payload facts to the arm that downcasts `place` to
        // that variant. Eligible arms have J as sole predecessor and do not
        // themselves reassign `place`.
        let mut arm_targets: Vec<BlockId> =
            targets.iter().map(|(_, t)| *t).chain(std::iter::once(*otherwise)).collect();
        arm_targets.sort_by_key(|b| b.0);
        arm_targets.dedup();
        for arm in arm_targets {
            // BUDGET POLL, per ARM: a wide switch walks every arm block
            // (`arm_downcast_variants`) and clones the variant's whole fact list into
            // `out`. Sound to interrupt HERE in a way the predecessor loop was not:
            // `by_variant` is final (all predecessors conformed and the duplicated
            // variants were removed), and each arm is routed independently, so a
            // routed subset is a subset of the same true facts — fewer hypotheses at
            // the arms left unrouted.
            if trust_types::verify_budget::budget_exhausted() {
                return out;
            }
            if arm.0 >= blocks.len() || preds[arm.0].as_slice() != [j] {
                continue;
            }
            // Trust (2026-10-06, VARIANT-ARM-DUP-EDGE-1): `preds` is deduplicated, so an
            // arm two labels of J's switch reach (`[0: A, 1: A]`, or a label and
            // `otherwise`) passed the gate above although another variant also enters it;
            // its routed guard facts are then false on that other variant's path. Require
            // exactly one of the switch's edges into the arm.
            if switch_edges_into(targets, *otherwise, arm) != 1 {
                continue;
            }
            let arm_block = &blocks[arm.0];
            if block_assigns_local(arm_block, place_local) {
                continue;
            }
            for variant in arm_downcast_variants(arm_block, place_local) {
                if let Some(facts) = by_variant.get(&variant) {
                    out.entry(arm).or_default().extend(facts.iter().cloned());
                }
            }
        }
    }
    out
}

/// The bare local of a projection-less `Copy`/`Move` operand, else `None`.
fn operand_bare_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
        _ => None,
    }
}

/// True if any statement writes a place rooted at `local` (whole-local or any
/// field/discriminant of it) — a write that would invalidate a routed payload
/// fact about that local.
fn block_assigns_local(block: &BasicBlock, local: usize) -> bool {
    block.stmts.iter().any(|s| match s {
        Statement::Assign { place, .. }
        | Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place } => place.local == local,
        _ => false,
    })
}

/// Whole-local var-names written (assignments, set-discriminant, deinit, call
/// destinations) by `pk` or `j`. A routed edge guard whose free variables touch
/// any of these is stale by the time control reaches the arm. Every written place
/// is reduced to its WHOLE-local name so a field write (`opt.0 = …`) still records
/// the base local — `name_clobbered` then catches field/whole-local aliasing.
fn guard_edge_clobbered_names(
    func: &VerifiableFunction,
    pk: &BasicBlock,
    j: &BasicBlock,
) -> FxHashSet<String> {
    let mut locals: FxHashSet<usize> = FxHashSet::default();
    for block in [pk, j] {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, .. }
                | Statement::SetDiscriminant { place, .. }
                | Statement::Deinit { place } => {
                    locals.insert(place.local);
                }
                _ => {}
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator {
            locals.insert(dest.local);
        }
    }
    if locals.is_empty() {
        return FxHashSet::default();
    }
    let mut out = FxHashSet::with_capacity_and_hasher(locals.len(), Default::default());
    for l in locals {
        out.insert(crate::place_to_var_name(func, &trust_types::Place::local(l)));
    }
    out
}

/// True if free-variable name `fv` aliases any written whole-local name in
/// `clobbered`: either an exact match, or `fv` is a field/projection of a written
/// local (`w` followed by a projection char). Written names are clean base locals
/// (source identifier or `_N`, no projection chars), so prefix matching is exact.
fn name_clobbered(fv: &str, clobbered: &FxHashSet<String>) -> bool {
    if clobbered.is_empty() {
        return false;
    }
    let base_end =
        fv.bytes().position(|b| matches!(b, b'.' | b'@' | b'[' | b'*')).unwrap_or(fv.len());
    if clobbered.contains(&fv[..base_end]) {
        return true;
    }
    base_end < fv.len()
        && clobbered.iter().any(|w| {
            fv == w
                || (fv.len() > w.len()
                    && fv.starts_with(w.as_str())
                    && matches!(fv.as_bytes()[w.len()], b'.' | b'@' | b'[' | b'*'))
        })
}

/// True if var-name `child` is a strict field/projection of `parent` — `parent`
/// followed by a projection separator (`.`, `@`, `[`, `*`). `_t.0` is a child of
/// `_t`; `_t0` is not (`0` is not a separator).
fn is_strict_field_child(child: &str, parent: &str) -> bool {
    child.len() > parent.len()
        && child.starts_with(parent)
        && matches!(child.as_bytes()[parent.len()], b'.' | b'@' | b'[' | b'*')
}

/// Expand aggregate-valued payload equalities into their leaf equalities so a
/// nested `match`-arm read of a constructed tuple/struct payload is constrained.
///
/// `Some((a, b))` lowers to `_t = (a, b); place = Some(_t)`, so the routed payload
/// fact is the whole-aggregate `place@1.0 == _t` while the arm `Some((x, _))` reads
/// the leaf `place@1.0.0`. A fact's RHS is an aggregate exactly when `block_defs`
/// holds field children `_t.J == …` for its RHS name; rename the `_t` prefix to the
/// payload-field name (`place@1.0`) to obtain `place@1.0.J == …`, and re-queue each
/// leaf so nested aggregates expand fully.
///
/// Purely additive: every input fact is kept and leaves are appended. Each leaf is
/// a genuinely-true congruence consequence of the kept whole-aggregate equality and
/// the temp's field def — and the field def already passed `block_defs`'
/// stale-operand discipline, so a leaf whose source was dropped as stale is never
/// produced. Monotone-safe: it can turn a false-FAIL into a PROVE for safe code but
/// can never make a real overflow PROVE.
fn expand_nested_payload_facts(top_facts: Vec<Formula>, block_defs: &[Formula]) -> Vec<Formula> {
    if top_facts.is_empty() {
        return top_facts;
    }
    let has_var_rhs = top_facts.iter().any(|f| {
        matches!(f, Formula::Eq(lhs, rhs) if lhs.var_name().is_some() && rhs.var_name().is_some())
    });
    let projected_defs: Vec<(&str, &Formula, &Formula)> = if has_var_rhs {
        block_defs
            .iter()
            .filter_map(|d| {
                let Formula::Eq(cl, cr) = d else { return None };
                let cname = cl.var_name()?;
                cname
                    .bytes()
                    .any(|b| matches!(b, b'.' | b'@' | b'[' | b'*'))
                    .then_some((cname, cl.as_ref(), cr.as_ref()))
            })
            .collect()
    } else {
        Vec::new()
    };
    let mut out: Vec<Formula> = Vec::with_capacity(top_facts.len());
    let mut work: Vec<(Formula, usize)> = top_facts.into_iter().map(|f| (f, 0usize)).collect();
    while let Some((f, depth)) = work.pop() {
        // BUDGET POLL, per POP: the depth cap bounds the CHAIN, not the WORK — every
        // pop rescans all of `block_defs` with a prefix/string test per def, and each
        // matching child re-queues, so a block with many aggregate field defs makes
        // this drain quadratic with no time bound. It is reached once per
        // construction predecessor of every candidate join
        // (`enum_construction_demux_definitions`), which multiplies it again.
        //
        // Returning `out` as built is the degradation this function is already safe
        // under: it is PURELY ADDITIVE (every input fact is kept and true leaves are
        // appended), so any subset of its output is a subset of the same genuinely-true
        // congruence consequences. They are routed into a match arm as HYPOTHESES, so
        // losing leaves — or, bailing mid-drain, some of the input `top_facts` still on
        // the worklist and the popped `f` itself — leaves the arm's payload less
        // constrained: PROVE turns into FAIL, never FAIL into PROVE.
        if trust_types::verify_budget::budget_exhausted() {
            return out;
        }
        // Depth cap is a belt-and-braces guard; the def chain is acyclic (each temp
        // is built before use within the block), so expansion terminates anyway.
        if depth < 8
            && !projected_defs.is_empty()
            && let Formula::Eq(lhs, rhs) = &f
            && let Some(lhs_name) = lhs.var_name()
            && let Some(rhs_name) = rhs.var_name()
        {
            for &(cname, cl, cr) in &projected_defs {
                // BUDGET POLL, per DEF PROBE: the per-pop poll above cannot interrupt
                // ONE pop — this scan is the whole cost of a pop, and a single fact
                // with many field children can also re-queue unboundedly from here.
                // Same fail-closed degradation as the pop poll: `out` as built, minus
                // the facts still queued and the `f` being expanded.
                if trust_types::verify_budget::budget_exhausted() {
                    return out;
                }
                if is_strict_field_child(cname, rhs_name) {
                    let suffix = &cname[rhs_name.len()..];
                    let sort = cl.var_sort().cloned().unwrap_or(Sort::Int);
                    work.push((
                        Formula::Eq(
                            Box::new(Formula::Var(format!("{lhs_name}{suffix}"), sort)),
                            Box::new(cr.clone()),
                        ),
                        depth + 1,
                    ));
                }
            }
        }
        out.push(f);
    }
    out
}

/// Variant indices that `block` downcasts `target_local` to (across every place
/// read or written by its assignments).
fn arm_downcast_variants(block: &BasicBlock, target_local: usize) -> FxHashSet<usize> {
    let mut out = FxHashSet::default();
    for stmt in &block.stmts {
        if let Statement::Assign { place, rvalue, .. } = stmt {
            push_place_downcasts(place, target_local, &mut out);
            rvalue_place_downcasts(rvalue, target_local, &mut out);
        }
    }
    out
}

fn push_place_downcasts(
    place: &trust_types::Place,
    target_local: usize,
    out: &mut FxHashSet<usize>,
) {
    if place.local != target_local {
        return;
    }
    for proj in &place.projections {
        if let trust_types::Projection::Downcast(v) = proj {
            out.insert(*v);
        }
    }
}

fn rvalue_place_downcasts(rvalue: &Rvalue, target_local: usize, out: &mut FxHashSet<usize>) {
    fn vop(op: &Operand, target_local: usize, out: &mut FxHashSet<usize>) {
        if let Operand::Copy(p) | Operand::Move(p) = op {
            push_place_downcasts(p, target_local, out);
        }
    }
    match rvalue {
        Rvalue::Use(o) | Rvalue::UnaryOp(_, o) | Rvalue::Cast(o, _) | Rvalue::Repeat(o, _) => {
            vop(o, target_local, out)
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            vop(a, target_local, out);
            vop(b, target_local, out);
        }
        Rvalue::Aggregate(_, ops) | Rvalue::Unsupported { operands: ops, .. } => {
            for o in ops {
                vop(o, target_local, out);
            }
        }
        Rvalue::Ref { place, .. }
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::AddressOf(_, place)
        | Rvalue::CopyForDeref(place) => push_place_downcasts(place, target_local, out),
        _ => {}
    }
}

/// Trust: the FREE base array term for the McCarthy array-theory channel —
/// `arr$local$base`, an unconstrained `(Array Int elem)`. Element positions not
/// pinned by a construction store read as unconstrained from it (sound).
fn array_free_base(local: usize, elem: &Sort) -> Formula {
    Formula::Var(
        format!("arr${local}$base"),
        Sort::Array(Box::new(Sort::Int), Box::new(elem.clone())),
    )
}

/// Trust: seed equality for `[e0, e1, .., eN-1]` construction of array-theory
/// local `local`: `v0 == Store(.. Store(FREE_base, 0, e0) .., N-1, eN-1)`.
fn array_construction_seed(
    func: &VerifiableFunction,
    local: usize,
    elem: &Sort,
    operands: &[Operand],
    read_ctx: &ArrayReadCtx<'_>,
) -> Option<Formula> {
    let mut acc = array_free_base(local, elem);
    for (i, op) in operands.iter().enumerate() {
        let value = operand_to_formula_with_array_ctx(func, op, Some(read_ctx));
        acc = Formula::Store(Box::new(acc), Box::new(Formula::Int(i as i128)), Box::new(value));
    }
    Some(Formula::Eq(Box::new(crate::array_term_var(local, 0, elem.clone())), Box::new(acc)))
}

/// Trust: seed equality for `[op; count]` construction:
/// `v0 == ((as const (Array Int elem)) op)`, the constant array whose every
/// lane is `op`. The term is the same four nodes for every `count`; `count`
/// does not occur in it at all.
///
/// It replaces a `count`-long Store chain over the free base (built only while
/// `count <= 64`, so its cost grew with the array's VALUE-LEVEL length) and,
/// above 64, a bare free base that lost `op` altogether (every element read of
/// a large `[v; N]` was unconstrained, a false FAIL).
///
/// SOUNDNESS. On the Rust lanes `0..count` the constant array is exactly the
/// value the construction builds. It also pins the lanes at and beyond `count`
/// to `op`, where the old chain left them free. Those lanes are unobservable:
/// every element read of an array-theory local is `a[i]` through a bounds-
/// checked `Index`, whose in-bounds obligation is generated separately, and the
/// array channel never equates two array terms unless one side is a fresh
/// version (`v0` here, `v{n+1}` for a store). `array_theory_local` keeps that
/// last premise true: `v0` has at most one definition (one whole-local write,
/// none for a parameter, whose entry value is the other) and the local never
/// escapes.
fn array_repeat_seed(
    func: &VerifiableFunction,
    local: usize,
    elem: &Sort,
    op: &Operand,
    read_ctx: &ArrayReadCtx<'_>,
) -> Option<Formula> {
    let value = operand_to_formula_with_array_ctx(func, op, Some(read_ctx));
    Some(Formula::Eq(
        Box::new(crate::array_term_var(local, 0, elem.clone())),
        Box::new(Formula::const_array(Sort::Int, elem.clone(), value)),
    ))
}

fn aggregate_field_definitions(
    func: &VerifiableFunction,
    place: &trust_types::Place,
    kind: &AggregateKind,
    operands: &[Operand],
) -> Vec<(String, Formula)> {
    let has_variant_twin = matches!(kind, AggregateKind::Adt { active_field: None, .. });
    let mut defs = Vec::with_capacity(if has_variant_twin {
        operands.len().saturating_mul(2)
    } else {
        operands.len()
    });
    for (index, operand) in operands.iter().enumerate() {
        let value_formula = operand_to_formula(func, operand);
        // Trust: a field write produces up to two equalities under different
        // naming conventions. The struct-style place `o.<i>` matches a struct
        // field read; the variant-downcast place `o@<v>.<i>` matches an enum
        // `match`-arm payload read (`(o as Some).0`). `AggregateKind::Adt`
        // cannot distinguish struct from enum, so emit whichever apply — a
        // local has a single type, so exactly one name is ever read; the
        // other is a dangling equality on a fresh variable that appears in no
        // obligation (sound: it can neither false-prove nor false-fail; the
        // discriminant lives in the separate `discr_` namespace). Fixes the
        // previously unconstrained enum payload that let the solver pick an
        // overflowing value for `let o = Some(7); match o { Some(v) => v + 1 }`.
        let variant_field_place = crate::aggregate_variant_field_place(place, kind, index);
        if let Some(field_place) = crate::aggregate_field_place(place, kind, index, operands.len())
        {
            let field_name = crate::place_to_var_name(func, &field_place);
            let field_formula = Formula::var(
                &field_name,
                crate::place_sort(func, &field_place).unwrap_or(Sort::Int),
            );
            if !aggregate_def_sorts_disagree(&field_formula, &value_formula) {
                if variant_field_place.is_none() {
                    defs.push((
                        field_name,
                        Formula::Eq(Box::new(field_formula), Box::new(value_formula)),
                    ));
                    continue;
                }
                defs.push((
                    field_name,
                    Formula::Eq(Box::new(field_formula), Box::new(value_formula.clone())),
                ));
            }
        }
        if let Some(field_place) = variant_field_place {
            let field_name = crate::place_to_var_name(func, &field_place);
            let field_formula = Formula::var(
                &field_name,
                crate::place_sort(func, &field_place).unwrap_or(Sort::Int),
            );
            if !aggregate_def_sorts_disagree(&field_formula, &value_formula) {
                defs.push((
                    field_name,
                    Formula::Eq(Box::new(field_formula), Box::new(value_formula)),
                ));
            }
        }
    }
    defs
}

/// Trust (AGG-BOOL-TWIN-SORT-1, 2026-10-06): would `field == value` be an
/// ill-sorted equality between a `Bool` and a non-`Bool` term?
///
/// THE DEFECT, measured on the stage 1 of `0ac7a96d9f` (`integ/wave18`). A field
/// write produces two names (above): the struct-style `o.<i>` and the downcast
/// twin `o@<v>.<i>`. For a STRUCT the twin's type does not resolve (a struct's
/// fields carry no `__v<v>_` prefix, so `declared_ty_step` finds none), and its
/// variable falls back to `Int`; for an ENUM the bare `o.<i>` reads the flattened
/// field list (`__tag` first). So a `bool` field written by an aggregate became
/// `Var(o@0.2, Int) == Bool(false)`: `core::ops::RangeInclusive { start, end,
/// exhausted: false }`, which every `a..=b` that an explicit MIR inliner exposes
/// builds. `trust_types::check_formula_sort` rejects an equality whose sides
/// differ, so in-process ay DECLINED the whole VC ("VC formula is sort-invalid"),
/// and an always-violated `SliceBoundsCheck` row came back `Unknown`, which the
/// default, strict and memory-safe policies report as runtime-checked: under
/// `-Zinline-mir=yes`, `let r = black_box(0usize..=4); &a[r]` and
/// `&a[core::range::RangeInclusive::from(0..=4)]` built rc=0 and panicked, while
/// at `-O0` the same rows were FAILED by ay.
///
/// Such an equality says nothing any lane can use, and the twin it comes from is
/// the name the program never reads (a local has one type), so dropping it only
/// removes a hypothesis. Restricted to the `Bool`/non-`Bool` mismatch, the one
/// no lane coerces; a numeric sort mismatch is left as it was.
fn aggregate_def_sorts_disagree(field: &Formula, value: &Formula) -> bool {
    match (crate::formula_sort(field), crate::formula_sort(value)) {
        (Some(a), Some(b)) => a != b && (a == Sort::Bool || b == Sort::Bool),
        _ => false,
    }
}

/// Trust (ENC-DEFECTS 13a, 2026-09-26): the declared discriminant tags of a
/// FIELDLESS enum type — an enum every one of whose variants carries no field
/// (`enum Motion { Idle, Up, Down }`, `#[repr(i8)] enum E { A = -1, B = 3 }`) — in
/// variant-index order, or `None`.
///
/// THE MODEL THIS LICENSES. A fieldless enum value is determined by its variant,
/// and its variant by its discriminant, so the value and its discriminant are in
/// bijection. The value's integer model (`Ty::Adt` lowers to `Sort::Int`) may
/// therefore BE the discriminant: construction pins it to the variant's tag
/// ([`fieldless_enum_construction_tag`]) and a `Discriminant` read returns it
/// unchanged ([`fieldless_enum_discriminant_read_def`]). Every other producer of a
/// fact about such a value already agrees with that reading or says nothing:
///  * a `Use` copy equates two values (a bijection preserves equality);
///  * `BinOp::Cmp` defines an `Ordering` result as `ite(-1, 0, 1)`
///    (`chc::try_binop_to_formula`), which IS `Ordering`'s discriminant set;
///  * a constant of the type reaches vcgen as the SAME `Aggregate` this arm reads
///    (`trust_mir_extract::convert_const_aggregate_rvalue`) or as a fresh opaque
///    symbol, never as a raw tag bit pattern;
///  * no int->ADT or ADT->int cast is modeled (`is_modeled_identity_cast` is
///    int/pointer only); rustc lowers `e as u8` as a `Discriminant` read (plus an
///    int cast when the types differ), and the one cast lane that reads the tags
///    (`enum-disc-index`) declines a negative one (`min_disc >= 0`);
///  * the interval lanes bound a `Discriminant` read by the enum's decoded tag
///    hull (`abstract_interp::transfer::discriminant_read_hull`, shared by
///    `value_analysis`). Until 2026-09-28 they said `[0, MAX]` for EVERY read, which
///    a negative tag contradicts — the independent review's rd01
///    (`#[repr(i8)] enum S { Neg = -1, .. }`, `s as i8 - 127 - 1` proved on a
///    parameter, pre-existing on main): the one producer that did NOT agree.
///
/// GATES (each fails closed to "no model", i.e. today's free value):
///  * `adt_kind == Some(Enum)` — a `Ty::Adt` with `variants: []` is how a STRUCT
///    is spelled, and an unstamped ADT cannot be read as an enum at all;
///  * at least one variant, and EVERY variant fieldless — an enum with a payload
///    keeps its payload lanes and its opaque value;
///  * every tag inside `i64` — `VariantDef::discriminant` is the decoded tag, but
///    a `#[repr(u128)]` tag above `i128::MAX` is stored lossily (negative); the
///    `i64` window excludes it and every other width a destination could disagree
///    with;
///  * tags pairwise distinct (the language guarantees it; checked, not assumed —
///    a duplicate would make the bijection false).
fn fieldless_enum_variants(ty: &Ty) -> Option<&[trust_types::VariantDef]> {
    let Ty::Adt { adt_kind: Some(trust_types::AdtKind::Enum), variants, .. } = ty else {
        return None;
    };
    if variants.is_empty()
        || variants.iter().any(|v| {
            !v.fields.is_empty()
                || v.discriminant < i128::from(i64::MIN)
                || v.discriminant > i128::from(i64::MAX)
        })
    {
        return None;
    }
    if variants.len() <= 16 {
        for (i, v) in variants.iter().enumerate() {
            if variants[..i].iter().any(|prev| prev.discriminant == v.discriminant) {
                return None;
            }
        }
    } else {
        let mut seen = FxHashSet::default();
        if !variants.iter().all(|v| seen.insert(v.discriminant)) {
            return None;
        }
    }
    Some(variants.as_slice())
}

pub(crate) fn fieldless_enum_tags(ty: &Ty) -> Option<Vec<i128>> {
    Some(fieldless_enum_variants(ty)?.iter().map(|v| v.discriminant).collect())
}

/// The tag `place = Enum::Variant` defines `place`'s integer model to be, when
/// `place` has a FIELDLESS enum type (see [`fieldless_enum_tags`]). `variant` is
/// the aggregate's variant INDEX; the tag is that variant's decoded discriminant.
/// A variant index outside the declared list declines.
fn fieldless_enum_construction_tag(
    func: &VerifiableFunction,
    place: &trust_types::Place,
    variant: usize,
) -> Option<i128> {
    let ty = crate::place_ty_cow(func, place)?;
    let variants = fieldless_enum_variants(ty.as_ref())?;
    variants.get(variant).map(|v| v.discriminant)
}

/// The value `dest = Discriminant(src)` defines `dest` to be: `src`'s own integer
/// model, when `src` has a FIELDLESS enum type (see [`fieldless_enum_tags`]).
///
/// Gates beyond the type:
///  * `dest` is an integer whose type can hold EVERY declared tag, so the tag the
///    construction arm writes and the value a `SwitchInt` label decodes to
///    (`switch_label_to_formula`, at `dest`'s type) are the same integer;
///  * the payload-read gate of the `Use` arm (hunt-15): a `src` reached through a
///    `Downcast` of a mutably borrowed local declines, because a store through the
///    `&mut` is not tracked as a write of the payload name;
///  * `src` renders as a plain `Int`-sorted variable — the shape a `Use` copy of
///    it would mint. An array-theory element read or any other rendering declines.
fn fieldless_enum_discriminant_read_def(
    func: &VerifiableFunction,
    dest: &trust_types::Place,
    src: &trust_types::Place,
    read_ctx: &ArrayReadCtx<'_>,
) -> Option<Formula> {
    let src_ty = crate::place_ty_cow(func, src)?;
    let variants = fieldless_enum_variants(src_ty.as_ref())?;
    let dest_ty = crate::place_ty_cow(func, dest)?;
    let Ty::Int { width, signed } = dest_ty.as_ref() else {
        return None;
    };
    let (lo, hi): (i128, i128) = match (*width, *signed) {
        (w @ 1..=64, true) => (-(1i128 << (w - 1)), (1i128 << (w - 1)) - 1),
        (w @ 1..=64, false) => (0, (1i128 << w) - 1),
        (128, true) => (i128::MIN, i128::MAX),
        (128, false) => (0, i128::MAX),
        _ => return None,
    };
    if variants.iter().any(|v| v.discriminant < lo || v.discriminant > hi) {
        return None;
    }
    if src.projections.iter().any(|pr| matches!(pr, trust_types::Projection::Downcast(_)))
        && local_is_mutably_borrowed(func, src.local)
    {
        return None;
    }
    let value =
        operand_to_formula_with_array_ctx(func, &Operand::Copy(src.clone()), Some(read_ctx));
    matches!(&value, Formula::Var(_, Sort::Int)).then_some(value)
}

/// Trust (verified-sysroot §5 step 3, slice 2): allocation-root bounds for the
/// provenance-EXPOSE cast `dest = p as usize`. When `p` PROVABLY denotes the
/// address of a model-covered allocation ROOT — `&x` / `&raw x` of a WHOLE
/// local whose sort has a statically known byte size
/// (`trust_types::alloc_model::known_alloc_byte_size`), reached through
/// unique whole-local defs and thin-identity casts only — return the model's
/// two-axiom bound on the minted address
/// (`alloc_model::alloc_root_address_bounds`):
///
/// ```text
/// 1 <= dest  &&  dest <= usize::MAX - size_of(x)
/// ```
///
/// This is the fact that makes the `*mut T::add::precondition_check` overflow
/// legs PROVABLE on covered shapes: `addr + byte_len` cannot wrap when
/// `byte_len <= size_of(x)`. Everything else declines, fail-closed:
///
///   * not the expose cast (wrong source/target sort) — `None`;
///   * `p` reassigned anywhere, or defined by anything but a root borrow /
///     whole-local copy / thin-identity cast (`local_defs::unique_value_def` +
///     the fueled chase) — `None`;
///   * the borrow is PROJECTED (`&x.f`, `&x[i]` — nonzero offset, size of a
///     sub-object) — `None`;
///   * the root's sort is not size-covered (ADT/tuple padding, slice/str,
///     pointer-typed roots) — `None`.
///
/// SOUND: the bounds are per-value theorems of the allocation model (see the
/// axiom discussion on `alloc_root_address_bounds`), so a conjoined fact can
/// only discharge a false-FAIL. No fact ever RELATES two distinct roots, so
/// cross-allocation comparisons stay exactly as unprovable as before.
fn alloc_model_expose_root_bounds_with_ty(
    func: &VerifiableFunction,
    op: &Operand,
    from_ty: Option<&Ty>,
    to_ty: &Ty,
    dest_name: &str,
) -> Option<Formula> {
    let from_ty = from_ty?;
    if !crate::is_thin_pointer_address_expose_cast(from_ty, to_ty) {
        return None;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else {
        return None;
    };
    if !p.projections.is_empty() {
        return None;
    }
    let byte_size = expose_root_alloc_byte_size(func, p.local, 8)?;
    trust_types::alloc_model::alloc_root_address_bounds(
        Formula::Var(dest_name.to_string(), Sort::Int),
        byte_size,
    )
}

/// The chase half of [`alloc_model_expose_root_bounds_with_ty`]: the statically known
/// byte size of the allocation `local` roots at, or `None`. Follows only
/// value-preserving pointer defs (whole-local `Use`, thin-identity `Cast`)
/// down to a `Ref`/`AddressOf` of a WHOLE local; fuel exhaustion fails
/// CLOSED. `local_defs::unique_value_def` already declines any local assigned more
/// than once or through a projection, so the chased value is unambiguous.
fn expose_root_alloc_byte_size(func: &VerifiableFunction, local: usize, fuel: u8) -> Option<u128> {
    let fuel = fuel.checked_sub(1)?;
    if crate::local_defs::is_parameter(func, local) {
        return None;
    }
    match crate::local_defs::unique_value_def(func, local)? {
        Rvalue::Ref { place: root, .. } | Rvalue::AddressOf(_, root) => {
            if !root.projections.is_empty() {
                return None;
            }
            let root_ty = crate::local_ty_ref(func, root.local)?;
            trust_types::alloc_model::known_alloc_byte_size(root_ty)
        }
        Rvalue::Use(Operand::Copy(q) | Operand::Move(q)) if q.projections.is_empty() => {
            expose_root_alloc_byte_size(func, q.local, fuel)
        }
        Rvalue::Cast(Operand::Copy(q) | Operand::Move(q), cast_to) if q.projections.is_empty() => {
            let inner_ty = crate::local_ty_ref(func, q.local)?;
            // Only a thin->thin pointer identity preserves the address value.
            if !crate::is_thin_pointer_identity_cast(inner_ty, cast_to) {
                return None;
            }
            expose_root_alloc_byte_size(func, q.local, fuel)
        }
        _ => None,
    }
}

#[cfg(test)]
fn cast_definition_formula(
    func: &VerifiableFunction,
    dest: &trust_types::Place,
    op: &Operand,
    to_ty: &Ty,
) -> Option<Formula> {
    let from_ty = crate::operand_ty_cow(func, op);
    cast_definition_formula_with_ty(func, dest, op, from_ty.as_deref(), to_ty)
}

fn cast_definition_formula_with_ty(
    func: &VerifiableFunction,
    dest: &trust_types::Place,
    op: &Operand,
    from_ty: Option<&Ty>,
    to_ty: &Ty,
) -> Option<Formula> {
    let from_ty = from_ty?;
    if matches!(from_ty, Ty::Bool) && to_ty.is_integer() {
        return Some(bool_to_int_formula(func, op));
    }

    if crate::is_callable_reification_cast(from_ty, to_ty) {
        return Some(callable_reification_formula(func, dest, to_ty));
    }

    if crate::is_modeled_identity_cast(from_ty, to_ty) {
        return Some(operand_to_formula(func, op));
    }

    // Constant value-preserving int->int cast: `dest = (k as T)` where the OPERAND is a
    // concrete integer constant `k` representable in T equals k EXACTLY (no truncation,
    // no signed/unsigned wrap), so `dest == k` is an unconditional theorem of this
    // statement. Rust lowers a literal shift amount as `_t = (const K_i32 as u32)` — a
    // same-width signed->unsigned reinterpret that `is_modeled_identity_cast` SOUNDLY
    // declines for a symbolic source (negatives wrap) — so without this fact `_t` is a
    // free var and the provably-in-range shift-overflow boundary (`_t < W`) FALSE-refutes
    // a safe constant shift (`x << 16`, `n >> 18`, `high << 4`). We return the VALUE; the
    // caller wraps it in `Eq(dest, value)` like every other branch.
    //
    // SOUND: gated on a CONSTANT operand whose exact value is representable in the
    // destination integer type. A symbolic source, a non-integer dest, or a truncating
    // constant (`300_i32 as u8`, `-5_i32 as u32`) declines and the def is dropped —
    // fail-closed: a missing hypothesis can only cause a false-FAIL, never a false-PROVE.
    if from_ty.is_integer() {
        if let Ty::Int { width, signed } = to_ty {
            let w = *width;
            let k = match op {
                Operand::Constant(ConstValue::Int(v)) => Some(*v),
                Operand::Constant(ConstValue::Uint(v, _)) if *v <= i128::MAX as u128 => {
                    Some(*v as i128)
                }
                _ => None,
            };
            if let Some(k) = k {
                let (to_min, to_max) = if *signed {
                    if w >= 128 {
                        (i128::MIN, i128::MAX)
                    } else {
                        (-(1i128 << (w - 1)), (1i128 << (w - 1)) - 1)
                    }
                } else if w < 128 {
                    (0i128, (1i128 << w) - 1)
                } else {
                    (0i128, i128::MAX)
                };
                if k >= to_min && k <= to_max {
                    return Some(Formula::Int(k));
                }
            }
        }
    }

    // Trust: enum-disc-index cast `_d = (e_disc as usize)` — re-emit the dropped
    // `index == disc-cast` equality. When the source is the `Discriminant` read of a
    // layout-`disc_index_safe` enum, the destination integer is at least as wide as the
    // repr, and EVERY declared discriminant is representable unchanged in the
    // DESTINATION type (`0 <= tag <= MAX(dest)`), the cast is VALUE-PRESERVING on every
    // value the read can produce, so `_d == e_disc` is an unconditional theorem of this
    // statement (the index IS the disc cast). Mirrors the `-full` native bridge's
    // GATE-NONNEG. Without it the index `e as usize` is a free var and `arr[e as usize]`
    // over a `[T; len > max_disc]` false-FAILs (proved/enumdf_i8_nonneg).
    //
    // SOUND, on both ends of the tag set:
    // * `min_disc >= 0` — a negative-disc enum (where `e as usize` reinterprets the sign
    //   bit) declines here and falls to the signed->unsigned relation below.
    // * `max_disc <= MAX(dest)` (CAST-ENUMDISC-SIGNED-1) — the DESTINATION's signedness
    //   matters, not only its width. A same-width unsigned->signed cast reinterprets the
    //   top bit: `#[repr(u8)] enum F { A = 200, B = 1 }` gives `F::A as i8 == -56`.
    //   Width alone admitted it, and `_0 == _2` beside `_2 == 200`, value_facts' true
    //   tag image `_0 == -56` and `_0 <= 127` was a CONTRADICTION that removed the
    //   `F::A` path — `ensures result >= 0` and `x >> ((e as i8) as u32)` were
    //   kernel-certified on a binary that returns -56 and panics. A wider signed
    //   destination (`e as i16`), any unsigned one at least as wide, and a tag set below
    //   `2^(w-1)` (`{100, 1} as i8`) still pass; a declined cast returns `None` (the
    //   source is unsigned, so the signed->unsigned arm below does not apply), and the
    //   tag-image fact in value_facts stays the only description of the value.
    //
    // GATE-NONNEG DEPENDS ON THE DECODED TAG. `VariantDef::discriminant` is the TRUE
    // signed tag (decoded at the extraction boundary, `trust_mir_extract::ty_convert`'s
    // `decode_discr_tag`). While it was the RAW `Discr::val` bit pattern this gate could
    // NEVER decline: a sub-128-bit raw pattern is never negative, so `#[repr(i8)] A = -1`
    // presented as `min_disc == 2` (over `{255, 2}`) and passed. It did no harm only
    // because the tag FACTS were raw too — the OOB witness `_3 = 255` stayed reachable —
    // an accidental cancellation, not a gate. With the tags decoded the gate does what
    // this comment always claimed: `{-1, 2}` has `min_disc == -1` and declines, and
    // `t[e as usize]` / `t[a.cmp(&b) as usize]` refute on a real witness.
    //
    // Trust (2026-09-30, round 10 of the callee-summary review): AND every declared
    // discriminant must fit the DESTINATION. "At least as wide" is not "value
    // preserving" when the destination is signed: `#[repr(u64)] enum { A = u64::MAX,
    // B = 1 }` read `as i64` is -1 for `A`, and `#[repr(u8)] A = 255` read `as i8` is
    // -1 too. The equality said 2^64 - 1 and 255, and `t[(e as i64 + 51) as usize]`
    // style indexes proved, certified, and went out of bounds.
    let to_max = match to_ty {
        Ty::Int { width, signed: true } if *width < 128 => (1i128 << (width - 1)) - 1,
        Ty::Int { width, signed: false } if *width < 127 => (1i128 << width) - 1,
        _ => i128::MAX,
    };
    if let (Some(from_w), Ty::Int { width: to_w, signed: to_signed }) = (from_ty.int_width(), to_ty)
        && *to_w >= from_w
        && let Operand::Copy(p) | Operand::Move(p) = op
        && p.projections.is_empty()
        && !crate::local_defs::is_parameter(func, p.local)
        && let Some(Rvalue::Discriminant(disc_place)) =
            crate::local_defs::unique_value_def(func, p.local)
        && let Some(enum_ty) = crate::place_ty_cow(func, disc_place)
        && let Ty::Adt { variants, disc_index_safe: true, .. } = enum_ty.as_ref()
        && !variants.is_empty()
        && variants
            .iter()
            .map(|v| normalize_raw_discriminant(v.discriminant, from_w, from_ty.is_signed()))
            .all(|d| {
                (0..=to_max).contains(&d) && nonneg_tag_survives_int_cast(d, *to_w, *to_signed)
            })
    {
        // Caller wraps this in `Eq(Var(dest), value)`, i.e. `_d == e_disc`.
        return Some(operand_to_formula(func, op));
    }

    // Trust: a NON-NARROWING signed->unsigned `as` cast (`i32 as u64`, `i32 as u32`,
    // `isize as usize`) — the exact two's-complement value relation.
    //
    // Every other helper on this path declines this cast, each for its own sound
    // reason: `is_modeled_identity_cast` refuses (a negative source does not survive
    // as identity), `widening_cast_result_range` refuses (`*ss && !ds`), and
    // `narrowing_cast_result_range` refuses a strict widening (`*dw > *sw`). The
    // CONJUNCTION of those declines emitted NOTHING relating the destination to the
    // source, leaving it constrained only by its own type range — so a dominating
    // `if x < 0 || x >= 16 { return 0; }` guard bounds the SOURCE while the solver is
    // still free to pick any `usize` for the RESULT, and `a[x as usize]` refutes on a
    // model no execution can produce.
    //
    // Rust's `as` here sign-extends to the destination width and reinterprets, so the
    // result is the source's residue mod `2^to_w`. For `to_w >= from_w` the source
    // range `[-2^(from_w-1), 2^(from_w-1)-1]` sits strictly inside `(-2^to_w, 2^to_w)`,
    // so the residue takes exactly two forms and the relation is the total function
    //   `dest == if src >= 0 { src } else { src + 2^to_w }`
    // — a value-level identity of this statement for EVERY input, not a claim about
    // any guard. `value_facts::truncate_nonneg_tag_as_int` constant-folds the same
    // `as` semantics for the enum-discriminant tag sets.
    //
    // GATED on `to_w >= from_w`. A NARROWING signed->unsigned cast (`i32 as u8`) is a
    // truncation whose residue needs many representatives, and either branch above
    // would be FALSE for a source outside `[0, 2^to_w)`: conjoined with the
    // destination's own `[0, 2^to_w-1]` range (which `narrowing_cast_result_range`
    // does emit) the hypotheses would be CONTRADICTORY for exactly those sources, and
    // a contradiction proves everything — including the out-of-bounds
    // `a[(x as u8) as usize]`. Narrowing therefore gets no unconditional relation here.
    // Trust (2026-10-11, VC-NARROW-CAST-FALSE-REFUTE-1): it is not left with the
    // target range ALONE any more, which made the result a free target value and
    // refuted `arr[x as u8 as usize]` under `x < 0x80`: the Cast arm also emits
    // `narrowing_cast_in_range_identity`, `(to_min <= src <= to_max) => dest == src`.
    // That implication is vacuous for exactly the sources this note is about (those
    // outside the target), so it cannot form the contradiction described above; on
    // the sources inside the target it is the definition of `as`. `to_w == 128` is
    // likewise declined here: `2^128` is not representable as a
    // `Formula::Int`/`UInt` literal, and a wrong modulus is worse than none.
    if let (Ty::Int { width: from_w, signed: true }, Ty::Int { width: to_w, signed: false }) =
        (from_ty, to_ty)
        && *to_w >= *from_w
        && let Some(modulus) = power_of_two_i128(*to_w)
    {
        let src = operand_to_formula(func, op);
        // Caller wraps this in `Eq(Var(dest), value)`.
        return Some(Formula::Ite(
            Box::new(Formula::Ge(Box::new(src.clone()), Box::new(Formula::Int(0)))),
            Box::new(src.clone()),
            Box::new(Formula::Add(Box::new(src), Box::new(Formula::Int(modulus)))),
        ));
    }

    None
}

/// Reinterpret the extractor's RAW discriminant bit pattern (stored non-negative in an
/// `i128`: `-1` in `repr(i8)` arrives as `255`, `-5` in `repr(i16)` as `65531`) as its
/// TRUE signed value, per the discriminant's own repr type. For an unsigned repr the
/// raw pattern already IS the value.
///
/// Mirror of the native bridge's `normalize_disc` / `sign_extend_raw_value`
/// (`crates/trust-ir-bridge/src/lower.rs`). REQUIRED before any ORDER comparison on a
/// declared discriminant — comparing the raw pattern makes a negative-discriminant enum
/// look non-negative and opens a false proof (see the GATE-NONNEG note above). Equality
/// comparisons against a tag variable that itself carries the raw pattern are unaffected
/// and must NOT be normalized.
///
/// Fail-safe on degenerate widths: a `0` or `>= 128` width returns the pattern unchanged
/// rather than shifting out of range (`width` here comes from `Ty::int_width()`, which
/// yields 8/16/32/64/128, so those arms are defensive).
pub(crate) fn normalize_raw_discriminant(pattern: i128, width: u32, signed: bool) -> i128 {
    if !signed || width == 0 || width >= 128 {
        return pattern;
    }
    let mask = (1u128 << width) - 1;
    let value = (pattern as u128) & mask;
    let sign_bit = 1u128 << (width - 1);
    if value & sign_bit == 0 { value as i128 } else { (value as i128) - (1i128 << width) }
}

/// Does `tag as Int { width, signed }` leave the (decoded) enum tag `tag` UNCHANGED?
/// True exactly when `0 <= tag <= MAX(width, signed)` — the value-preservation
/// condition the enum-disc-index identity arm of `cast_definition_formula` needs
/// (CAST-ENUMDISC-SIGNED-1). A non-negative `tag` survives an `as` cast iff it is
/// below `2^value_bits`, where a signed destination spends one bit on the sign; so
/// `200 as i8` (value bits 7, `200 >= 128`) does NOT survive while `200 as i16` and
/// `200 as u8` do. Equivalent, for `tag >= 0`, to
/// `value_facts::truncate_nonneg_tag_as_int(tag, width, signed) == tag`.
///
/// Fail-closed: a negative tag (a signed repr below zero, or a `repr(u128)` tag above
/// `i128::MAX` that arrived as its lossy `as i128` pattern) and a width outside
/// `1..=128` answer `false`. Every non-negative `i128` is below `2^127`, so a
/// destination with 127 or more value bits (`i128`, `u128`) holds every such tag.
fn nonneg_tag_survives_int_cast(tag: i128, width: u32, signed: bool) -> bool {
    if tag < 0 || width == 0 || width > 128 {
        return false;
    }
    let value_bits = if signed { width - 1 } else { width };
    value_bits >= 127 || (tag as u128) < (1u128 << value_bits)
}

/// `2^exp` as an `i128`, or `None` when it does not fit.
///
/// `1i128 << 127` evaluates to `i128::MIN`, not `2^127`, so the shift has to be
/// range-checked rather than trusted; a caller that needs a modulus DECLINES on
/// `None` instead of asserting a wrong one.
fn power_of_two_i128(exp: u32) -> Option<i128> {
    (exp < 127).then(|| 1i128 << exp)
}

fn callable_reification_formula(
    func: &VerifiableFunction,
    dest: &trust_types::Place,
    to_ty: &Ty,
) -> Formula {
    let dest_name = crate::place_to_var_name(func, dest);
    let sort = crate::place_sort(func, dest).unwrap_or_else(|| crate::sort_for_ty(to_ty));
    crate::callable_reification_token(&dest_name, sort)
}

/// A widening integer cast result is bounded by the *source* type's
/// range. Zero-/sign-extension preserves the value, so `(x as u64)` for `x: u32`
/// lies in `[0, 2^32-1]` however wide the destination is. `extract_block_definitions`
/// already emits `dest == source`, but that only bounds `dest` when the *source*
/// variable is itself range-constrained (e.g. a u32 parameter, via `infer_from_types`).
/// When the source is a #51-extracted struct-payload field — `(p.x as u64)` over a
/// moved enum-variant payload — nothing else constrains it, so the widened value
/// reads as a free u64 and a genuinely safe `(p.x as u64) + (p.y as u64)` false-FAILs.
/// Emitting the source-width range on the cast result restores the bound at its origin.
///
/// Soundness: the returned range is an unconditional truth about the cast, so it can
/// only ever help discharge a real obligation — never manufacture a false-PROVE.
/// It is gated to value-preserving widenings:
///   * unsigned source → any strictly wider integer: result ∈ [0, 2^sw-1];
///   * signed source → strictly wider *signed*:       result ∈ [-2^(sw-1), 2^(sw-1)-1].
/// Signed→unsigned is skipped (a negative source wraps to a huge unsigned value, so the
/// source-width range would be *false*). Same-or-narrowing casts are skipped
/// (reinterpretation/truncation, not value-preserving; narrowing is covered by the
/// CastOverflow VC).
fn widening_cast_result_range_with_ty(
    src_ty: Option<&Ty>,
    to_ty: &Ty,
    dest_name: &str,
) -> Option<Formula> {
    // A `bool as <int>` cast is a value-preserving widening into {0,1}: the
    // boolean's runtime value is exactly 0 or 1, so the widened result lies in
    // [0, 1] for EVERY integer destination (any width, signed or unsigned — 0
    // and 1 fit `i8` as readily as `u64`). Model the source as an unsigned
    // width-1 value and emit that range. Without this a hardened panic_boundary
    // over a bool-sum (`(a != b) as u32 + …`, a3d-kernel `face_active_edge_count`)
    // leaves the cast operand unconstrained and the provably-safe add
    // OVER-REFUTES — the same {0,1} gap the per-statement arithmetic-safety lane
    // and trust-mc's typed-CHC cast encoding already close, here in the hardened
    // operand-range lane. Sound: {0,1} is the EXACT image of a bool cast, so this
    // is an unconditional true conjunct (monotone — only discharges a false-FAIL,
    // never manufactures a false-PROVE; a genuine non-bool overflow still refutes).
    if matches!(src_ty, Some(Ty::Bool)) {
        if !matches!(to_ty, Ty::Int { .. }) {
            return None;
        }
        return Some(crate::range::input_range_constraint(
            &Formula::Var(dest_name.to_string(), Sort::Int),
            1,
            false,
        ));
    }
    let Some(Ty::Int { width: sw, signed: ss }) = src_ty else {
        return None;
    };
    let Ty::Int { width: dw, signed: ds } = to_ty else {
        return None;
    };
    // Strict widening only, and only value-preserving signedness transitions.
    if *dw <= *sw || (*ss && !ds) {
        return None;
    }
    Some(crate::range::input_range_constraint(
        &Formula::Var(dest_name.to_string(), Sort::Int),
        *sw,
        *ss,
    ))
}

/// Trust (drop-in cast type-tracking, decision 2026-07-06): a NARROWING or
/// signedness-REINTERPRETING integer `as` cast is DEFINED in Rust (it truncates /
/// reinterprets the bit pattern, never UB), so it carries NO `CastOverflow`
/// obligation (see `generate::v2_build_cast_vc`) — Trust does not restrict the
/// programmer. To keep downstream reasoning sound AND precise we instead TYPE-TRACK
/// the result: the cast dest holds a value of the TARGET type, so it lies in the
/// target-type range `type_min(to_ty) <= dest <= type_max(to_ty)`. This is an
/// unconditional truth about the wrapped value (monotone — a conjoined true fact can
/// only discharge a false-FAIL, never manufacture a false-PROVE), and it is exactly
/// what lets `(x as u8) as u32 + 1` prove (result <= 255) while a genuinely OOB
/// `arr[(x as u8) as usize]` over a len-8 array is still CAUGHT (the index can reach
/// 255). Complements [`widening_cast_result_range_with_ty`], which carries the tighter
/// SOURCE-width range for value-preserving widenings; this fires for exactly the
/// int->int casts widening does NOT cover (narrowing `dw <= sw`, or a value-changing
/// signed->unsigned reinterpret), so each cast contributes one range fact.
fn narrowing_cast_result_range_with_ty(
    src_ty: Option<&Ty>,
    to_ty: &Ty,
    dest_name: &str,
) -> Option<Formula> {
    let Some(Ty::Int { width: sw, signed: _ }) = src_ty else {
        return None;
    };
    let Ty::Int { width: dw, signed: ds } = to_ty else {
        return None;
    };
    // Fire for NARROWING (`dw < sw`) and SAME-WIDTH signedness reinterprets
    // (`dw == sw`): the result is a genuine value of the target type whose range
    // meaningfully constrains it (`u32 as u8` -> [0,255]). A strictly-WIDENING cast
    // is left to `widening_cast_result_range_with_ty` (value-preserving widenings keep their
    // tighter source-width range; a signed->unsigned widening's only sound bound is
    // the trivially-true target range, so it stays free as before).
    if *dw > *sw {
        return None;
    }
    Some(crate::range::input_range_constraint(
        &Formula::Var(dest_name.to_string(), Sort::Int),
        *dw,
        *ds,
    ))
}

/// Trust (2026-10-01, ordsweep2 enums/c03): the companion VALUE fact of
/// [`narrowing_cast_result_range_with_ty`]. A narrowing or reinterpreting integer `as` cast
/// keeps the value whenever it fits the target type (truncation drops only bits a
/// fitting value does not have), so `src < MIN(target) ∨ src > MAX(target) ∨
/// dest == src`. True of every execution, so monotone. `'0'..='9' => c as u8 - b'0'`
/// (a `char`, lowered as `u32`) was refuted with `c as u8 = 0` under `c = '0'`.
/// Fires for exactly the casts the range fact covers.
fn narrowing_cast_value_fact_with_ty(
    func: &VerifiableFunction,
    op: &Operand,
    src_ty: Option<&Ty>,
    to_ty: &Ty,
    dest_name: &str,
) -> Option<Formula> {
    let Some(Ty::Int { width: sw, signed: _ }) = src_ty else { return None };
    let Ty::Int { width: dw, signed: ds } = to_ty else { return None };
    if *dw > *sw {
        return None;
    }
    let src = crate::operand_to_formula(func, op);
    Some(Formula::Or(vec![
        Formula::Lt(Box::new(src.clone()), Box::new(crate::range::type_min_formula(*dw, *ds))),
        Formula::Gt(Box::new(src.clone()), Box::new(crate::range::type_max_formula(*dw, *ds))),
        Formula::Eq(Box::new(Formula::Var(dest_name.to_string(), Sort::Int)), Box::new(src)),
    ]))
}

/// Trust (2026-10-11, VC-NARROW-CAST-FALSE-REFUTE-1): the VALUE relation of a strictly
/// NARROWING integer `as` cast (and of a same-width unsigned->signed reinterpret) on the
/// sources it does not change:
///
///   `(to_min <= src && src <= to_max) => dest == src`
///
/// (for an unsigned source, `src <= to_max => dest == src`; see THE ANTECEDENT'S SHAPE).
///
/// THE DEFECT. [`narrowing_cast_result_range_with_ty`] bounds the result by its TARGET type, and
/// [`cast_definition_formula_with_ty`] declines every symbolic narrowing cast (an unconditional
/// `dest == src` is false for a source outside the target, and beside that range it would
/// be a contradiction). Nothing else tied `dest` to `src`, so the result was a FREE value
/// of the target type: `TABLE[c as u8 as usize]` under `c.is_ascii()` (a `char` is a
/// `u32` here) and `arr[x as u8 as usize]` under `x < 0x80`, over `[0u8; 0x80]`, were
/// refuted at `dest = 128` and published `[bounds] FAILED (trust-full-verifier);
/// counterexample: verified_counterexample = true`; `(x as u8) + 0x7f` and `1u32 << (x
/// as u8)` under the same kind of guard were `[overflow:add]` / `[shift:left] FAILED`.
/// Measured on the stage 1 of `1213387e6d` (`tests/ui/trust/
/// narrowing_cast_in_range_identity.rs`).
///
/// SOUND, for every integer type pair. Rust's `as` between integer types returns the
/// source value unchanged whenever that value is representable in the target type;
/// truncation and sign reinterpretation only move values outside it. So on every
/// execution with `to_min <= src <= to_max` the result IS `src`. Outside that range the
/// implication is vacuous and claims nothing, so it can never contradict the target-type
/// range (the contradiction the narrowing note in [`cast_definition_formula_with_ty`] declines
/// the unconditional relation for). Like [`variable_shl_result_range`]'s implication it
/// is entailed by the operation's definition: it prunes no model the cast admits. `src`
/// is the operand spelled exactly as that function spells the widening identity
/// (`operand_to_formula`), i.e. its value AT the cast statement: the block's staleness
/// kill and the path-definition transport key on the fact's free variables, so a later
/// write of `src` or `dest` drops it like any other def that mentions them (an `Implies`
/// has no `Eq` lhs, so the versioned path's subject-pin exemption never reaches it).
///
/// CORRECTED 2026-10-12 (UNION-SIBLING-WRITE-1, the wave-24 review): "a later write of
/// `src` or `dest`" did not include a write of a UNION SIBLING. With `union V { a: u8,
/// b: i8 }`, `u.a = x as u8; u.b = -56; if x < 0x80 { u.a + 0x7f }` kept this fact on
/// `u.0` across the write of `u.1` (the place names take sibling fields for disjoint
/// storage), the `overflow:add` row was kernel-certified on the stage 1 of `51eac007f3`,
/// and the advisory lane elided its check. Every write oracle now adds the union value's
/// own name to a union field write (`path_defs::union_write_cover_name`), which rebinds
/// the siblings; the widening cast's `dest == src` had the same staleness before this
/// function existed.
///
/// THE ANTECEDENT'S SHAPE. For an UNSIGNED source the lower bound is dropped:
/// `src <= to_max => dest == src`. On every execution `src >= 0 >= to_min`, so this is
/// the same fact, and a single `Le` atom is the antecedent `trust-certify`'s modus-ponens
/// normalization (`discharge_entailed_implications`) discharges, as it does the
/// `Implies(Ge(src, 0), Eq(dest, src))` the signed->unsigned `ite` lifts to; with both
/// bounds no unsigned row was kernel-certified (measured on the real MIR of
/// `tests/narrowing_cast_identity_realmir.rs`). A SIGNED source needs both bounds, and
/// that two-atom antecedent proves by SMT but is not kernel-certified today (KNOWN_HAZARDS
/// VC-NARROW-CAST-FALSE-REFUTE-1).
///
/// SCOPE. Source and target both `Ty::Int` (the two cast ranges' own gate). Strictly
/// narrowing (`dw < sw`), or a same-width UNSIGNED->SIGNED reinterpret (`u32 as i32`).
/// Not a same-width signed->unsigned cast: [`cast_definition_formula_with_ty`] emits its exact
/// `ite(src >= 0, src, src + 2^w)`. Not a widening cast, which is value-preserving and
/// has its own identity and range. Not a constant source: the constant arm of
/// [`cast_definition_formula_with_ty`] is exact. Declines when a target bound is not a
/// `Formula::Int` (only `u128::MAX`, which no narrowing target reaches).
///
/// NOT CLOSED: a truncation that WRAPS an out-of-range source back into the target's
/// low values (`x` in `[0x100, 0x17f]`, `arr[x as u8 as usize]` over `[0u8; 0x80]`)
/// still reads a free target value there and is still falsely refuted; an exact
/// `src mod 2^w` for unsigned sources would close it (KNOWN_HAZARDS
/// VC-NARROW-CAST-FALSE-REFUTE-1).
fn narrowing_cast_in_range_identity_with_ty(
    func: &VerifiableFunction,
    op: &Operand,
    src_ty: Option<&Ty>,
    to_ty: &Ty,
    dest_name: &str,
) -> Option<Formula> {
    if matches!(op, Operand::Constant(_)) {
        return None;
    }
    let Some(Ty::Int { width: sw, signed: ss }) = src_ty else {
        return None;
    };
    let Ty::Int { width: dw, signed: ds } = to_ty else {
        return None;
    };
    let strictly_narrowing = *dw < *sw;
    let unsigned_to_signed_reinterpret = *dw == *sw && !*ss && *ds;
    if !(strictly_narrowing || unsigned_to_signed_reinterpret) || *dw == 0 || *dw > 128 {
        return None;
    }
    let (to_min, to_max) = if *ds {
        (crate::range::signed_min(*dw), crate::range::signed_max(*dw))
    } else {
        (0, i128::try_from(crate::range::unsigned_max(*dw)).ok()?)
    };
    let src = operand_to_formula(func, op);
    let upper = Formula::Le(Box::new(src.clone()), Box::new(Formula::Int(to_max)));
    // An unsigned source is `>= 0 >= to_min` on every execution: its lower bound is
    // the source type's own fact, and a lone `Le` is the kernel-certifiable shape.
    let antecedent = if *ss {
        Formula::And(vec![
            Formula::Ge(Box::new(src.clone()), Box::new(Formula::Int(to_min))),
            upper,
        ])
    } else {
        upper
    };
    Some(Formula::Implies(
        Box::new(antecedent),
        Box::new(Formula::Eq(
            Box::new(Formula::Var(dest_name.to_string(), Sort::Int)),
            Box::new(src),
        )),
    ))
}

/// An unsigned right-shift by a constant `k` bounds its result above by
/// `(2^w - 1) >> k`, where `w` is the operand's width. This is a value-preserving
/// truth: the shifted operand is a width-`w` unsigned value, so `x <= 2^w-1` implies
/// `x >> k <= (2^w-1) >> k`. Like the #52 widening-cast range, it restores a bound the
/// integer model otherwise loses when the shifted operand is itself unconstrained — a
/// moved enum-variant payload field, or a widened value. `(x >> 1) + 1` then false-FAILs
/// because `x >> 1` reads as a free integer with no upper bound; emitting the
/// width-derived bound on the result discharges it.
///
/// Soundness: the bound is an unconditional truth about every real execution, so as a
/// conjoined hypothesis it can only turn a false-FAIL into a PROVE, never an overflow
/// into a false-PROVE (monotonicity — adding a true fact only shrinks the model). It is
/// gated tightly:
///   * `Shr` only — `Shl` can overflow, so its result has no tautological sub-type-max bound;
///   * unsigned operand only — a signed `>>` sign-extends, a different (still-bounded but
///     two-sided) range we do not model here (since corrected: the signed `Shr` arm of
///     `shift_result_range` now emits that two-sided range — see `soundness-signed-shift`);
///   * constant shift only — an UNCONDITIONAL bound on a variable shift is just the type
///     max (`k` could be 0), which is useless; and `k >= w` is a checked shift-overflow
///     (the op may panic and never produce a value), so we must not pre-bound it.
///     `variable_shl_result_range` reaches the variable-amount case a different way — as an
///     IMPLICATION whose antecedent bounds `k` — which is why it escapes this argument
///     rather than contradicting it.
/// The largest value the shift's LHS can hold, when that is structurally bounded BELOW the
/// shift type's max: a widening cast `(x as W)` of an UNSIGNED `ELEM` is `<= MAX(ELEM)`
/// (`2^width(ELEM) - 1`), and a non-negative integer constant bounds itself. None when the LHS
/// is an unconstrained value of the full shift type (no tighter bound than the type max).
fn shift_lhs_unsigned_max(func: &VerifiableFunction, lhs: &Operand) -> Option<u128> {
    match lhs {
        Operand::Constant(ConstValue::Uint(v, _)) => Some(*v),
        Operand::Constant(ConstValue::Int(v)) if *v >= 0 => Some(*v as u128),
        Operand::Copy(p) | Operand::Move(p)
            if p.projections.is_empty() && !crate::local_defs::is_parameter(func, p.local) =>
        {
            let Rvalue::Cast(src, _) = crate::local_defs::unique_value_def(func, p.local)? else {
                return None;
            };
            let src_ty = crate::operand_ty_cow(func, src)?;
            let Ty::Int { width: ew, signed: false } = src_ty.as_ref() else {
                return None;
            };
            Some(crate::range::unsigned_max(*ew))
        }
        _ => None,
    }
}

/// An UNSIGNED floor-division is bounded by its own dividend: `x >> k` is
/// `floor(x / 2^k)` and `x / c` is `floor(x / c)`, and `floor(x / d) <= x` holds for
/// every unsigned `x` and every divisor `d >= 1`.
///
/// This is the RELATIONAL companion to `shift_result_range`, which bounds the
/// result only by the CONSTANT `MAX(W) >> k`. That constant bound is useless for
/// the safe-midpoint idiom, the canonical unsigned-shift consumer:
///
/// ```ignore (illustrative)
/// if low <= high { low + ((high - low) >> 1) }   // can this Add overflow?
/// ```
///
/// From `h <= MAX>>1` and `low <= MAX` nothing follows — `low` could be `MAX`.
/// From `h <= d` and `d == high - low` we get `low + h <= low + d == high <= MAX`,
/// and the Add discharges. Emitting BOTH facts is what makes the idiom provable.
///
/// SOUNDNESS: unsigned `>>` bridges to the integer domain through the unsigned
/// `bv2nat` (`BvToInt signed=false`), so `dest` and `lhs` inhabit the same
/// nonnegative value-space and `floor(x / 2^k) <= x` is an unconditional truth
/// there — for a constant OR a variable shift amount, and even when the amount is
/// out of range (a masked `x >> (k mod w)` is still `<= x`; the out-of-range case
/// is separately caught by the `ShiftOverflow` VC). Monotone-safe: adding a true
/// fact can only turn a false-FAIL into a PROVE, never an overflow into a
/// false-PROVE.
///
/// SIGNED shifts are EXCLUDED and must stay excluded: arithmetic `>>` rounds
/// toward -inf, so `-8 >> 1 == -4`, and `-4 <= -8` is FALSE. Emitting this fact
/// for a signed shift would be unsound.
#[cfg(test)]
fn unsigned_floor_div_le_lhs(
    func: &VerifiableFunction,
    op: &BinOp,
    lhs: &Operand,
    rhs: &Operand,
    dest_name: &str,
    lhs_formula: Formula,
) -> Option<Formula> {
    let lhs_ty = crate::operand_ty_cow(func, lhs);
    unsigned_floor_div_le_lhs_with(lhs_ty.as_deref(), op, rhs, dest_name, || lhs_formula)
}

fn unsigned_floor_div_le_lhs_with(
    lhs_ty: Option<&Ty>,
    op: &BinOp,
    rhs: &Operand,
    dest_name: &str,
    lhs_formula: impl FnOnce() -> Formula,
) -> Option<Formula> {
    // Both spellings of the idiom reduce to `floor(x / d) <= x` for some `d >= 1`:
    // `x >> k` is `floor(x / 2^k)`, and `x / c` is `floor(x / c)` directly. Cover
    // both, or the fix would discharge `low + ((high - low) >> 1)` while leaving the
    // equivalent `low + (high - low) / 2` unprovable.
    match op {
        // The shift AMOUNT needs no constraint: `floor(x / 2^k) <= x` for every k.
        BinOp::Shr => {}
        // The DIVISOR must be a constant `>= 1`. A zero divisor leaves the quotient
        // unconstrained in the model (its panic is carried by the separate
        // divide-by-zero VC), and a variable divisor could be zero.
        BinOp::Div => {
            let c = match rhs {
                Operand::Constant(ConstValue::Uint(v, _)) => *v,
                Operand::Constant(ConstValue::Int(v)) if *v >= 0 => *v as u128,
                _ => return None,
            };
            if c < 1 {
                return None;
            }
        }
        _ => return None,
    }
    // Unsigned integers only — see the SIGNED note above.
    if !matches!(lhs_ty, Some(Ty::Int { signed: false, .. })) {
        return None;
    }
    let lhs_formula = lhs_formula();
    // `x = x >> k` in a non-renamed frame would render as the vacuous `x <= x`.
    if matches!(&lhs_formula, Formula::Var(name, Sort::Int) if name == dest_name) {
        return None;
    }
    let dest = Formula::Var(dest_name.to_string(), Sort::Int);
    Some(Formula::Le(Box::new(dest), Box::new(lhs_formula)))
}

/// The true result type of a SHIFT whose shifted value is a **width-less signed
/// constant**, recovered from the assignment DESTINATION.
///
/// `ConstValue::Int` carries no width, so `operand_ty` must infer one from the
/// value: it returns `i64` for anything that fits `i64` (`lib.rs`, and the widening
/// to 128 there only fires for values OUTSIDE `i64`). For `1i128 << k` that
/// fabricates width **64**, and the shift definition
/// `extract_block_definitions` then emits is `bv2int_signed(bvshl(int2bv(1,64),
/// int2bv(k,64), 64))` — which is FALSE of the real program the moment `k >= 63`
/// (Rust computes `1i128 << 63 == 2^63`; the 64-bit model says `-2^63`). A false
/// hypothesis is a latent vacuity, and it is also what pins the companion
/// `variable_shl_result_range` to a useless `k <= 62` window when the program's own
/// guard gives `k <= 126`.
///
/// The destination of `dst = Shl(lhs, rhs)` has EXACTLY the shift's result type,
/// which in Rust is the shifted value's type — so this is the exact width, not an
/// estimate in either direction. Same recovery, and the same soundness argument, as
/// `generate::checked_vcs::v2_shift_dest_width` (round-19), which already applies it
/// to the `ShiftOverflow` VC; this brings the block DEFINITION into agreement with
/// it.
///
/// Deliberately narrow: it fires ONLY for `ConstValue::Int`, the one operand form
/// whose width is fabricated. Every other shifted value (a local, a
/// width-carrying `ConstValue::Uint`, an `OpaqueScalar`) already reports its real
/// type, and overriding that with the destination's would be a change of meaning
/// rather than a repair.
fn shift_result_ty_from_dest(
    func: &VerifiableFunction,
    place: &trust_types::Place,
    op: &BinOp,
    lhs: &Operand,
) -> Option<Ty> {
    if !matches!(op, BinOp::Shl | BinOp::Shr) {
        return None;
    }
    if !matches!(lhs, Operand::Constant(ConstValue::Int(_))) {
        return None;
    }
    if !place.projections.is_empty() {
        return None;
    }
    let dest_ty = &func.body.locals.get(place.local)?.ty;
    // A shifted SIGNED literal has a signed result type. If the destination reads
    // otherwise the two do not describe the same operation — decline rather than
    // reinterpret.
    match dest_ty {
        Ty::Int { width, signed: true } => Some(Ty::Int { width: *width, signed: true }),
        _ => None,
    }
}

/// The shift AMOUNT as a plain non-negative constant, if it is one. `None` for a
/// variable amount and for a negative literal (Rust panics on a negative shift
/// amount, so no value is produced and no bound may be pre-committed).
fn const_shift_amount(rhs: &Operand) -> Option<u128> {
    match rhs {
        Operand::Constant(ConstValue::Uint(v, _)) => Some(*v),
        Operand::Constant(ConstValue::Int(v)) if *v >= 0 => Some(*v as u128),
        _ => None,
    }
}

/// A LEFT shift of a non-negative integer CONSTANT by a **variable** amount —
/// `1i128 << width`, the type-extremum idiom — emitted no result range at all
/// before this, so the consuming `- 1` / unary `-` had nothing to discharge
/// against and trust-mc REFUTED them: with `dest` unconstrained the model is free
/// to pick the amount that makes `1i128 << k` equal `i128::MIN`, and then `x - 1`
/// really does underflow and `-x` really does overflow.
///
/// A sound range DOES exist, and it is **conditional on the amount**:
///
/// ```text
/// (0 <= k  AND  k <= K)  ==>  (c <= dest  AND  dest <= c << K)
/// ```
///
/// `K` is the largest amount for which `c << K` provably stays at or below the
/// shift type's own maximum — `2^w - 1` unsigned, `2^(w-1) - 1` signed, i.e. the
/// sign bit stays CLEAR. It is stated as an IMPLICATION because that is the honest
/// form: **nothing here bounds `k`**, and an unconditional range would be a false
/// PROVE. The bound becomes available exactly when the surrounding program bounds
/// `k` — for `trust_semantics::signed_min` the enclosing
/// `else if width >= 1 && width <= 127` guard makes `k = width - 1 <= 126 = K` a
/// path fact the solver already holds.
///
/// # What the caller may rely on
///
/// This bounds the shift's **result value**, and only inside the antecedent. It is
/// NOT a claim that the shift is overflow-free, and it does not discharge the
/// `ShiftOverflow` VC (`k < w`), which stays a separate obligation: `K <= w - 1`
/// means a satisfied antecedent implies an in-range amount, but a FALSE antecedent
/// says nothing at all, so the two never trade places.
///
/// # Soundness
///
/// The fact is **entailed by the shift's own definition**, not asserted alongside
/// it, so it cannot prune a model the definition admits — it only puts the
/// consequence in reach of a solver that will not reason through `bvshl`. Under
/// `0 <= k <= K <= w - 1`: `IntToBv(k, w)` is exactly `k`, so `BvShl` shifts by
/// exactly `k`; `c * 2^k <= c * 2^K <= MAX` means no bit is shifted out and (signed)
/// the sign bit stays clear; so the bridge back — `bv2nat` for unsigned,
/// `bv2int_signed` for signed (`chc.rs`, `try_binop_to_formula`) — reads exactly
/// `c * 2^k`, which lies in `[c, c << K]` because `1 <= 2^k <= 2^K`.
///
/// Outside the antecedent nothing is claimed, and that is precisely what keeps it
/// sound where an unconditional range would not be:
///
/// * `k == w - 1` on a SIGNED type sets the sign bit — `1i128 << 127` **is**
///   `i128::MIN` — and there `K == w - 2`, so the antecedent is false and no bound
///   is offered. This is the case a wrong range would turn into a false PROVE of
///   the consuming `-x` / `x - 1`; it is the negative fixture below.
/// * `k >= w` is a checked shift-overflow: the operation panics and produces no
///   value. `K <= w - 1` keeps the antecedent false there too.
/// * a NEGATIVE `k` (a signed shift-amount operand) also panics in Rust, while
///   SMT-LIB `bvshl` by a huge unsigned amount would yield `0`; the explicit
///   `0 <= k` conjunct excludes it rather than leaning on the operand's type.
///
/// Restricted to a CONSTANT lhs on purpose. A structurally-bounded VARIABLE lhs
/// (`shift_lhs_unsigned_max`) would only give the weaker `0 <= dest <= B << K`, and
/// its truth would then rest on a separate model fact about that other local rather
/// than on the shift definition alone. No measured idiom needs it; not taken.
fn variable_shl_result_range(
    lhs: &Operand,
    dest_name: &str,
    amount: impl FnOnce() -> Formula,
    width: u32,
    signed: bool,
) -> Option<Formula> {
    // Real integer widths only. `range::signed_max` SATURATES to `i128::MAX` for an
    // out-of-domain width, which would be a ceiling ABOVE the true one and would let
    // `K` grow past the sign bit — decline instead of trusting the saturation.
    if width == 0 || width > 128 {
        return None;
    }
    let c: u128 = match lhs {
        Operand::Constant(ConstValue::Uint(v, _)) => *v,
        Operand::Constant(ConstValue::Int(v)) if *v >= 0 => *v as u128,
        _ => return None,
    };
    // `c == 0` makes `dest == 0` for every amount, but then `K` is unbounded and the
    // fact is worthless; `c >= 1` is also what makes the LOWER bound `c <= dest`
    // (from `2^k >= 1`) the useful half.
    if c < 1 {
        return None;
    }
    let ceiling: u128 = if signed {
        let m = crate::range::signed_max(width);
        if m < 0 {
            return None;
        }
        m as u128
    } else {
        crate::range::unsigned_max(width)
    };
    if c > ceiling {
        return None;
    }
    // The largest `K <= width - 1` with `c * 2^K <= ceiling`. `checked_mul` is what
    // detects the value overflow — `checked_shl` only checks the AMOUNT and would
    // silently wrap into a too-small, unsound ceiling.
    let mut k_max: u32 = 0;
    while k_max + 1 <= width - 1 {
        match c.checked_mul(1u128 << (k_max + 1)) {
            Some(v) if v <= ceiling => k_max += 1,
            _ => break,
        }
    }
    let hi = c.checked_mul(1u128 << k_max)?;
    debug_assert!(hi <= ceiling, "K search must not exceed the type ceiling");
    let dest = Formula::Var(dest_name.to_string(), Sort::Int);
    let amount = amount();
    Some(Formula::Implies(
        Box::new(Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(amount.clone())),
            Formula::Le(Box::new(amount), Box::new(Formula::Int(i128::from(k_max)))),
        ])),
        Box::new(Formula::And(vec![
            Formula::Le(Box::new(unsigned_value_to_formula(c)), Box::new(dest.clone())),
            Formula::Le(Box::new(dest), Box::new(unsigned_value_to_formula(hi))),
        ])),
    ))
}

#[cfg(test)]
fn shift_result_range(
    func: &VerifiableFunction,
    lhs_ty: Option<&Ty>,
    op: &BinOp,
    lhs: &Operand,
    rhs: &Operand,
    dest_name: &str,
    amount: Formula,
) -> Option<Formula> {
    shift_result_range_with(func, lhs_ty, op, lhs, rhs, dest_name, || amount)
}

/// `lhs_ty` is the shift's own result type as the CALLER resolved it — the SAME
/// value the `dest == lhs << rhs` equality is built with, including the
/// `shift_result_ty_from_dest` repair. Taking it as a parameter rather than
/// recomputing it is load-bearing: a range stated at a width the definition does not
/// use can CONTRADICT that definition (at `k == 63`, a width-64 def forces
/// `dest == -2^63` while a width-128 range asserts `dest >= 1`), and contradictory
/// hypotheses vacuously prove every obligation in the body.
///
/// `amount` is the shift-amount operand already rendered through the SAME operand
/// path the `dest == lhs << rhs` equality uses, so the conditional bound below names
/// the identical symbol (same rationale as `unsigned_floor_div_le_lhs`'s LHS
/// parameter — a differently-rendered symbol would make the implication silently
/// unfireable rather than wrong).
fn shift_result_range_with(
    func: &VerifiableFunction,
    lhs_ty: Option<&Ty>,
    op: &BinOp,
    lhs: &Operand,
    rhs: &Operand,
    dest_name: &str,
    amount: impl FnOnce() -> Formula,
) -> Option<Formula> {
    // Trust #50: an unsigned LEFT-shift by a constant `(x as W) << k`, where the LHS is
    // structurally bounded by `B = MAX(ELEM) <= MAX(W)`, tightens its result BELOW the type
    // max: if `B << k <= MAX(W)` the shift provably cannot overflow `W`, so for every value
    // `0 <= x <= B` the result `x << k = x * 2^k <= B << k` (no modular wrap). Emit
    // `dest <= B << k`. SOUNDNESS: a loaded element is some value in `[0, B]`, and under the
    // no-overflow check `B << k <= MAX(W)` the W-bit shift equals the true product, so the
    // bound is an unconditional upper bound on `dest` (monotone-safe — only turns a false-FAIL
    // into a PROVE, never an overflow into a false-PROVE; a shift that COULD overflow W has
    // `B << k > MAX(W)` and emits nothing). This is the addend-side companion to
    // `build_accumulator_bound_facts`' case (c): together they discharge `t += (x as W) << k`.
    if matches!(op, BinOp::Shl) {
        let Some(Ty::Int { width, signed }) = lhs_ty else {
            return None;
        };
        let (width, signed) = (*width, *signed);
        // A VARIABLE amount takes the conditional lane. It is the only lane that
        // covers a SIGNED lhs, and the only one that says anything at all about
        // `1i128 << width` — see `variable_shl_result_range` for why the bound must
        // be an implication and what keeps `k == w - 1` outside it.
        let Some(k) = const_shift_amount(rhs) else {
            return variable_shl_result_range(lhs, dest_name, amount, width, signed);
        };
        // A CONSTANT amount keeps the original unconditional unsigned bound. A signed
        // lhs with a constant amount is a separate (smaller) gap: it is covered by the
        // same construction but is not reached by any measured idiom, so it is left
        // declining rather than widened speculatively.
        if signed {
            return None;
        }
        if k >= u128::from(width) {
            return None;
        }
        let base = shift_lhs_unsigned_max(func, lhs)?;
        // `base * 2^k` with a TRUE value-overflow check. NB: `u128::checked_shl` only checks
        // the shift AMOUNT (`k < 128`), not value overflow, so it would silently WRAP for a
        // large `base` (e.g. a u64 element) and emit an unsound too-small bound; `checked_mul`
        // detects the overflow and declines instead. `1u128 << k` is safe (`k < width <= 128`).
        let scaled = base.checked_mul(1u128 << k)?;
        if scaled > crate::range::unsigned_max(width) {
            return None; // the shift could overflow W — no tight linear bound
        }
        let dest = Formula::Var(dest_name.to_string(), Sort::Int);
        return Some(Formula::Le(Box::new(dest), Box::new(unsigned_value_to_formula(scaled))));
    }
    if !matches!(op, BinOp::Shr) {
        return None;
    }
    let Some(Ty::Int { width, signed }) = lhs_ty else {
        return None;
    };
    let (width, signed) = (*width, *signed);
    let k = const_shift_amount(rhs)?;
    if k >= u128::from(width) {
        return None;
    }
    let k = k as u32; // safe: k < width <= 128
    let dest = Formula::Var(dest_name.to_string(), Sort::Int);
    if !signed {
        // Unsigned logical shift: `x: u_w => x >> k <= (2^w - 1) >> k`
        // (lower bound 0 is implicit in the unsigned range).
        let max_val = crate::range::unsigned_max(width) >> k;
        return Some(Formula::Le(Box::new(dest), Box::new(unsigned_value_to_formula(max_val))));
    }
    // soundness-signed-shift: a SIGNED arithmetic right shift now bounds
    // its result TWO-sidedly: `-(2^(w-1) >> k) <= dest <= (2^(w-1)-1) >> k`. This
    // was UNSOUND while the shift def bridged via the unsigned bv2nat
    // (BvToInt signed=false) -- the signed-domain endpoints contradicted the
    // bridged unsigned value and vacuously proved overflows. Now that chc.rs
    // bridges signed shifts via bv2int_signed, `dest` lives in this same signed
    // value-space, so the bound is an unconditional truth (monotone-safe: it can
    // only turn a false-FAIL into a PROVE, never an overflow into a false-PROVE).
    // `>>` on i128 is arithmetic, matching Rust's signed `>>` floor-toward-(-inf)
    // endpoints exactly.
    let (smin, smax): (i128, i128) = if width >= 128 {
        (i128::MIN, i128::MAX)
    } else {
        let half = 1i128 << (width - 1);
        (-half, half - 1)
    };
    let lower = smin >> k;
    let upper = smax >> k;
    Some(Formula::And(vec![
        Formula::Le(Box::new(Formula::Int(lower)), Box::new(dest.clone())),
        Formula::Le(Box::new(dest), Box::new(Formula::Int(upper))),
    ]))
}

fn bool_to_int_formula(func: &VerifiableFunction, op: &Operand) -> Formula {
    if let Operand::Constant(ConstValue::Bool(value)) = op {
        return Formula::Int(if *value { 1 } else { 0 });
    }

    Formula::Ite(
        Box::new(operand_to_formula(func, op)),
        Box::new(Formula::Int(1)),
        Box::new(Formula::Int(0)),
    )
}

pub(crate) fn float_binop_to_formula(
    func: &VerifiableFunction,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    width: u32,
) -> Option<Formula> {
    // soundness: float comparisons are modeled with the IEEE-754 FloatingPoint
    // theory (`fp.eq`/`fp.lt`/`fp.leq`/`fp.gt`/`fp.geq`), which matches Rust's
    // `PartialEq`/`PartialOrd` on floats EXACTLY — NaN is unordered and
    // `NaN != NaN`, and `+0.0 == -0.0`. Each operand's bit pattern (the existing
    // bitvector modelling of float locals) is reinterpreted as a float via
    // `FpFromBits`, so this composes with the rest of the encoding.
    //
    // History (round-8): before the FP theory existed these were left UNMODELED
    // (fail-closed) because the bitvector stand-ins were false-PROVEs — ordering
    // compared sign-dropped magnitudes (wrong for negatives) and general `==`
    // used full-bit `Eq` (made `NaN == NaN`). The `fp.*` encoding fixes both at
    // the source, validated end-to-end against the ay solver, so they are now
    // soundly modeled rather than skipped.
    //
    // The div-by-zero–critical `x == 0.0` / `x != 0.0` keeps its proven
    // magnitude-`== 0` encoding (equivalent to `fp.eq(x, +0.0)`, on the
    // battle-tested path).
    let has_zero = float_is_zero_operand(lhs) || float_is_zero_operand(rhs);
    match op {
        BinOp::Eq if has_zero => Some(float_zero_magnitude_eq(func, lhs, rhs, width)),
        BinOp::Ne if has_zero => {
            Some(Formula::Not(Box::new(float_zero_magnitude_eq(func, lhs, rhs, width))))
        }
        BinOp::Eq => fp_compare(func, lhs, rhs, width, FpCmp::Eq),
        BinOp::Ne => fp_compare(func, lhs, rhs, width, FpCmp::Ne),
        BinOp::Lt => fp_compare(func, lhs, rhs, width, FpCmp::Lt),
        BinOp::Le => fp_compare(func, lhs, rhs, width, FpCmp::Le),
        BinOp::Gt => fp_compare(func, lhs, rhs, width, FpCmp::Gt),
        BinOp::Ge => fp_compare(func, lhs, rhs, width, FpCmp::Ge),
        _ => None,
    }
}

/// IEEE-754 comparison operators we model from Rust `PartialOrd`/`PartialEq`.
#[derive(Clone, Copy)]
enum FpCmp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// Reinterpret a float operand's bit pattern as an IEEE-754 float term. `None`
/// for non-IEEE widths (fail-closed: an unmodeled comparison leaves the
/// discriminant unconstrained rather than risking an unsound encoding).
fn fp_operand(func: &VerifiableFunction, operand: &Operand, width: u32) -> Option<Formula> {
    let (eb, sb) = match Sort::float_for_width(width) {
        Some(Sort::Float { eb, sb }) => (eb, sb),
        _ => return None,
    };
    Some(Formula::FpFromBits {
        bits: Box::new(float_operand_formula(func, operand, width)),
        eb,
        sb,
    })
}

/// Sound IEEE-754 encoding of a float comparison; matches Rust float
/// `PartialOrd`/`PartialEq` (NaN unordered, `NaN != NaN`, `+0.0 == -0.0`).
fn fp_compare(
    func: &VerifiableFunction,
    lhs: &Operand,
    rhs: &Operand,
    width: u32,
    cmp: FpCmp,
) -> Option<Formula> {
    let l = Box::new(fp_operand(func, lhs, width)?);
    let r = Box::new(fp_operand(func, rhs, width)?);
    Some(match cmp {
        FpCmp::Eq => Formula::FpEq(l, r),
        FpCmp::Ne => Formula::Not(Box::new(Formula::FpEq(l, r))),
        FpCmp::Lt => Formula::FpLt(l, r),
        FpCmp::Le => Formula::FpLe(l, r),
        FpCmp::Gt => Formula::FpGt(l, r),
        FpCmp::Ge => Formula::FpGe(l, r),
    })
}

/// The destination of a float assignment, lifted into FP space. The dest local
/// is modeled as `Sort::BitVec(width)` (its IEEE bit pattern) everywhere, so a
/// value-definition must reinterpret it via `FpFromBits` to compare against an
/// FP-theory result. `None` for non-IEEE widths (fail-closed).
///
/// NOTE: the inner var is kept BARE (`Var(dest, BitVec)`) so
/// `generate::block_def_subject` / `rebind_block_def_subject` can recover and
/// re-version the subject through the `FpFromBits` wrapper.
fn fp_dest_term(dest_name: &str, width: u32) -> Option<Formula> {
    let (eb, sb) = match Sort::float_for_width(width) {
        Some(Sort::Float { eb, sb }) => (eb, sb),
        _ => return None,
    };
    Some(Formula::FpFromBits {
        bits: Box::new(Formula::Var(dest_name.to_string(), Sort::BitVec(width))),
        eb,
        sb,
    })
}

/// Sound value-definition for a float ARITHMETIC assignment `dest = lhs OP rhs`
/// (`OP` ∈ Add/Sub/Mul/Div). Returns the complete top-level **structural** `Eq`
///
///   `Eq( FpFromBits(dest), fp.OP(RNE, FpFromBits(lhs), FpFromBits(rhs)) )`
///
/// Structural `Eq` (NOT `FpEq`) is the only sound choice for a *definition*:
/// it is reflexive on NaN and distinguishes ±0, so `dest` is pinned to exactly
/// the IEEE result value (a NaN result merely leaves the dest bit pattern free
/// over all NaN encodings — sound underconstraint matching unspecified Rust NaN
/// payloads). Rust `f32/f64` `+ - * /` round to nearest-ties-even (RNE) with no
/// dynamic mode, so RNE matches hardware exactly. `None` for non-arith ops or
/// non-IEEE widths (fail-closed: dest stays free → at worst a missed proof).
fn fp_arith_value_def(
    func: &VerifiableFunction,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    dest_name: &str,
    width: u32,
) -> Option<Formula> {
    let l = Box::new(fp_operand(func, lhs, width)?);
    let r = Box::new(fp_operand(func, rhs, width)?);
    let rne = || Box::new(Formula::FpRoundingMode(RoundingMode::RNE));
    let fp_result = match op {
        BinOp::Add => Formula::FpAdd(rne(), l, r),
        BinOp::Sub => Formula::FpSub(rne(), l, r),
        BinOp::Mul => Formula::FpMul(rne(), l, r),
        BinOp::Div => Formula::FpDiv(rne(), l, r),
        _ => return None,
    };
    let dest = Box::new(fp_dest_term(dest_name, width)?);
    Some(Formula::Eq(dest, Box::new(fp_result)))
}

/// Sound value-definition for a float `dest = -operand` (`Rvalue::UnaryOp(Neg)`).
/// Negation is EXACT in IEEE-754 (a sign-bit flip, no rounding), so no rounding
/// mode is needed: `Eq( FpFromBits(dest), fp.neg(FpFromBits(operand)) )`.
fn fp_neg_value_def(
    func: &VerifiableFunction,
    operand: &Operand,
    dest_name: &str,
    width: u32,
) -> Option<Formula> {
    let a = Box::new(fp_operand(func, operand, width)?);
    let dest = Box::new(fp_dest_term(dest_name, width)?);
    Some(Formula::Eq(dest, Box::new(Formula::FpNeg(a))))
}

/// Trust (2026-10-05, NEG-WRAP-OFF-1): THE one spelling of a bare (wrapping) signed
/// MIR `Neg` of `value` at `width` bits — `ite(value == MIN, MIN, -value)`, exact on
/// every in-range `value` (the caller states `value`'s type range beside it). Off
/// `MIN` the term is the `Formula::Neg` node the block definition always carried.
/// `None` outside `1..=128`.
///
/// One constructor, two readers: `extract_block_definitions` emits it, and
/// `contracts::machine_faithful_translate` recognizes it BY CONSTRUCTION (the node
/// must be byte-identical to this function's output) and reads it as the
/// declared-width `0 -w value`, so the Machine{w} postcondition lane translates the
/// definition exactly as it translated the bare `Neg` before.
pub(crate) fn bare_neg_wrap_ite(value: &Formula, width: u32) -> Option<Formula> {
    if !(1..=128).contains(&width) {
        return None;
    }
    let min = crate::range::type_min_formula(width, true);
    Some(Formula::Ite(
        Box::new(Formula::Eq(Box::new(value.clone()), Box::new(min.clone()))),
        Box::new(min),
        Box::new(Formula::Neg(Box::new(value.clone()))),
    ))
}

/// Trust (2026-10-05, NEG-WRAP-OFF-1): the `(width, signed)` machine shape of an
/// integer `dest = Neg(operand)`, read from the DESTINATION — a pointer-width
/// integer at the pinned 64-bit target (`Ty::int_width`'s convention) — or `None`.
///
/// The destination is authoritative because a MIR `Neg`'s result type IS its
/// operand type, while `operand_ty` of a width-less `ConstValue::Int` is derived
/// from the constant's VALUE, not its type. A PLACE operand carries a real
/// declared type; if that type is a machine integer of a different shape the two
/// disagree and nothing is modelled (fail-closed: an exact-value def at a wrong
/// width is wrong in both directions). `char`, `bool` and non-integer destinations
/// are `None` (no integer `Neg` produces them).
pub(crate) fn bare_neg_machine_shape(
    func: &VerifiableFunction,
    dest: &trust_types::Place,
    operand: &Operand,
) -> Option<(u32, bool)> {
    fn machine_shape(ty: &Ty) -> Option<(u32, bool)> {
        match ty {
            Ty::Int { width, signed } => Some((*width, *signed)),
            Ty::PtrSizedInt { signed } => Some((64, *signed)),
            _ => None,
        }
    }
    let shape = machine_shape(crate::place_ty_cow(func, dest)?.as_ref())
        .filter(|(width, _)| (1..=128).contains(width))?;
    if let Operand::Copy(source) | Operand::Move(source) = operand
        && crate::place_ty_cow(func, source).as_deref().and_then(machine_shape) != Some(shape)
    {
        return None;
    }
    Some(shape)
}

/// Trust (2026-10-13, BARE-BINOP-LITERAL-LHS-WIDTH-1): the `(width, signed)` machine
/// shape of a bare (wrapping) integer `dest = lhs OP rhs` (`Add`/`Sub`/`Mul`), read
/// from the DESTINATION — a pointer-width integer at the pinned 64-bit target
/// (`Ty::int_width`'s convention) — with BOTH operands checked against it, or `None`.
///
/// The destination is authoritative because a MIR `Add`/`Sub`/`Mul` has one type for
/// both operands and the result, while `operand_ty` of a width-less `ConstValue::Int`
/// is derived from the constant's VALUE (i64 for `1`). Reading the LEFT operand's
/// type, as the block definition did, modelled `1 + x` on `i32` as wrapping at 2^64
/// — the sibling of the `Neg` hazard `bare_neg_machine_shape` closed (NEG-WRAP-OFF-1).
///
/// Each operand must AGREE with the destination, or nothing is modelled (fail-closed:
/// an exact-value def at a wrong width is wrong in both directions):
///   * a PLACE: its own machine shape equals the destination's (shapes, not `Ty`
///     equality, so the `usize` / `PtrSizedInt` spellings agree);
///   * a `ConstValue::Int`: the destination is signed and the value fits its width;
///   * a `ConstValue::Uint`: the destination is unsigned, the constant carries the
///     same width, and the value fits it;
///   * any other constant: its typed `operand_ty` machine shape equals the
///     destination's;
///   * anything else (a symbolic or unsupported operand): disagreement.
///
/// The fits-width rule is `generate::assert_refutation`'s
/// (`wrapping_operand_matches_destination`), shared rather than re-spelled.
pub(crate) fn bare_binop_machine_shape(
    func: &VerifiableFunction,
    dest: &trust_types::Place,
    lhs: &Operand,
    rhs: &Operand,
) -> Option<(u32, bool)> {
    fn machine_shape(ty: &Ty) -> Option<(u32, bool)> {
        match ty {
            Ty::Int { width, signed } => Some((*width, *signed)),
            Ty::PtrSizedInt { signed } => Some((64, *signed)),
            _ => None,
        }
    }
    let shape = machine_shape(crate::place_ty_cow(func, dest)?.as_ref())
        .filter(|(width, _)| (1..=128).contains(width))?;
    let (width, signed) = shape;
    let agrees = |operand: &Operand| match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            crate::place_ty_cow(func, place).as_deref().and_then(machine_shape) == Some(shape)
        }
        Operand::Constant(ConstValue::Int(value)) => {
            signed && crate::generate::signed_constant_fits_width(*value, width)
        }
        Operand::Constant(ConstValue::Uint(value, encoded_width)) => {
            !signed
                && *encoded_width == width
                && crate::generate::unsigned_constant_fits_width(*value, width)
        }
        Operand::Constant(_) => {
            crate::operand_ty_cow(func, operand).as_deref().and_then(machine_shape) == Some(shape)
        }
        _ => false,
    };
    (agrees(lhs) && agrees(rhs)).then_some(shape)
}

/// Sound value-definition for a float `dest = operand.abs()` (a `f32::abs` /
/// `f64::abs` Call). Like negation, abs is EXACT in IEEE-754 (a sign-bit clear,
/// no rounding), so no rounding mode is needed:
/// `Eq( FpFromBits(dest), fp.abs(FpFromBits(operand)) )`. Used by
/// `generate::build_fp_abs_facts` (abs arrives as a Call terminator, not an
/// Rvalue, so it is emitted as a global SSA-gated fact rather than a per-block
/// definition). `None` for non-IEEE widths (fail-closed).
pub(crate) fn fp_abs_value_def(
    func: &VerifiableFunction,
    operand: &Operand,
    dest_name: &str,
    width: u32,
) -> Option<Formula> {
    let a = Box::new(fp_operand(func, operand, width)?);
    let dest = Box::new(fp_dest_term(dest_name, width)?);
    Some(Formula::Eq(dest, Box::new(Formula::FpAbs(a))))
}

/// Sound encoding of `x == 0.0` (and, negated, `x != 0.0`): the magnitude (all
/// bits except the sign) is zero. True for +0.0 and -0.0; false for NaN (nonzero
/// magnitude) and every other value.
fn float_zero_magnitude_eq(
    func: &VerifiableFunction,
    lhs: &Operand,
    rhs: &Operand,
    width: u32,
) -> Formula {
    let nonzero_side = if float_is_zero_operand(lhs) { rhs } else { lhs };
    Formula::Eq(
        Box::new(float_magnitude_formula(func, nonzero_side, width)),
        Box::new(Formula::BitVec { value: 0, width: width - 1 }),
    )
}

fn float_magnitude_formula(func: &VerifiableFunction, operand: &Operand, width: u32) -> Formula {
    Formula::BvExtract {
        inner: Box::new(float_operand_formula(func, operand, width)),
        high: width - 2,
        low: 0,
    }
}

fn float_operand_formula(func: &VerifiableFunction, operand: &Operand, width: u32) -> Formula {
    match operand {
        Operand::Constant(ConstValue::Float(value)) => Formula::BitVec {
            value: match width {
                32 => i128::from(((*value) as f32).to_bits()),
                64 => i128::from(value.to_bits()),
                _ => i128::from(value.to_bits()),
            },
            width,
        },
        Operand::Constant(ConstValue::FloatBits { bits, width: const_width })
            if *const_width == width =>
        {
            match i128::try_from(*bits) {
                Ok(value) => Formula::BitVec { value, width },
                Err(_) => operand_to_formula(func, operand),
            }
        }
        _ => operand_to_formula(func, operand),
    }
}

fn float_is_zero_operand(operand: &Operand) -> bool {
    match operand {
        Operand::Constant(ConstValue::Float(value)) => *value == 0.0,
        Operand::Constant(ConstValue::FloatBits { bits, width }) => {
            crate::float_bits_magnitude_is_zero(*bits, *width)
        }
        _ => false,
    }
}

#[cfg(test)]
#[path = "guards_bool_walk_tests.rs"]
mod bool_walk_tests;

#[cfg(test)]
#[path = "guards_deref_hop_anchor_tests.rs"]
mod deref_hop_anchor_tests;

#[cfg(test)]
#[path = "guards_slice_view_anchor_tests.rs"]
mod slice_view_anchor_tests;

// Trust (2026-10-15, STRING-AS-STR): std `String`'s own `Deref` view ties its length.
#[cfg(test)]
#[path = "guards_string_view_len_tests.rs"]
mod string_view_len_tests;

#[cfg(test)]
#[path = "guards_mut_pointer_copy_tests.rs"]
mod mut_pointer_copy_tests;

// Trust (LEN-TIE-JOIN-SEED-1 / LAST-SOME-ARM-SEED-1, 2026-10-12): the collection-length
// ties and the `last()`/`first()` non-emptiness fact are seeded only at a block their
// own edge is the one entry of. Pinned on real extracted MIR.
#[cfg(test)]
#[path = "guards_len_seed_entry_tests.rs"]
mod len_seed_entry_tests;

// Trust (2026-10-15, TRUST-KI-1015-1): an `if` without `else` keeps, under its skip
// edge's route guard, the guard copy its join loses.
#[cfg(test)]
#[path = "guards_skip_edge_join_tests.rs"]
mod skip_edge_join_tests;

#[cfg(test)]
mod tests {
    use trust_types::UnwindEdge;

    use super::*;

    fn test_func() -> VerifiableFunction {
        VerifiableFunction {
            name: "test".to_string(),
            def_path: "test::test".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Bool, name: Some("ret".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("flag".into()) },
                ],
                blocks: vec![],
                arg_count: 2,
                return_ty: Ty::Bool,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    fn checked_literal_func(value_ty: Ty, lhs: Operand, rhs: Operand) -> VerifiableFunction {
        checked_op_func(BinOp::Add, value_ty, lhs, rhs)
    }

    fn checked_op_func(op: BinOp, value_ty: Ty, lhs: Operand, rhs: Operand) -> VerifiableFunction {
        VerifiableFunction {
            name: "checked_literal".into(),
            def_path: "test::checked_literal".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: value_ty.clone(), name: Some("ret".into()) },
                    LocalDecl { index: 1, ty: value_ty.clone(), name: Some("x".into()) },
                    LocalDecl {
                        index: 2,
                        ty: Ty::Tuple(vec![value_ty.clone(), Ty::Bool]),
                        name: Some("checked".into()),
                    },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::CheckedBinaryOp(op, lhs, rhs),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            cond: Operand::Move(Place {
                                local: 2,
                                projections: vec![trust_types::Projection::Field(1)],
                            }),
                            expected: false,
                            msg: AssertMessage::Overflow(op),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                            unwind: UnwindEdge::Unreachable,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: value_ty,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    // ─────────────────────────────────────────────────────────────────────
    // #222 — THE BICONDITIONAL PIN.
    //
    // The `unix_hardened` panic-boundary twin used to build its violation as
    // `Not(extract_assert_passed_semantics()[0])`. It now emits
    // `checked_binop_out_of_range_violation` instead. Those two must denote the
    // SAME proposition on every block where either fires, or the hardened row
    // silently stops being the negation of the safe range — a change of MEANING
    // disguised as a change of spelling.
    //
    // This is the "ADMIT and EMIT helpers must agree" discipline, and an
    // agreement between two helpers is a BICONDITIONAL, so both halves are
    // pinned: the SHAPE (exact De Morgan dual) and the DOMAIN (`Some` exactly
    // when the safe-range extractor is non-empty).
    // ─────────────────────────────────────────────────────────────────────

    /// The De Morgan dual of `And([Le(lo, x), Le(x, hi)])`, computed here so the
    /// assertion states the relationship rather than restating the new code.
    fn de_morgan_dual_of_in_range(in_range: &Formula) -> Formula {
        let Formula::And(cs) = in_range else {
            panic!("in_range must be a two-conjunct And, got {in_range:?}");
        };
        assert_eq!(cs.len(), 2, "in_range must be exactly `lo <= x && x <= hi`");
        let (Formula::Le(lo, x1), Formula::Le(x2, hi)) = (&cs[0], &cs[1]) else {
            panic!("in_range conjuncts must both be `Le`, got {cs:?}");
        };
        assert_eq!(x1, x2, "both bounds must be on the SAME result term");
        Formula::Or(vec![Formula::Lt(x1.clone(), lo.clone()), Formula::Gt(x2.clone(), hi.clone())])
    }

    #[test]
    fn out_of_range_violation_is_the_de_morgan_dual_of_in_range() {
        let x = Operand::Copy(Place::local(1));
        let mut checked = 0usize;
        for op in [BinOp::Add, BinOp::Sub, BinOp::Mul] {
            for ty in [Ty::i8(), Ty::i32(), Ty::i64(), Ty::u8(), Ty::u32(), Ty::u64()] {
                let func = checked_op_func(op, ty.clone(), x.clone(), x.clone());
                let block = &func.body.blocks[0];
                let facts = extract_assert_passed_semantics(&func, block);
                let violation = checked_binop_out_of_range_violation(&func, block);

                // DOMAIN half: the two helpers fire on exactly the same blocks.
                assert_eq!(
                    facts.is_empty(),
                    violation.is_none(),
                    "domain disagreement at {op:?}/{ty:?}: the hardened twin would \
                     fall back to a different violation than the safe-range \
                     extractor's negation"
                );
                let (Some((in_range, _)), Some(violation)) = (facts.split_first(), violation)
                else {
                    continue;
                };

                // SHAPE half: exactly the dual, node for node.
                assert_eq!(
                    violation,
                    de_morgan_dual_of_in_range(in_range),
                    "the emitted violation is not the De Morgan dual of in_range \
                     at {op:?}/{ty:?}"
                );

                // The property the CERTIFIER keys on. `certify_disjunctive_
                // contradiction` scans the conjunct pool for `Formula::Or`; a
                // violation that is not an `Or` at the top is invisible to it,
                // which is the entire defect #222 closed. Assert the recognizer's
                // precondition directly, not a proxy for it.
                assert!(
                    matches!(violation, Formula::Or(ref ds) if ds.len() == 2),
                    "the violation must be a 2-way top-level `Or` or the kernel \
                     recognizer cannot see it: {violation:?}"
                );
                checked += 1;
            }
        }
        assert_eq!(checked, 18, "the matrix must actually exercise 18 op/type pairs");
    }

    /// The emitted core is the term the KERNEL names. `trust_semantics::
    /// noOverflow_violation_formula` is the trust-types reflection of the Clean
    /// `noOverflow` definition; `range.rs` already pins it structurally equal to
    /// the per-statement lane's `out_of_range`. Pin the hardened twin to the same
    /// term, so all three — primary VC, hardened twin, kernel lemma — cannot
    /// drift apart independently.
    #[test]
    fn out_of_range_violation_matches_the_kernel_no_overflow_denotation() {
        let x = Operand::Copy(Place::local(1));
        for (ty, width, signed) in [
            (Ty::i8(), 8u32, true),
            (Ty::i32(), 32, true),
            (Ty::u8(), 8, false),
            (Ty::u32(), 32, false),
        ] {
            let func = checked_op_func(BinOp::Add, ty.clone(), x.clone(), x.clone());
            let violation = checked_binop_out_of_range_violation(&func, &func.body.blocks[0])
                .expect("a checked Add on an in-range operand must yield a violation");

            // The kernel term over a variable named `result`; substitute our
            // actual result expression for that variable and the two must be
            // structurally identical.
            let kernel = trust_semantics::noOverflow_violation_formula(width, signed, "result");
            let Formula::Or(kernel_ds) = kernel else {
                panic!("the kernel denotation stopped being an `Or` — re-derive #222");
            };
            let Formula::Or(ref ds) = violation else {
                panic!("emitted violation is not an `Or`: {violation:?}");
            };
            assert_eq!(ds.len(), kernel_ds.len(), "disjunct count diverged at {ty:?}");
            // Bounds and relational operators must match exactly; only the
            // result TERM differs (kernel: `Var("result")`, emitted: `x + x`).
            match (&ds[0], &kernel_ds[0], &ds[1], &kernel_ds[1]) {
                (
                    Formula::Lt(_, lo),
                    Formula::Lt(_, kernel_lo),
                    Formula::Gt(_, hi),
                    Formula::Gt(_, kernel_hi),
                ) => {
                    assert_eq!(lo, kernel_lo, "min bound diverged from the kernel at {ty:?}");
                    assert_eq!(hi, kernel_hi, "max bound diverged from the kernel at {ty:?}");
                }
                other => panic!("shape diverged from the kernel denotation: {other:?}"),
            }
        }
    }

    #[test]
    fn checked_assert_semantics_contextualize_signed_narrow_literals_exactly() {
        let x = Operand::Copy(Place::local(1));
        for (lhs, rhs) in [
            (x.clone(), Operand::Constant(ConstValue::Int(1))),
            (Operand::Constant(ConstValue::Int(1)), x.clone()),
        ] {
            let func = checked_literal_func(Ty::i32(), lhs, rhs);
            let success = extract_assert_passed_semantics(&func, &func.body.blocks[0]);
            let failure = extract_overflow_flag_semantics(&func, &func.body.blocks[0]);
            assert!(!success.is_empty(), "representable i32 literal must retain success facts");
            assert!(!failure.is_empty(), "representable i32 literal must retain overflow facts");

            let success_smt = Formula::And(success).to_smtlib();
            assert!(
                success_smt.contains("(= checked.0 (+"),
                "success facts must define the checked value: {success_smt}"
            );
            assert!(
                success_smt.contains("2147483648")
                    && success_smt.contains("2147483647")
                    && !success_smt.contains("9223372036854775808"),
                "the tuple's authenticated i32 domain—not the literal fallback i64—must drive the facts: {success_smt}"
            );
        }

        let out_of_range = checked_literal_func(
            Ty::i8(),
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Int(128)),
        );
        assert!(
            extract_assert_passed_semantics(&out_of_range, &out_of_range.body.blocks[0]).is_empty(),
            "an out-of-range i8 literal must not mint success-edge arithmetic facts"
        );
        assert!(
            extract_overflow_flag_semantics(&out_of_range, &out_of_range.body.blocks[0]).is_empty(),
            "an out-of-range i8 literal must not mint overflow-flag arithmetic facts"
        );
    }

    #[test]
    fn enum_aggregate_write_constrains_downcast_payload_place() {
        // Trust: `let o: Option<u32> = Some(7)` lowers to an ADT aggregate whose
        // payload is read in the match arm as `(o as Some).0` → `o@1.0`. The
        // write must constrain that downcast-named place; otherwise the payload
        // is a free variable and the arm's `v + 1` overflow check false-fails
        // (the solver picks `o@1.0 = u32::MAX`). Regression for the enum-payload
        // aggregate-naming mismatch — must NOT depend on telling struct from enum.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl {
                index: 1,
                ty: Ty::Adt {
                    adt_kind: None,
                    layout: None,
                    variants: Vec::new().into(),
                    name: "Option".into(),
                    // Enum layout per `lower_enum_adt`: `__tag` then per-variant
                    // flattened payload fields (`__v1_0` for `Some`'s field 0).
                    fields: vec![("__tag".into(), Ty::i32()), ("__v1_0".into(), Ty::u32())].into(),
                    disc_index_safe: false,
                    faithful_enum_repr: None,
                    enum_layout: None,
                    arbitrary_precision: None,
                    validity_wrapper: None,
                },
                name: Some("o".into()),
            },
        ];
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Aggregate(
                    AggregateKind::Adt {
                        name: "Option".into(),
                        variant: 1,
                        active_field: None,
                        args: None,
                    },
                    vec![Operand::Constant(ConstValue::Int(7))],
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }];

        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        let constrains_downcast_payload = defs.iter().any(|f| {
            matches!(f, Formula::Eq(lhs, rhs)
                if lhs.var_name() == Some("o@1.0")
                && matches!(rhs.as_ref(), Formula::Int(7)))
        });
        assert!(
            constrains_downcast_payload,
            "enum payload write must constrain `o@1.0 == 7`, got: {defs:?}"
        );
    }

    /// Build `_c = Discriminant(e); _d = _c as usize` over a `#[repr(i8)]` enum with
    /// the given RAW discriminant bit patterns, and ask `cast_definition_formula` for
    /// the cast's definition fact.
    fn enum_disc_index_cast_def(raw_patterns: &[i128]) -> Option<Formula> {
        enum_disc_cast_def(Ty::i8(), Ty::usize(), raw_patterns)
    }

    /// Build `_c = Discriminant(e); _d = _c as <cast_to>` over a `#[repr(<repr>)]` enum
    /// with the given discriminants (`repr` types both the synthetic `__tag` field and
    /// the `Discriminant` read's dest, as the extractor spells a fieldless repr enum),
    /// and ask `cast_definition_formula` for the cast's definition fact.
    fn enum_disc_cast_def(repr: Ty, cast_to: Ty, raw_patterns: &[i128]) -> Option<Formula> {
        let variants: Vec<trust_types::VariantDef> = raw_patterns
            .iter()
            .enumerate()
            .map(|(i, d)| trust_types::VariantDef {
                name: format!("V{i}"),
                discriminant: *d,
                fields: vec![],
            })
            .collect();
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u8(), name: Some("ret".into()) },
            LocalDecl {
                index: 1,
                ty: Ty::Adt {
                    adt_kind: None,
                    layout: None,
                    name: "E".into(),
                    fields: vec![("__tag".into(), repr.clone())].into(),
                    variants: variants.into(),
                    // `#[repr(iN/uN)]` inhibits niche layout, so rustc classifies this
                    // enum `Variants::Multiple { Direct }` — the gate PASSES here; the
                    // tag VALUES against the destination type are what must decline it.
                    disc_index_safe: true,
                    faithful_enum_repr: None,
                    enum_layout: None,
                    arbitrary_precision: None,
                    validity_wrapper: None,
                },
                name: Some("e".into()),
            },
            // The `Discriminant` read dest: the repr type.
            LocalDecl { index: 2, ty: repr, name: Some("c".into()) },
            LocalDecl { index: 3, ty: cast_to.clone(), name: Some("d".into()) },
        ];
        func.body.arg_count = 1;
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Discriminant(Place::local(1)),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }];
        cast_definition_formula(&func, &Place::local(3), &Operand::Copy(Place::local(2)), &cast_to)
    }

    /// ADVERSARIAL (R5): GATE-NONNEG on the enum-disc-index cast must test the
    /// **normalized** discriminant, not the raw bit pattern.
    ///
    /// The old `min(v.discriminant) >= 0` test was vacuous when
    /// `VariantDef::discriminant` still carried the extractor's RAW pattern — always
    /// non-negative in its `i128` carrier (`-1` in `repr(i8)` arrived as `255`).
    /// Witness — a live FALSE PROOF:
    ///
    /// ```ignore (illustrative)
    /// #[repr(i8)] enum E { A = 0, B = -1 }
    /// fn f(e: E, arr: &[u8; 256]) -> u8 { arr[e as usize] }
    /// ```
    ///
    /// `repr(i8)` inhibits niche layout so `disc_index_safe` is true and the raw gate
    /// passed; the emitted `_d == e_disc` equality plus `_c: i8`'s `[-128, 127]` range
    /// let the bounds VC `_d < 256` PROVE, while `e == B` really indexes
    /// `0xFFFF_FFFF_FFFF_FFFF`. **The `_d == e_disc` equality must be DROPPED** — that,
    /// and only that, is what this test pins.
    ///
    /// STALE PREMISE CORRECTED 2026-08-31: extraction now DECODES the tag at the single
    /// boundary (`trust_mir_extract::ty_convert`'s `decode_discr_tag_or_raw`, added by
    /// `b4fd4c0e43a` repair #1), so `VariantDef::discriminant` is the TRUE SIGNED tag —
    /// see the GATE-NONNEG note at `cast_definition_formula`, which says the same. The
    /// helper below still feeds RAW patterns (255/251) only because
    /// `normalize_raw_discriminant` is IDEMPOTENT on already-decoded values
    /// (`normalize(-1, 8, true) == -1`), so both spellings exercise the same gate arm.
    #[test]
    fn enum_disc_index_cast_negative_repr_i8_fails_closed() {
        // PIN RE-POINTED 2026-08-31 (was `== None` for both tag sets). WHAT MOVED, AND
        // WHY THE PIN — NOT THE PROPERTY — WAS WRONG:
        //
        // Two campaigns fixed the SAME false proof and a squash merge took their union.
        // `b4fd4c0e43a` (2026-08-26) decoded the tag at the extraction boundary AND added
        // a new branch to `cast_definition_formula` AFTER GATE-NONNEG: the exact
        // non-narrowing signed->unsigned two's-complement value relation. The b62 campaign
        // branch instead normalized at each consumer and wrote THIS test — and on that
        // branch GATE-NONNEG was the LAST branch before `None`, so declining it really did
        // drop the fact (verified: `git show origin/b62-merge-redo:.../guards.rs` holds
        // this test and ZERO hits for the two's-complement branch). The squash
        // `d24c6712111` landed the b62 gate + test onto a tree where the decline now falls
        // THROUGH into the newer branch, so this test went red at its own landing commit
        // and has never passed on main. No pre-push lane runs a `crates/` test, so nothing
        // said so.
        //
        // THE PROPERTY IS UNCHANGED AND STILL HOLDS: the plain `_d == e_disc` equality is
        // still refused for a negative-tag enum. `== None` was an over-specified proxy for
        // that — it pinned the absence of ANY fact rather than the absence of the FALSE
        // one. What replaced the dropped fact is the EXACT `as` semantics, which is
        // strictly STRONGER than dropping:
        //   * it is a total value-level identity of the statement (`dest == if src >= 0
        //     { src } else { src + 2^64 }`), so it constrains no input and removes no
        //     execution from the model — it cannot manufacture a proof;
        //   * at `e == B` it yields `_d == 2^64-1`, so the witness this test defends
        //     (`arr[e as usize]` over `[u8; 256]`) still REFUTES — and now with a model
        //     that names the failing input, where `None` refuted only by `_d` being
        //     unconstrained.
        // Formula arithmetic is over SMT `Int`, not `BitVec`, so `c + 2^64` does not wrap.
        //
        // THE NAMED DEPENDENCY, which is why the negative arm is asserted structurally:
        // this lane is sound only because the discriminant source denotes the TRUE SIGNED
        // tag. If any consumer ever re-RAWs it (`_4 == 255`), the `Ite` takes its POSITIVE
        // arm and `_d == 255 < 256` becomes a false PROVE. Today decode happens once, at
        // the extraction boundary.
        let two_to_the_64 = 1i128 << 64;
        for tags in [&[0i128, 255][..], &[251, 3][..]] {
            let def = enum_disc_index_cast_def(tags).unwrap_or_else(|| {
                panic!("the signed->unsigned relation lane must still model this cast: {tags:?}")
            });
            assert_ne!(
                def.var_name(),
                Some("c"),
                "a negative `repr(i8)` discriminant must NOT get the plain `_d == e_disc` \
                 equality: `e as usize` reinterprets the sign bit as ~2^64, so the equality \
                 is false and the bounds VC falsely proves. tags {tags:?}, got {def:?}"
            );
            assert!(
                matches!(&def, Formula::Ite(cond, then, els)
                    if matches!(cond.as_ref(), Formula::Ge(l, r)
                        if l.var_name() == Some("c") && matches!(r.as_ref(), Formula::Int(0)))
                    && then.var_name() == Some("c")
                    && matches!(els.as_ref(), Formula::Add(l, r)
                        if l.var_name() == Some("c")
                        && matches!(r.as_ref(), Formula::Int(m) if *m == two_to_the_64))),
                "the NEGATIVE arm must be `c + 2^64` — that arm is the whole reason the \
                 out-of-bounds witness stays reachable; a plain equality, a wrong modulus \
                 or a dropped else arm is the false proof this test exists for. \
                 tags {tags:?}, got {def:?}"
            );
        }
    }

    /// Positive control for the test above: the lever the gate exists to enable must
    /// still fire for a genuinely non-negative `repr(i8)` enum, otherwise the fix would
    /// have "fixed" the false proof by disabling the feature.
    #[test]
    fn enum_disc_index_cast_nonneg_repr_i8_still_emits_the_equality() {
        let def = enum_disc_index_cast_def(&[0, 1, 2])
            .expect("a non-negative repr(i8) enum must keep emitting `_d == e_disc`");
        assert!(
            def.var_name() == Some("c"),
            "the emitted value is the discriminant operand itself, got {def:?}"
        );
    }

    /// CAST-ENUMDISC-SIGNED-1: the identity `_d == e_disc` must NOT be emitted when a
    /// tag does not survive the cast because the DESTINATION is signed and the tag
    /// sets its sign bit. `#[repr(u8)] enum F { A = 200, B = 1 }` gives
    /// `F::A as i8 == -56`; the old gate read only the destination WIDTH, emitted
    /// `_0 == _2`, and that equality contradicted value_facts' true tag image
    /// `_0 == -56` and the `i8` range — the `F::A` path vanished and
    /// `ensures result >= 0` was kernel-certified (stage1-w15r, certify, rc=0).
    ///
    /// MEASURED BEFORE (the parent commit's gate): every case below returned
    /// `Some(Var("c"))`, the plain identity.
    #[test]
    fn enum_disc_same_width_signed_cast_of_a_high_tag_is_not_identity() {
        let usize_max_tag = i128::from(u64::MAX);
        let cases: [(&str, Ty, Ty, &[i128]); 6] = [
            ("repr(u8) {200, 1} as i8", Ty::u8(), Ty::i8(), &[200, 1]),
            ("repr(u8) {255} as i8", Ty::u8(), Ty::i8(), &[255]),
            ("repr(u8) {128, 0} as i8 (the boundary)", Ty::u8(), Ty::i8(), &[128, 0]),
            ("repr(u16) {40000} as i16", Ty::u16(), Ty::i16(), &[40_000]),
            ("repr(u32) {0x8000_0000, 7} as i32", Ty::u32(), Ty::i32(), &[0x8000_0000, 7]),
            ("repr(usize) {usize::MAX} as isize", Ty::usize(), Ty::isize(), &[usize_max_tag]),
        ];
        for (what, repr, cast_to, tags) in cases {
            let def = enum_disc_cast_def(repr, cast_to, tags);
            assert_ne!(
                def.as_ref().and_then(Formula::var_name),
                Some("c"),
                "{what}: a tag at or above 2^(w-1) changes value under a same-width \
                 unsigned->signed cast, so `_d == e_disc` is false for it and the VC's \
                 facts contradict each other; got {def:?}"
            );
        }
    }

    /// Controls for the test above: a cast that leaves EVERY tag unchanged keeps the
    /// identity, whichever branch of `cast_definition_formula` emits it — the fix must
    /// not "repair" the false proof by dropping the lever `proved/enumdf_*` rely on.
    #[test]
    fn enum_disc_cast_that_preserves_every_tag_keeps_the_identity() {
        let i64_max_tag = i128::from(i64::MAX);
        let cases: [(&str, Ty, Ty, &[i128]); 9] = [
            ("repr(u8) {100, 1} as i8", Ty::u8(), Ty::i8(), &[100, 1]),
            ("repr(u8) {127, 0} as i8 (the boundary)", Ty::u8(), Ty::i8(), &[127, 0]),
            ("repr(u8) {200, 1} as i16", Ty::u8(), Ty::i16(), &[200, 1]),
            ("repr(u8) {200, 1} as u8", Ty::u8(), Ty::u8(), &[200, 1]),
            ("repr(u8) {200, 1} as usize", Ty::u8(), Ty::usize(), &[200, 1]),
            ("repr(i8) {100, 1} as u8", Ty::i8(), Ty::u8(), &[100, 1]),
            ("repr(u16) {32767} as i16 (the boundary)", Ty::u16(), Ty::i16(), &[32_767]),
            ("repr(u16) {40000} as i32", Ty::u16(), Ty::i32(), &[40_000]),
            ("repr(u64) {i64::MAX} as i64", Ty::u64(), Ty::i64(), &[i64_max_tag]),
        ];
        for (what, repr, cast_to, tags) in cases {
            let def = enum_disc_cast_def(repr, cast_to, tags);
            assert_eq!(
                def.as_ref().and_then(Formula::var_name),
                Some("c"),
                "{what}: every tag survives this cast, so `_d == e_disc` must still be \
                 emitted; got {def:?}"
            );
        }
    }

    /// `nonneg_tag_survives_int_cast` against Rust's own `as`: for every width a repr
    /// can have and tags around each sign/width boundary, the predicate holds exactly
    /// when casting the tag to the destination type and back gives the tag.
    #[test]
    fn nonneg_tag_survival_matches_rust_as_semantics() {
        fn rust_as_preserves(tag: i128, width: u32, signed: bool) -> bool {
            let back: i128 = match (width, signed) {
                (8, true) => (tag as i8).into(),
                (8, false) => (tag as u8).into(),
                (16, true) => (tag as i16).into(),
                (16, false) => (tag as u16).into(),
                (32, true) => (tag as i32).into(),
                (32, false) => (tag as u32).into(),
                (64, true) => (tag as i64).into(),
                (64, false) => (tag as u64).into(),
                (128, true) => tag,
                (128, false) => match i128::try_from(tag as u128) {
                    Ok(v) => v,
                    Err(_) => return false,
                },
                _ => unreachable!("only real integer widths are probed"),
            };
            back == tag
        }
        let mut probes = vec![0i128, 1, i128::MAX, i128::MAX - 1];
        for bits in [7u32, 8, 15, 16, 31, 32, 63, 64] {
            let edge = 1i128 << bits;
            probes.extend([edge - 2, edge - 1, edge, edge + 1]);
        }
        for width in [8u32, 16, 32, 64, 128] {
            for signed in [false, true] {
                for &tag in &probes {
                    assert_eq!(
                        nonneg_tag_survives_int_cast(tag, width, signed),
                        rust_as_preserves(tag, width, signed),
                        "tag {tag} as {}{width}",
                        if signed { "i" } else { "u" }
                    );
                }
                // A negative tag never takes the identity, whatever the destination.
                assert!(!nonneg_tag_survives_int_cast(-1, width, signed));
            }
        }
        // Degenerate widths fail closed.
        assert!(!nonneg_tag_survives_int_cast(0, 0, false));
        assert!(!nonneg_tag_survives_int_cast(0, 129, true));
    }

    #[test]
    fn unsigned_shr_is_bounded_by_its_own_lhs() {
        // `x >> k <= x` for unsigned `x` — the RELATIONAL fact that makes the
        // safe-midpoint `low + ((high - low) >> 1)` Add provable, which the
        // constant `MAX >> k` bound cannot do. The fact is independent of the
        // shift AMOUNT (hence no `rhs` parameter): `floor(x / 2^k) <= x` for
        // every `k >= 0`. SIGNED shifts must decline — `-8 >> 1 == -4` and
        // `-4 <= -8` is false.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("sx".into()) },
        ];
        func.body.arg_count = 2;

        let x = Operand::Copy(Place::local(1));
        let sx = Operand::Copy(Place::local(2));
        let xf = operand_to_formula(&func, &x);
        let k = Operand::Constant(ConstValue::Uint(1, 32));
        let two = Operand::Constant(ConstValue::Uint(2, 32));
        let zero = Operand::Constant(ConstValue::Uint(0, 32));

        // Unsigned Shr → `dest <= x`.
        let rel = unsigned_floor_div_le_lhs(&func, &BinOp::Shr, &x, &k, "dest", xf.clone())
            .expect("unsigned Shr should be bounded by its LHS");
        assert!(
            matches!(&rel, Formula::Le(l, r)
                if l.var_name() == Some("dest") && r.var_name() == Some("x")),
            "got {rel:?}"
        );

        // Unsigned Div by a constant >= 1 is the SAME lemma (`x / 2 <= x`), so the
        // `/ 2` spelling of the safe-midpoint idiom proves too.
        let drel = unsigned_floor_div_le_lhs(&func, &BinOp::Div, &x, &two, "dest", xf.clone())
            .expect("unsigned Div by a positive constant should be bounded by its LHS");
        assert!(
            matches!(&drel, Formula::Le(l, r)
                if l.var_name() == Some("dest") && r.var_name() == Some("x")),
            "got {drel:?}"
        );

        // Div by a ZERO constant declines: the quotient is unconstrained in the model.
        assert!(
            unsigned_floor_div_le_lhs(&func, &BinOp::Div, &x, &zero, "dest", xf.clone()).is_none()
        );
        // Div by a VARIABLE divisor declines: it could be zero.
        assert!(
            unsigned_floor_div_le_lhs(&func, &BinOp::Div, &x, &x, "dest", xf.clone()).is_none()
        );

        // SIGNED declines for both ops — the fact is FALSE for negative values
        // (`-8 >> 1 == -4`, `-8 / 2 == -4`), so emitting it would be unsound.
        let sxf = operand_to_formula(&func, &sx);
        assert!(
            unsigned_floor_div_le_lhs(&func, &BinOp::Shr, &sx, &k, "dest", sxf.clone()).is_none()
        );
        assert!(unsigned_floor_div_le_lhs(&func, &BinOp::Div, &sx, &two, "dest", sxf).is_none());

        // Shl declines: `x << k` is not bounded above by `x`.
        assert!(unsigned_floor_div_le_lhs(&func, &BinOp::Shl, &x, &k, "dest", xf).is_none());

        // A self-assigning `x = x >> k` frame would render the vacuous `x <= x`.
        assert!(
            unsigned_floor_div_le_lhs(
                &func,
                &BinOp::Shr,
                &x,
                &k,
                "x",
                Formula::Var("x".into(), Sort::Int),
            )
            .is_none()
        );
    }

    #[test]
    fn shift_result_range_bounds_const_shr() {
        // `x >> k` for unsigned `x: uW` and constant `k < W` is bounded
        // above by `(2^W - 1) >> k`. soundness-signed-shift: a SIGNED `x >> k`
        // gets the two-sided `-(2^(W-1) >> k) <= dest <= (2^(W-1)-1) >> k`. Both are
        // gated to a constant `k < W`; `Shl`, a variable shift, and `k >= W` decline.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("sx".into()) },
        ];
        func.body.arg_count = 2;

        let x = Operand::Copy(Place::local(1));
        let sx = Operand::Copy(Place::local(2));
        let k = Operand::Constant(ConstValue::Uint(2, 32));

        // Unsigned Shr by const 2 → `dest <= (2^32-1) >> 2`.
        let bound = shift_result_range(
            &func,
            crate::operand_ty_cow(&func, &x).as_deref(),
            &BinOp::Shr,
            &x,
            &k,
            "dest",
            operand_to_formula(&func, &k),
        )
        .expect("unsigned const Shr should emit a bound");
        let expected = (u128::from(u32::MAX) >> 2) as i128; // 1_073_741_823
        assert!(
            matches!(&bound, Formula::Le(l, r)
                if l.var_name() == Some("dest")
                && matches!(r.as_ref(), Formula::Int(n) if *n == expected)),
            "got {bound:?}"
        );

        // Shl of a BARE full-width value (`x: u32`, no structural bound below the type max)
        // declines: the result could wrap, so there is no tight linear bound.
        assert!(
            shift_result_range(
                &func,
                crate::operand_ty_cow(&func, &x).as_deref(),
                &BinOp::Shl,
                &x,
                &k,
                "dest",
                operand_to_formula(&func, &k)
            )
            .is_none()
        );
        // Shl of a structurally-bounded LHS (here a non-negative constant `3`) by const `2`
        // CANNOT overflow u32, so it tightens to `dest <= 3 << 2 = 12` (#50 addend-side bound).
        let three_u32 = Operand::Constant(ConstValue::Uint(3, 32));
        let cbound = shift_result_range(
            &func,
            crate::operand_ty_cow(&func, &three_u32).as_deref(),
            &BinOp::Shl,
            &three_u32,
            &k,
            "dest",
            operand_to_formula(&func, &k),
        )
        .expect("Shl of a bounded LHS by a safe constant should emit a bound");
        assert!(
            matches!(&cbound, Formula::Le(l, r)
                if l.var_name() == Some("dest")
                && matches!(r.as_ref(), Formula::Int(n) if *n == 12)),
            "got {cbound:?}"
        );
        // Signed `>>` by const 2 → two-sided `-(2^31>>2) <= dest <= (2^31-1)>>2`,
        // i.e. `-536_870_912 <= dest <= 536_870_911` (sound now that signed shifts
        // bridge via bv2int_signed).
        let signed_bound = shift_result_range(
            &func,
            crate::operand_ty_cow(&func, &sx).as_deref(),
            &BinOp::Shr,
            &sx,
            &k,
            "dest",
            operand_to_formula(&func, &k),
        )
        .expect("signed const Shr should emit a two-sided bound");
        match &signed_bound {
            Formula::And(parts) if parts.len() == 2 => {
                assert!(
                    matches!(&parts[0], Formula::Le(l, r)
                        if matches!(l.as_ref(), Formula::Int(n) if *n == -536_870_912)
                        && r.var_name() == Some("dest")),
                    "lower bound wrong: {:?}",
                    parts[0]
                );
                assert!(
                    matches!(&parts[1], Formula::Le(l, r)
                        if l.var_name() == Some("dest")
                        && matches!(r.as_ref(), Formula::Int(n) if *n == 536_870_911)),
                    "upper bound wrong: {:?}",
                    parts[1]
                );
            }
            other => panic!("expected two-sided And bound, got {other:?}"),
        }
        // Variable shift → tightest sound bound is just the type max (useless).
        let var_k = Operand::Copy(Place::local(1));
        assert!(
            shift_result_range(
                &func,
                crate::operand_ty_cow(&func, &x).as_deref(),
                &BinOp::Shr,
                &x,
                &var_k,
                "dest",
                operand_to_formula(&func, &var_k)
            )
            .is_none()
        );
        // Shift amount >= width → a checked shift-overflow, must not pre-bound.
        let big_k = Operand::Constant(ConstValue::Uint(32, 32));
        assert!(
            shift_result_range(
                &func,
                crate::operand_ty_cow(&func, &x).as_deref(),
                &BinOp::Shr,
                &x,
                &big_k,
                "dest",
                operand_to_formula(&func, &big_k)
            )
            .is_none()
        );

        // Shl SOUNDNESS: a structurally-bounded LHS whose `base << k` would OVERFLOW the shift
        // type `W` must DECLINE (no bound) — emitting `dest <= base << k` would be unsound when
        // the W-bit shift modularly wraps. Here const `base = 2^30` shifted by `k = 5` gives
        // `2^35 > u32::MAX`, so the result could wrap; the bound is withheld.
        let big_base = Operand::Constant(ConstValue::Uint(1u128 << 30, 32));
        let k5 = Operand::Constant(ConstValue::Uint(5, 32));
        assert!(
            shift_result_range(
                &func,
                crate::operand_ty_cow(&func, &big_base).as_deref(),
                &BinOp::Shl,
                &big_base,
                &k5,
                "dest",
                operand_to_formula(&func, &k5)
            )
            .is_none(),
            "Shl whose base<<k overflows the shift width must not emit a bound"
        );
    }

    /// The shift DEFINITION and the shift RANGE must be stated at one width, and for
    /// a width-less `ConstValue::Int` that width comes from the destination. Pinned
    /// end-to-end on the real `signed_min` block shape, because the failure mode is
    /// not a wrong answer from either piece alone — it is the two DISAGREEING, which
    /// makes the hypotheses contradictory and vacuously proves everything.
    #[test]
    fn shift_def_and_range_agree_on_the_destination_width() {
        fn assign(i: usize, r: Rvalue) -> Statement {
            Statement::Assign { place: Place::local(i), rvalue: r, span: SourceSpan::default() }
        }
        // bb: _6 = width - 1; _5 = Shl(1i128, _6); _0 = -_5   (trust_semantics::signed_min)
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::i128(), name: Some("_0".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("width".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("_2".into()) },
            LocalDecl { index: 3, ty: Ty::i128(), name: Some("_3".into()) },
            LocalDecl { index: 4, ty: Ty::i128(), name: Some("_4".into()) },
            LocalDecl { index: 5, ty: Ty::i128(), name: Some("_5".into()) },
            LocalDecl { index: 6, ty: Ty::u32(), name: Some("_6".into()) },
        ];
        func.body.arg_count = 1;
        func.body.return_ty = Ty::i128();
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(
                    6,
                    Rvalue::BinaryOp(
                        BinOp::Sub,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(1, 32)),
                    ),
                ),
                assign(
                    5,
                    Rvalue::BinaryOp(
                        BinOp::Shl,
                        Operand::Constant(ConstValue::Int(1)),
                        Operand::Move(Place::local(6)),
                    ),
                ),
                assign(0, Rvalue::UnaryOp(trust_types::UnOp::Neg, Operand::Copy(Place::local(5)))),
            ],
            terminator: Terminator::Return,
        }];

        // The bare operand type is the FABRICATED i64 — this is the defect being repaired,
        // pinned so the test still means something if `operand_ty`'s inference changes.
        assert_eq!(
            crate::operand_ty(&func, &Operand::Constant(ConstValue::Int(1))),
            Some(Ty::Int { width: 64, signed: true }),
            "a width-less signed literal is inferred i64; that is what makes the repair necessary"
        );
        assert_eq!(
            shift_result_ty_from_dest(
                &func,
                &Place::local(5),
                &BinOp::Shl,
                &Operand::Constant(ConstValue::Int(1)),
            ),
            Some(Ty::Int { width: 128, signed: true }),
            "the destination `_5: i128` carries the shift's real result type"
        );

        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        let mut saw_def_at_128 = false;
        let mut saw_range_k126 = false;
        for d in &defs {
            if let Formula::Eq(l, r) = d
                && l.var_name() == Some("_5")
                && let Formula::BvToInt(_, w, true) = r.as_ref()
            {
                assert_eq!(*w, 128, "the shift DEF must use the destination width, got {w}");
                saw_def_at_128 = true;
            }
            if let Formula::Implies(ante, _) = d
                && let Formula::And(parts) = ante.as_ref()
                && parts.len() == 2
                && matches!(&parts[1], Formula::Le(_, r) if matches!(r.as_ref(), Formula::Int(126)))
            {
                saw_range_k126 = true;
            }
        }
        assert!(saw_def_at_128, "no width-128 shift definition for `_5` in {defs:?}");
        // K = 126, not 62. 62 is what the fabricated i64 width yields, and it is
        // UNREACHABLE from the program's own `width <= 127` guard, so the fact would
        // be sound and permanently inert — the silent-failure mode this pins against.
        assert!(saw_range_k126, "no conditional range with K=126 in {defs:?}");

        // The repair is DELIBERATELY narrow: a width-CARRYING operand keeps its own
        // type even when the destination disagrees, because there the operand type is
        // a fact and the override would be a reinterpretation.
        assert_eq!(
            shift_result_ty_from_dest(
                &func,
                &Place::local(5),
                &BinOp::Shl,
                &Operand::Constant(ConstValue::Uint(1, 32)),
            ),
            None,
            "a width-carrying constant must not be re-typed from the destination"
        );
        assert_eq!(
            shift_result_ty_from_dest(
                &func,
                &Place::local(5),
                &BinOp::Shl,
                &Operand::Copy(Place::local(1))
            ),
            None,
            "a local operand must not be re-typed from the destination"
        );
        // Non-shift ops are untouched: `Sub` keeps `operand_ty`'s answer.
        assert_eq!(
            shift_result_ty_from_dest(
                &func,
                &Place::local(5),
                &BinOp::Sub,
                &Operand::Constant(ConstValue::Int(1)),
            ),
            None,
            "only shifts recover their width from the destination"
        );
    }

    /// `1i128 << width` — a signed constant LHS shifted by a VARIABLE amount, the
    /// type-extremum idiom in `trust_semantics::signed_min`/`signed_max`/
    /// `type_max_formula`. The bound is CONDITIONAL on the amount, and the whole
    /// soundness argument is which amounts the antecedent lets in.
    #[test]
    fn variable_shl_emits_conditional_range_and_stops_at_the_sign_bit() {
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::i128(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("width".into()) },
        ];
        func.body.arg_count = 1;

        let one_i128 = Operand::Constant(ConstValue::Int(1));
        let amt = Operand::Copy(Place::local(1));
        let amt_f = operand_to_formula(&func, &amt);

        // `1i128 << width` (signed lhs, variable amount) now emits a bound where the
        // old gate emitted nothing at all.
        // The caller resolves the shift's result type; for a width-less
        // `ConstValue::Int` that is the DESTINATION's type, recovered by
        // `shift_result_ty_from_dest` (pinned by its own test below).
        let i128_ty = Ty::i128();
        let bound = shift_result_range(
            &func,
            Some(&i128_ty),
            &BinOp::Shl,
            &one_i128,
            &amt,
            "dest",
            amt_f.clone(),
        )
        .expect("signed constant lhs with a variable amount should emit a conditional bound");

        // Shape: `(0 <= amt AND amt <= K) => (1 <= dest AND dest <= 2^K)`.
        //
        // K MUST be 126, not 127. This is the negative half of the fixture and the
        // whole point: `1i128 << 127` IS `i128::MIN`, so a K of 127 would license
        // `dest >= 1` on an amount that really does produce the most negative value,
        // and the consuming `-dest` / `dest - 1` would then FALSE-PROVE.
        let (ante, cons) = match &bound {
            Formula::Implies(a, c) => (a.as_ref(), c.as_ref()),
            other => panic!("expected an IMPLICATION, got {other:?}"),
        };
        match ante {
            Formula::And(parts) if parts.len() == 2 => {
                assert!(
                    matches!(&parts[0], Formula::Le(l, _)
                        if matches!(l.as_ref(), Formula::Int(0))),
                    "antecedent must exclude a NEGATIVE amount (bvshl would yield 0 there): {:?}",
                    parts[0]
                );
                assert!(
                    matches!(&parts[1], Formula::Le(_, r)
                        if matches!(r.as_ref(), Formula::Int(126))),
                    "antecedent must stop at K=126 — 1i128 << 127 is i128::MIN: {:?}",
                    parts[1]
                );
            }
            other => panic!("expected a two-conjunct antecedent, got {other:?}"),
        }
        match cons {
            Formula::And(parts) if parts.len() == 2 => {
                assert!(
                    matches!(&parts[0], Formula::Le(l, r)
                        if matches!(l.as_ref(), Formula::Int(1)) && r.var_name() == Some("dest")),
                    "lower bound must be `1 <= dest` (that is what discharges `-dest`/`dest-1`): {:?}",
                    parts[0]
                );
                assert!(
                    matches!(&parts[1], Formula::Le(l, r)
                        if l.var_name() == Some("dest")
                        && matches!(r.as_ref(), Formula::Int(n) if *n == (1i128 << 126))),
                    "upper bound must be 2^126: {:?}",
                    parts[1]
                );
            }
            other => panic!("expected a two-conjunct consequent, got {other:?}"),
        }

        // NEGATIVE FIXTURE 1 — a base that genuinely overflows before the sign bit.
        // `3i128 << k` reaches `3 * 2^126 > i128::MAX` at k = 126, so K must be 125.
        // A K of 126 here would be a range that is FALSE of the real machine value.
        let three = Operand::Constant(ConstValue::Int(3));
        let b3 = shift_result_range(
            &func,
            Some(&i128_ty),
            &BinOp::Shl,
            &three,
            &amt,
            "dest",
            amt_f.clone(),
        )
        .expect("base 3 still has a non-empty safe amount window");
        match &b3 {
            Formula::Implies(a, _) => match a.as_ref() {
                Formula::And(parts) => assert!(
                    matches!(&parts[1], Formula::Le(_, r)
                        if matches!(r.as_ref(), Formula::Int(125))),
                    "base 3 must stop at K=125 (3*2^126 > i128::MAX): {:?}",
                    parts[1]
                ),
                other => panic!("{other:?}"),
            },
            other => panic!("{other:?}"),
        }

        // NEGATIVE FIXTURE 2 — an UNSIGNED lhs takes the same lane and gets the
        // strictly larger window, because there is no sign bit to protect:
        // `1u128 << 127` is a perfectly ordinary u128 value, so K is 127.
        // Sharing one code path between the two would silently license the signed
        // sign-bit case; this pins that they differ by exactly one.
        let mut ufunc = test_func();
        ufunc.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u128(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("width".into()) },
        ];
        ufunc.body.arg_count = 1;
        let one_u128 = Operand::Constant(ConstValue::Uint(1, 128));
        let ub = shift_result_range(
            &ufunc,
            Some(&Ty::u128()),
            &BinOp::Shl,
            &one_u128,
            &amt,
            "dest",
            amt_f.clone(),
        )
        .expect("unsigned constant lhs with a variable amount should emit a bound");
        match &ub {
            Formula::Implies(a, _) => match a.as_ref() {
                Formula::And(parts) => assert!(
                    matches!(&parts[1], Formula::Le(_, r)
                        if matches!(r.as_ref(), Formula::Int(127))),
                    "unsigned u128 has no sign bit, so K is 127: {:?}",
                    parts[1]
                ),
                other => panic!("{other:?}"),
            },
            other => panic!("{other:?}"),
        }

        // NEGATIVE FIXTURE 3 — a VARIABLE lhs must still decline. `x << k` for an
        // unconstrained `x` has no sound range at all, and the conditional lane must
        // not manufacture one just because the amount is now handled.
        let var_lhs = Operand::Copy(Place::local(1));
        assert!(
            shift_result_range(
                &func,
                Some(&i128_ty),
                &BinOp::Shl,
                &var_lhs,
                &amt,
                "dest",
                amt_f.clone()
            )
            .is_none(),
            "a variable LHS has no sound conditional range"
        );

        // NEGATIVE FIXTURE 4 — a lhs that already EXCEEDS the signed ceiling declines
        // outright rather than emitting an empty-window bound.
        let huge = Operand::Constant(ConstValue::Uint(u128::MAX, 128));
        assert!(
            shift_result_range(
                &func,
                Some(&i128_ty),
                &BinOp::Shl,
                &huge,
                &amt,
                "dest",
                amt_f.clone()
            )
            .is_none(),
            "a lhs above the type ceiling must decline"
        );

        // NEGATIVE FIXTURE 5 — `0 << k` declines: the fact would be true but carries
        // no usable lower bound, and `K` is unbounded.
        let zero = Operand::Constant(ConstValue::Int(0));
        assert!(
            shift_result_range(&func, Some(&i128_ty), &BinOp::Shl, &zero, &amt, "dest", amt_f)
                .is_none(),
            "a zero lhs must decline"
        );
    }

    #[test]
    fn shared_ref_connects_deref_to_referent() {
        // a match-guard binding lowers by reference (`r = &payload`;
        // the guard tests `*r`) while the arm reads the payload by value. The
        // shared borrow must emit `*r == payload` (`r* == p`) so the guard
        // constrains the same value the arm uses — otherwise `*r` is a free
        // variable and a guarded binding (`Some(v) if v < K => v + 1`)
        // false-fails.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("p".into()) },
            LocalDecl {
                index: 2,
                ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                name: Some("r".into()),
            },
        ];
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }];

        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        let connects = defs.iter().any(|f| {
            matches!(f, Formula::Eq(lhs, rhs)
                if lhs.var_name() == Some("r*") && rhs.var_name() == Some("p"))
        });
        assert!(connects, "shared ref must emit `r* == p`, got: {defs:?}");
    }

    #[test]
    fn mut_ref_does_not_emit_deref_equality() {
        // `&mut` is deliberately skipped: a later `*r = ..` could invalidate
        // `*r == referent`, so emitting the equality would be unsound.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("p".into()) },
            LocalDecl {
                index: 2,
                ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                name: Some("r".into()),
            },
        ];
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }];

        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        assert!(
            !defs.iter().any(|f| matches!(f, Formula::Eq(lhs, _) if lhs.var_name() == Some("r*"))),
            "&mut must not emit a deref equality, got: {defs:?}"
        );
    }

    #[test]
    fn mut_ref_slice_reborrow_ties_length() {
        // `r = &mut (*s)` for `s: &mut [u8]` — the shape a guarded
        // `if i < s.len() { *s.get_unchecked_mut(i) = v }` lowers to (the receiver
        // is a fresh `&mut (*s)` reborrow) — must tie the reborrow's `__slice_len`
        // to the source's, so the guard's `s.len()` discharges the bounds
        // obligation. SOUND: a slice's LENGTH is immutable through `&mut [T]`
        // (only its elements are). Regression lock for the get_unchecked_mut fix.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl {
                index: 1,
                ty: Ty::Ref {
                    mutable: true,
                    inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
                },
                name: Some("s".into()),
            },
            LocalDecl {
                index: 2,
                ty: Ty::Ref {
                    mutable: true,
                    inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
                },
                name: Some("r".into()),
            },
        ];
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Ref {
                    mutable: true,
                    place: Place { local: 1, projections: vec![trust_types::Projection::Deref] },
                },
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }];

        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        // The length tie `r__slice_len == s__slice_len` must now be present.
        assert!(
            defs.iter().any(|f| matches!(f, Formula::Eq(lhs, rhs)
                if lhs.var_name() == Some("r__slice_len") && rhs.var_name() == Some("s__slice_len"))),
            "&mut slice reborrow must tie length `r__slice_len == s__slice_len`, got: {defs:?}"
        );
        // ...but it must STILL NOT emit the deref-VALUE equality (unsound for &mut).
        assert!(
            !defs.iter().any(|f| matches!(f, Formula::Eq(lhs, _) if lhs.var_name() == Some("r*"))),
            "&mut must not emit a deref-value equality even while tying length, got: {defs:?}"
        );
    }

    /// The length formula an array→slice cast ties its destination to, if any.
    /// `_2` is `single_cast_func`'s destination local, so the tie is on
    /// `_2__slice_len`.
    fn cast_slice_len_tie(src_ty: Ty, dst_ty: Ty) -> Option<Formula> {
        let func = single_cast_func(src_ty, dst_ty);
        extract_block_definitions(&func, &func.body.blocks[0]).into_iter().find_map(|f| match f {
            Formula::Eq(lhs, rhs) if lhs.var_name() == Some("_2__slice_len") => Some(*rhs),
            _ => None,
        })
    }

    #[test]
    fn array_unsize_cast_ties_the_static_length() {
        // `_2 = _1 as &[u8]` for `_1: &[u8; 8]` — the array→slice coercion. Without
        // the tie `_2__slice_len` is free and `a.len() - 1` refutes at length 0.
        let tie = cast_slice_len_tie(
            Ty::Ref {
                mutable: false,
                inner: Box::new(Ty::Array { elem: Box::new(Ty::u8()), len: 8 }),
            },
            Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) },
        );
        assert_eq!(
            tie,
            Some(Formula::Int(8)),
            "`&[u8; 8] -> &[u8]` must tie the destination's length to the array's 8"
        );

        // `&mut [T; N] -> &mut [T]` carries the same N: a reborrow cannot change a
        // length. Raw pointers unsize the same way (`*const [T; N] -> *const [T]`).
        assert_eq!(
            cast_slice_len_tie(
                Ty::Ref {
                    mutable: true,
                    inner: Box::new(Ty::Array { elem: Box::new(Ty::u32()), len: 3 })
                },
                Ty::Ref { mutable: true, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u32()) }) },
            ),
            Some(Formula::Int(3)),
            "`&mut [u32; 3] -> &mut [u32]` must tie length 3"
        );
        assert_eq!(
            cast_slice_len_tie(
                Ty::RawPtr {
                    mutable: false,
                    pointee: Box::new(Ty::Array { elem: Box::new(Ty::u8()), len: 0 })
                },
                Ty::RawPtr {
                    mutable: false,
                    pointee: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
                },
            ),
            Some(Formula::Int(0)),
            "`*const [u8; 0] -> *const [u8]` must tie length 0 — the EXACT length, \
             including the empty case that makes `100 / a.len()` genuinely divide by zero"
        );
    }

    #[test]
    fn const_generic_array_unsize_cast_ties_the_param_symbol() {
        // `&[u8; N] -> &[u8]` for a const-generic `N`: the tie must name the SAME
        // per-param symbol a bare `[T; N]` resolves to (`sym_array_len_formula`), so
        // a guard written against `N` and a bound that came through the coercion
        // share one variable.
        let len_sym = trust_types::ConstLen { index: 0, name: "N".into() };
        let tie = cast_slice_len_tie(
            Ty::Ref {
                mutable: false,
                inner: Box::new(Ty::SymArray {
                    elem: Box::new(Ty::u8()),
                    len_sym: len_sym.clone(),
                }),
            },
            Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) },
        );
        assert_eq!(
            tie,
            Some(crate::sym_array_len_formula(&len_sym)),
            "`&[u8; N] -> &[u8]` must tie the const-param symbol, not a fresh variable"
        );
    }

    #[test]
    fn elem_changing_pointer_cast_does_not_tie_length() {
        // TrustIR's `Rvalue::Cast` is the same variant used for `PtrToPtr`, so the
        // array→slice tie must not fire on a cast that CHANGES the element type.
        // `*const [u32; 4] -> *const [u8]` would preserve the metadata VALUE 4 while
        // the metadata now counts BYTES, so claiming `len == 4` for the destination
        // is not a fact about the program. Fail closed: emit nothing.
        assert_eq!(
            cast_slice_len_tie(
                Ty::RawPtr {
                    mutable: false,
                    pointee: Box::new(Ty::Array { elem: Box::new(Ty::u32()), len: 4 })
                },
                Ty::RawPtr {
                    mutable: false,
                    pointee: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) })
                },
            ),
            None,
            "a cast whose element type changes must NOT tie the destination's length"
        );
        // A source that is ALREADY a slice carries no STATIC length, but a fat→fat
        // cast copies its metadata (2026-10-08, `push_cast_slice_len`), so the
        // destination is tied to the SOURCE's own length name, never to a constant.
        assert_eq!(
            cast_slice_len_tie(
                Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) },
                Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) },
            ),
            Some(Formula::var_owned("x__slice_len".to_string(), Sort::Int)),
            "a slice→slice cast ties the destination to the source's metadata"
        );
        // An int→int cast is the overwhelmingly common `Rvalue::Cast` and must be
        // untouched by the slice-length lane.
        assert_eq!(
            cast_slice_len_tie(Ty::u32(), Ty::u64()),
            None,
            "an int→int cast must not emit a slice-length fact"
        );
    }

    /// True when `defs` contains an `input_range_constraint`-shaped fact bounding
    /// `var` from both sides (a lower `Le(_, var)` and an upper `Le(var, _)`).
    fn has_range_bound_on(defs: &[Formula], var: &str) -> bool {
        defs.iter().any(|f| {
            matches!(f, Formula::And(cs)
                if cs.iter().any(|c| matches!(c, Formula::Le(_, v) if v.var_name() == Some(var)))
                && cs.iter().any(|c| matches!(c, Formula::Le(v, _) if v.var_name() == Some(var))))
        })
    }

    fn single_cast_func(src_ty: Ty, dst_ty: Ty) -> VerifiableFunction {
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: dst_ty.clone(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: src_ty, name: Some("x".into()) },
            LocalDecl { index: 2, ty: dst_ty.clone(), name: None },
        ];
        func.body.arg_count = 1;
        func.body.return_ty = dst_ty.clone();
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), dst_ty),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }];
        func
    }

    /// The snapshot-transport write set must name the derived slice-length of a
    /// destination whose RVALUE definition extraction declines.
    ///
    /// `conservative_snapshot_writes` exists because extraction is partial: it
    /// starts from `generate::block_written_names` (which derives `{d}__slice_len`
    /// from the def names it CAN mint) and then adds every explicit place
    /// destination as a belt-and-suspenders gate. A dest reaching the loop is by
    /// construction one that produced no definition, so its derived name reaches
    /// the set through this site or not at all — and a proof snapshot transported
    /// across it would keep a length tie the write replaced.
    ///
    /// `Rvalue::Unsupported` is the extraction-declining shape here; the property
    /// is about the DEST, not about that particular rvalue.
    #[test]
    fn snapshot_writes_name_the_derived_slice_len_of_an_unextractable_dest() {
        let slice_ref =
            Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) };
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
            LocalDecl { index: 1, ty: slice_ref.clone(), name: Some("s".into()) },
        ];
        func.body.arg_count = 1;
        func.body.return_ty = Ty::Unit;
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Unsupported {
                    kind: "test".into(),
                    detail: "extraction declines this rvalue".into(),
                    operands: vec![],
                },
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }];
        let writes = conservative_snapshot_writes(&func, &func.body.blocks[0])
            .expect("an Assign statement surface is value-transparent");
        assert!(writes.contains("s"), "the written dest must be reported; got {writes:?}");
        assert!(
            writes.contains("s__slice_len"),
            "writing the whole slice reference replaces its length metadata, so the \
             snapshot write set must name `s__slice_len`; got {writes:?}"
        );
    }

    #[test]
    fn widening_unsigned_cast_bounds_result_by_source_width() {
        // `(x as u64)` for `x: u32` must emit `0 <= dest <= 2^32-1` on the
        // cast result, not merely `dest == x`. Without this, when the cast source has
        // no independent range bound (a #51-extracted struct-payload field), the
        // widened u64 reads as a free variable and a safe `(p.x as u64)+(p.y as u64)`
        // false-FAILs. The bound is a value-preserving-widening tautology, so sound.
        let func = single_cast_func(Ty::u32(), Ty::u64());
        let dest = crate::place_to_var_name(&func, &Place::local(2));
        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        let upper = (1i128 << 32) - 1;
        let bounded = defs.iter().any(|f| {
            matches!(f, Formula::And(cs)
                if cs.iter().any(|c| matches!(c, Formula::Le(_, v) if v.var_name() == Some(dest.as_str())))
                && cs.iter().any(|c| matches!(c,
                    Formula::Le(v, hi) if v.var_name() == Some(dest.as_str())
                        && matches!(hi.as_ref(), Formula::Int(n) if *n == upper))))
        });
        assert!(
            bounded,
            "widening u32->u64 cast must bound result `{dest}` to [0, 2^32-1], got: {defs:?}"
        );
    }

    #[test]
    fn widened_operand_source_range_rejects_reassigned_cast_local() {
        // The first definition says `w` came from a u8, but the second gives it
        // a legal u16 value far outside the u8 range. A whole-function first-cast
        // scan must not inject the stale `w <= 255` fact into a later checked op.
        let mut func = single_cast_func(Ty::u8(), Ty::u16());
        func.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(60_000, 16))),
            span: SourceSpan::default(),
        });
        assert!(
            widening_operand_source_range(&func, &Operand::Copy(Place::local(2))).is_none(),
            "a reassigned widened local must not retain its first cast's source range"
        );
    }

    #[test]
    fn narrowing_cast_emits_target_type_range_not_source_width() {
        // u64 -> u32 is a truncating (defined) cast — no CastOverflow VC. It is
        // type-tracked: the result is a u32, so `0 <= dest <= u32::MAX` is emitted
        // (the TARGET-type range), NOT the meaningless source-width (u64) range.
        let func = single_cast_func(Ty::u64(), Ty::u32());
        let dest = crate::place_to_var_name(&func, &Place::local(2));
        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        assert!(
            has_range_bound_on(&defs, &dest),
            "narrowing cast must type-track its result with the target-type range on \
             `{dest}`, got: {defs:?}"
        );
        // The upper bound must be the TARGET max (u32::MAX = 4_294_967_295), proving
        // it is the sound target-type range and not the source-width (u64) range.
        let has_u32_max = defs.iter().any(|f| {
            matches!(f, Formula::And(cs) if cs.iter().any(|c| matches!(c,
                Formula::Le(v, hi)
                    if v.var_name() == Some(dest.as_str())
                    && matches!(hi.as_ref(), Formula::Int(n) if *n == u32::MAX as i128))))
        });
        assert!(
            has_u32_max,
            "narrowing cast result must be bounded by the TARGET max (u32::MAX), not the \
             source-width max: {defs:?}"
        );
    }

    // ----- VC-NARROW-CAST-FALSE-REFUTE-1 (2026-10-11) -----
    //
    // A narrowing cast's result was a FREE value of its target type (only the range
    // above), so `arr[x as u8 as usize]` under `x < 0x80` was refuted at 128. The Cast
    // arm now also emits `narrowing_cast_in_range_identity`. Real-MIR twin:
    // `tests/narrowing_cast_identity_realmir.rs`.

    /// The `(lo <= src && src <= hi) => dest == src` fact `narrowing_cast_in_range_identity`
    /// emits, as `(lo, hi)`, when `defs` carries one for `dest`/`src`. `lo` is `None` for
    /// the unsigned-source shape `src <= hi => dest == src`, whose antecedent is one atom.
    fn in_range_identity_bounds(
        defs: &[Formula],
        dest: &str,
        src: &str,
    ) -> Option<(Option<i128>, i128)> {
        defs.iter().find_map(|f| {
            let Formula::Implies(ante, cons) = f else { return None };
            let Formula::Eq(l, r) = cons.as_ref() else { return None };
            if l.var_name() != Some(dest) || r.var_name() != Some(src) {
                return None;
            }
            let atoms: Vec<&Formula> = match ante.as_ref() {
                Formula::And(cs) => cs.iter().collect(),
                single => vec![single],
            };
            let constant = |k: &Formula| match k {
                Formula::Int(n) => Some(*n),
                _ => None,
            };
            let lo = atoms.iter().find_map(|c| match c {
                Formula::Ge(v, k) if v.var_name() == Some(src) => constant(k),
                _ => None,
            });
            let hi = atoms.iter().find_map(|c| match c {
                Formula::Le(v, k) if v.var_name() == Some(src) => constant(k),
                _ => None,
            })?;
            Some((lo, hi))
        })
    }

    /// FAILS BEFORE: no implication was emitted for any of these casts.
    #[test]
    fn narrowing_cast_emits_the_in_range_identity() {
        // An unsigned source carries the upper bound alone (`lo` is `None`): its lower
        // bound `0 >= to_min` is the source type's own fact.
        for (src_ty, dst_ty, lo, hi) in [
            (Ty::u32(), Ty::u8(), None, 255),
            (Ty::u32(), Ty::u16(), None, i128::from(u16::MAX)),
            (Ty::u64(), Ty::u32(), None, i128::from(u32::MAX)),
            (Ty::i32(), Ty::u8(), Some(0), 255),
            (Ty::i32(), Ty::i16(), Some(i128::from(i16::MIN)), i128::from(i16::MAX)),
            (Ty::u16(), Ty::i8(), None, 127),
            (Ty::u128(), Ty::u64(), None, i128::from(u64::MAX)),
            (Ty::i128(), Ty::i64(), Some(i128::from(i64::MIN)), i128::from(i64::MAX)),
            // Same-width UNSIGNED -> SIGNED reinterpret: identity below the sign bit.
            (Ty::u32(), Ty::i32(), None, i128::from(i32::MAX)),
            (Ty::u128(), Ty::i128(), None, i128::MAX),
        ] {
            let func = single_cast_func(src_ty.clone(), dst_ty.clone());
            let dest = crate::place_to_var_name(&func, &Place::local(2));
            let src = crate::place_to_var_name(&func, &Place::local(1));
            let defs = extract_block_definitions(&func, &func.body.blocks[0]);
            assert_eq!(
                in_range_identity_bounds(&defs, &dest, &src),
                Some((lo, hi)),
                "`{src_ty:?} as {dst_ty:?}` must emit `({lo:?} <= {src} <= {hi}) => {dest} == \
                 {src}`, got: {defs:?}"
            );
            assert!(
                has_range_bound_on(&defs, &dest),
                "`{src_ty:?} as {dst_ty:?}`: the target-type range must still be emitted: {defs:?}"
            );
        }
    }

    /// The identity's bounds are exactly the source values Rust's `as` leaves unchanged,
    /// checked against the compiler's own casts: both bounds are preserved, and one step
    /// outside either bound (where the source type has that value) is moved.
    #[test]
    fn the_in_range_identity_bounds_are_exactly_what_as_preserves() {
        type Cast = fn(i128) -> i128;
        let cases: [(Ty, Ty, (i128, i128), Cast); 6] = [
            (Ty::u32(), Ty::u8(), (0, i128::from(u32::MAX)), |v| i128::from(v as u32 as u8)),
            (Ty::i32(), Ty::u8(), (i128::from(i32::MIN), i128::from(i32::MAX)), |v| {
                i128::from(v as i32 as u8)
            }),
            (Ty::i32(), Ty::i16(), (i128::from(i32::MIN), i128::from(i32::MAX)), |v| {
                i128::from(v as i32 as i16)
            }),
            (Ty::u64(), Ty::u32(), (0, i128::from(u64::MAX)), |v| i128::from(v as u64 as u32)),
            (Ty::u16(), Ty::i8(), (0, i128::from(u16::MAX)), |v| i128::from(v as u16 as i8)),
            (Ty::u32(), Ty::i32(), (0, i128::from(u32::MAX)), |v| i128::from(v as u32 as i32)),
        ];
        for (src_ty, dst_ty, (src_min, src_max), cast) in cases {
            let func = single_cast_func(src_ty.clone(), dst_ty.clone());
            let dest = crate::place_to_var_name(&func, &Place::local(2));
            let src = crate::place_to_var_name(&func, &Place::local(1));
            let defs = extract_block_definitions(&func, &func.body.blocks[0]);
            let (lo, hi) = in_range_identity_bounds(&defs, &dest, &src)
                .unwrap_or_else(|| panic!("`{src_ty:?} as {dst_ty:?}`: no identity in {defs:?}"));
            let lo = lo.unwrap_or(src_min).max(src_min);
            assert_eq!(cast(lo), lo, "`{src_ty:?} as {dst_ty:?}` moves {lo}");
            assert_eq!(cast(hi), hi, "`{src_ty:?} as {dst_ty:?}` moves {hi}");
            for outside in [lo - 1, hi + 1] {
                if (src_min..=src_max).contains(&outside) {
                    assert_ne!(
                        cast(outside),
                        outside,
                        "`{src_ty:?} as {dst_ty:?}` preserves {outside}: the bound is not tight"
                    );
                }
            }
        }
    }

    /// Widening, same-type and signed->unsigned same-width casts have their own exact
    /// relation (or a value-preserving identity), and a constant source has the constant
    /// arm: none of them gets the implication.
    #[test]
    fn non_narrowing_casts_and_constants_emit_no_in_range_identity() {
        for (src_ty, dst_ty) in [
            (Ty::u8(), Ty::u32()),
            (Ty::u8(), Ty::u64()),
            (Ty::i8(), Ty::i32()),
            (Ty::u32(), Ty::u64()),
            (Ty::u32(), Ty::i64()),
            (Ty::u32(), Ty::u32()),
            (Ty::i32(), Ty::i32()),
            (Ty::i32(), Ty::u32()),
            (Ty::i8(), Ty::u8()),
            (Ty::i32(), Ty::u64()),
        ] {
            let func = single_cast_func(src_ty.clone(), dst_ty.clone());
            let defs = extract_block_definitions(&func, &func.body.blocks[0]);
            assert!(
                !defs.iter().any(|f| matches!(f, Formula::Implies(..))),
                "`{src_ty:?} as {dst_ty:?}` must not emit the narrowing identity: {defs:?}"
            );
        }
        let mut func = single_cast_func(Ty::u32(), Ty::u8());
        let Statement::Assign { rvalue, .. } = &mut func.body.blocks[0].stmts[0] else {
            unreachable!("single_cast_func builds one Assign")
        };
        *rvalue = Rvalue::Cast(Operand::Constant(ConstValue::Uint(300, 32)), Ty::u8());
        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        assert!(
            !defs.iter().any(|f| matches!(f, Formula::Implies(..))),
            "a constant source is the constant arm's: {defs:?}"
        );
    }

    /// SOUNDNESS: the identity names the source AT the cast. `b = x as u8; x = 0;` — a
    /// later write of the source makes it stale (it would tie `b` to the NEW `x`, and a
    /// guard on the new value would bound `b`), so it must be dropped; the range on `b`,
    /// which mentions only `b`, stays.
    #[test]
    fn the_in_range_identity_is_dropped_when_its_source_is_rewritten() {
        let mut func = single_cast_func(Ty::u32(), Ty::u8());
        func.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
            span: SourceSpan::default(),
        });
        let dest = crate::place_to_var_name(&func, &Place::local(2));
        let src = crate::place_to_var_name(&func, &Place::local(1));
        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        assert_eq!(
            in_range_identity_bounds(&defs, &dest, &src),
            None,
            "a rewritten source must drop the identity: {defs:?}"
        );
        assert!(has_range_bound_on(&defs, &dest), "the target range stays: {defs:?}");
    }

    #[test]
    fn signed_to_unsigned_widening_cast_does_not_emit_source_range() {
        // SOUNDNESS: i32 -> u64 sign-extends then reinterprets, so a negative source
        // wraps to a huge unsigned value — the signed source-width range would be
        // FALSE and could false-PROVE a real overflow. Must be skipped.
        let func = single_cast_func(Ty::i32(), Ty::u64());
        let dest = crate::place_to_var_name(&func, &Place::local(2));
        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        assert!(
            !has_range_bound_on(&defs, &dest),
            "signed->unsigned widening must not emit a source range on `{dest}`, got: {defs:?}"
        );
    }

    #[test]
    fn def_with_operand_overwritten_later_in_block_is_dropped() {
        // SOUNDNESS: `c = m < 1000; m = BIG;` must NOT leave `c == (m < 1000)` in
        // the block's defs — that fact describes the *post*-`m = BIG` value of `m`,
        // which is wrong. A later `if c { m + 1 }` would then carry the
        // contradictory hypotheses {c == true, c == (m < 1000), m == BIG} and
        // vacuously prove the overflow safe (a false-PROVE of a real overflow).
        // Same-destination last-write dedup does not catch this: the stale fact's
        // destination is `c`, but its *operand* `m` is what gets overwritten.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("m".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("big".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("c".into()) },
        ];
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(1000)),
                    ),
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                    span: SourceSpan::default(),
                },
            ],
            terminator: Terminator::Return,
        }];

        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        // The live reassignment of `m` survives.
        assert!(
            defs.iter().any(|f| matches!(f, Formula::Eq(lhs, rhs)
                if lhs.var_name() == Some("m") && rhs.var_name() == Some("big"))),
            "live `m == big` must survive, got: {defs:?}"
        );
        // The stale comparison over the overwritten `m` must be gone.
        assert!(
            !defs.iter().any(|f| matches!(f, Formula::Eq(lhs, _) if lhs.var_name() == Some("c"))),
            "stale `c == (m < 1000)` must be dropped once `m` is overwritten, got: {defs:?}"
        );
    }

    #[test]
    fn def_with_operand_not_overwritten_survives() {
        // Precision guard: when the operand is NOT reassigned later, the
        // comparison def must survive (otherwise every guard would be dropped).
        // `c = m < 1000;` with no later write to `m` keeps `c == (m < 1000)`.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("m".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("c".into()) },
        ];
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Lt,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Int(1000)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }];

        let defs = extract_block_definitions(&func, &func.body.blocks[0]);
        assert!(
            defs.iter().any(|f| matches!(f, Formula::Eq(lhs, _) if lhs.var_name() == Some("c"))),
            "live `c == (m < 1000)` must survive when `m` is not overwritten, got: {defs:?}"
        );
    }

    #[test]
    fn test_guard_switch_int_match_to_formula() {
        let func = test_func();
        let guard =
            GuardCondition::SwitchIntMatch { discr: Operand::Copy(Place::local(1)), value: 42 };
        let formula = guard_to_formula(&func, &guard);
        // Match both Var and SymVar via var_name().
        assert!(
            matches!(&formula, Formula::Eq(lhs, rhs)
                if lhs.var_name() == Some("x")
                && matches!(rhs.as_ref(), Formula::Int(42))
            ),
            "SwitchIntMatch should produce discr == value, got: {formula:?}"
        );
    }

    #[test]
    fn refutation_guard_rejects_an_undecodable_switch_label_instead_of_dropping_it() {
        let func = test_func();
        let guard = GuardCondition::SwitchIntMatch {
            discr: Operand::Copy(Place::local(1)),
            value: 1u128 << 40,
        };
        assert!(
            matches!(guard_to_formula(&func, &guard), Formula::Bool(true)),
            "the proof-facing lane deliberately weakens an undecodable u32 label"
        );
        assert!(
            guard_to_refutation_formula(&func, &guard).is_none(),
            "the same weakening must never enter a SAT-as-counterexample lane"
        );
    }

    #[test]
    fn refutation_guard_keeps_a_boolean_discriminant_raw_for_exact_grounding() {
        let func = test_func();
        let guard =
            GuardCondition::SwitchIntMatch { discr: Operand::Move(Place::local(2)), value: 0 };
        assert!(matches!(
            guard_to_refutation_formula(&func, &guard),
            Some(Formula::Not(inner)) if inner.var_name() == Some("flag")
        ));
    }

    #[test]
    fn refutation_guard_rejects_an_unsupported_operand_instead_of_freshening_it() {
        let func = test_func();
        let guard = GuardCondition::AssertHolds {
            cond: Operand::unsupported("future-operand", "no exact source carrier"),
            expected: true,
        };
        assert!(
            guard_to_refutation_formula(&func, &guard).is_none(),
            "a fresh fallback symbol cannot witness the unsupported source operand"
        );
    }

    #[test]
    fn test_guard_switch_int_otherwise_to_formula() {
        let func = test_func();
        let guard = GuardCondition::SwitchIntOtherwise {
            discr: Operand::Copy(Place::local(1)),
            excluded_values: vec![0, 7],
        };
        let formula = guard_to_formula(&func, &guard);
        match &formula {
            Formula::And(clauses) => {
                assert_eq!(clauses.len(), 2);
                assert!(matches!(&clauses[0], Formula::Not(inner)
                    if matches!(inner.as_ref(), Formula::Eq(_, rhs) if matches!(rhs.as_ref(), Formula::Int(0)))
                ));
                assert!(matches!(&clauses[1], Formula::Not(inner)
                    if matches!(inner.as_ref(), Formula::Eq(_, rhs) if matches!(rhs.as_ref(), Formula::Int(7)))
                ));
            }
            other => panic!("expected And, got: {other:?}"),
        }
    }

    #[test]
    fn test_guard_switch_int_otherwise_single_excluded() {
        let func = test_func();
        let guard = GuardCondition::SwitchIntOtherwise {
            discr: Operand::Copy(Place::local(1)),
            excluded_values: vec![5],
        };
        let formula = guard_to_formula(&func, &guard);
        // Single excluded value should produce just Not(Eq(..)), not And([...])
        assert!(matches!(&formula, Formula::Not(_)), "single excluded: {formula:?}");
    }

    #[test]
    fn test_guard_switch_int_otherwise_empty_excluded() {
        let func = test_func();
        let guard = GuardCondition::SwitchIntOtherwise {
            discr: Operand::Copy(Place::local(1)),
            excluded_values: vec![],
        };
        let formula = guard_to_formula(&func, &guard);
        assert_eq!(formula, Formula::Bool(true));
    }

    #[test]
    fn test_bool_switch_rewrite_ignores_nondominating_definition() {
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("cond".into()) },
        ];
        func.body.blocks = vec![
            BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(1, trust_types::BlockId(1))],
                    otherwise: trust_types::BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: trust_types::BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Eq,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(0)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: trust_types::BlockId(2),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ];

        let guard =
            GuardCondition::SwitchIntMatch { discr: Operand::Copy(Place::local(2)), value: 1 };
        let formula = guard_to_formula(&func, &guard);

        assert!(
            formula.var_name() == Some("cond"),
            "nondominating bool definitions must not rewrite the switch guard, got {formula:?}"
        );
    }

    // ── Nested-`SwitchInt` merge (`if / else if / else`) ──────────────────────

    /// The `proved/cursor_clamp_assert.rs` MIR, built block-for-block to match the
    /// real `-Ztrust-dump=mir` artifact:
    ///
    /// ```text
    ///   bb0: _4 = col < width;  SwitchInt(_4) -> [0: bb2] otherwise bb1
    ///   bb1: clamped = col;                                    Goto bb6
    ///   bb2: _5 = width > 0;    SwitchInt(_5) -> [0: bb5] otherwise bb3
    ///   bb3: _6 = CheckedSub(width, 1);  Assert(!_6.1)      -> bb4
    ///   bb4: clamped = _6.0;                                   Goto bb6
    ///   bb5: clamped = 0;                                      Goto bb6
    ///   bb6: (join)                                            Return
    /// ```
    fn nested_clamp_func() -> VerifiableFunction {
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("col".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("width".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: Some("clamped".into()) },
            LocalDecl { index: 4, ty: Ty::Bool, name: None },
            LocalDecl { index: 5, ty: Ty::Bool, name: None },
            LocalDecl { index: 6, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
        ];
        func.body.arg_count = 2;
        func.body.return_ty = Ty::u32();
        let assign = |local: usize, rvalue: Rvalue| Statement::Assign {
            place: Place::local(local),
            rvalue,
            span: SourceSpan::default(),
        };
        func.body.blocks = vec![
            BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![assign(
                    4,
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(4)),
                    targets: vec![(0, trust_types::BlockId(2))],
                    otherwise: trust_types::BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: trust_types::BlockId(1),
                stmts: vec![assign(3, Rvalue::Use(Operand::Copy(Place::local(1))))],
                terminator: Terminator::Goto(trust_types::BlockId(6)),
            },
            BasicBlock {
                id: trust_types::BlockId(2),
                stmts: vec![assign(
                    5,
                    Rvalue::BinaryOp(
                        BinOp::Gt,
                        Operand::Copy(Place::local(2)),
                        Operand::Constant(ConstValue::Uint(0, 32)),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(5)),
                    targets: vec![(0, trust_types::BlockId(5))],
                    otherwise: trust_types::BlockId(3),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: trust_types::BlockId(3),
                stmts: vec![assign(
                    6,
                    Rvalue::CheckedBinaryOp(
                        BinOp::Sub,
                        Operand::Copy(Place::local(2)),
                        Operand::Constant(ConstValue::Uint(1, 32)),
                    ),
                )],
                terminator: Terminator::Assert {
                    cond: Operand::Move(Place {
                        local: 6,
                        projections: vec![trust_types::Projection::Field(1)],
                    }),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Sub),
                    target: trust_types::BlockId(4),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Continue,
                },
            },
            BasicBlock {
                id: trust_types::BlockId(4),
                stmts: vec![assign(
                    3,
                    Rvalue::Use(Operand::Copy(Place {
                        local: 6,
                        projections: vec![trust_types::Projection::Field(0)],
                    })),
                )],
                terminator: Terminator::Goto(trust_types::BlockId(6)),
            },
            BasicBlock {
                id: trust_types::BlockId(5),
                stmts: vec![assign(3, Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))))],
                terminator: Terminator::Goto(trust_types::BlockId(6)),
            },
            BasicBlock {
                id: trust_types::BlockId(6),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ];
        func
    }

    /// Total ground evaluation of the fragment these merge facts live in
    /// (booleans are 0/1). `None` means "outside the fragment", which fails the
    /// test loudly rather than guessing a semantics.
    fn eval_ground(formula: &Formula, env: &[(&str, i128)]) -> Option<i128> {
        let look = |name: &str| env.iter().find(|(n, _)| *n == name).map(|(_, v)| *v);
        let bin = |l: &Formula, r: &Formula, op: fn(i128, i128) -> Option<i128>| {
            op(eval_ground(l, env)?, eval_ground(r, env)?)
        };
        match formula {
            Formula::Bool(value) => Some(i128::from(*value)),
            Formula::Int(value) => Some(*value),
            Formula::UInt(value) => i128::try_from(*value).ok(),
            Formula::Var(name, _) => look(name),
            Formula::SymVar(symbol, _) => look(symbol.as_str()),
            Formula::Not(inner) => Some(1 - eval_ground(inner, env)?),
            Formula::Or(parts) => {
                let mut any = 0;
                for part in parts {
                    any |= eval_ground(part, env)?;
                }
                Some(any)
            }
            Formula::And(parts) => {
                let mut all = 1;
                for part in parts {
                    all &= eval_ground(part, env)?;
                }
                Some(all)
            }
            Formula::Eq(l, r) => bin(l, r, |l, r| Some(i128::from(l == r))),
            Formula::Lt(l, r) => bin(l, r, |l, r| Some(i128::from(l < r))),
            Formula::Le(l, r) => bin(l, r, |l, r| Some(i128::from(l <= r))),
            Formula::Gt(l, r) => bin(l, r, |l, r| Some(i128::from(l > r))),
            Formula::Ge(l, r) => bin(l, r, |l, r| Some(i128::from(l >= r))),
            Formula::Add(l, r) => bin(l, r, i128::checked_add),
            Formula::Sub(l, r) => bin(l, r, i128::checked_sub),
            Formula::Mul(l, r) => bin(l, r, i128::checked_mul),
            // Lazy, like the machine: the untaken arm may be a value the branch
            // guard specifically prevents from being computed (`width - 1` when
            // `width == 0`).
            Formula::Ite(cond, then_branch, else_branch) => {
                if eval_ground(cond, env)? != 0 {
                    eval_ground(then_branch, env)
                } else {
                    eval_ground(else_branch, env)
                }
            }
            _ => None,
        }
    }

    /// The merged local of an `if / else if / else` must be recovered as a NESTED
    /// `Ite`, and that equality must hold on EVERY concrete execution — checked
    /// by running the program and the formula side by side over a dense input box.
    /// This is the property the whole lane rests on: a fact that is true on every
    /// reaching path only shrinks the model set, so it can neither false-prove
    /// (UNSAT direction) nor make a counterexample spurious (SAT direction).
    #[test]
    fn nested_switch_merge_matches_every_concrete_execution() {
        let func = nested_clamp_func();
        let merged = branch_merge_definitions(&func, trust_types::BlockId(6), &Default::default());
        assert_eq!(merged.len(), 1, "expected exactly the `clamped` merge, got {merged:?}");
        let Formula::Eq(lhs, rhs) = &merged[0] else {
            panic!("expected an equality, got {:?}", merged[0]);
        };
        assert_eq!(lhs.var_name(), Some("clamped"));
        let Formula::Ite(_, inner, _) = rhs.as_ref() else {
            panic!("expected an Ite, got {rhs:?}");
        };
        assert!(
            matches!(inner.as_ref(), Formula::Ite(..)),
            "the inner switch must nest inside the outer one, got {inner:?}"
        );

        for col in 0i128..=40 {
            for width in 0i128..=40 {
                // The program.
                let clamped = if col < width {
                    col
                } else if width > 0 {
                    width - 1
                } else {
                    0
                };
                // The state the formula's variables denote on that execution.
                let env = [
                    ("col", col),
                    ("width", width),
                    ("_4", i128::from(col < width)),
                    ("_5", i128::from(width > 0)),
                    ("_6.0", if width > 0 { width - 1 } else { 0 }),
                    ("_6.1", 0),
                ];
                assert_eq!(
                    eval_ground(rhs, &env),
                    Some(clamped),
                    "merge equality is false at col={col} width={width}: {rhs:?}"
                );
            }
        }
    }

    /// NEGATIVE. An intermediate block on the chain reassigns the OUTER switch's
    /// discriminant. Formulas here are unversioned, so the emitted Ite guard would
    /// read a value the outer switch never saw — a FALSE equality, which is
    /// unsound in BOTH directions (it can manufacture a spurious UNSAT, i.e. a
    /// false proof of panic-freedom, on exactly the safe shapes this lane serves).
    /// The single-switch lane's check covers only the arm block and its unique
    /// `Assert` parent, which is why the chain check had to be re-derived.
    #[test]
    fn nested_switch_merge_declines_clobbered_outer_discriminant() {
        let mut func = nested_clamp_func();
        func.body.blocks[2].stmts.insert(
            0,
            Statement::Assign {
                place: Place::local(4),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Lt,
                    Operand::Copy(Place::local(2)),
                    Operand::Copy(Place::local(1)),
                ),
                span: SourceSpan::default(),
            },
        );
        assert!(
            branch_merge_definitions(&func, trust_types::BlockId(6), &Default::default())
                .is_empty(),
            "a chain whose intermediate block clobbers an outer discriminant must yield nothing"
        );
    }

    /// NEGATIVE. An intermediate block rewrites a variable that ANOTHER arm's
    /// merged value reads (`if c { x = k } else { k = 7; if d { x = 0 } else { x = k } }`).
    /// The two `k`s denote different values but spell one symbol, so the Ite would
    /// again be a false equality. Nothing in the single-switch lane covers this:
    /// there, an arm's writes cannot precede a sibling arm.
    #[test]
    fn nested_switch_merge_declines_value_variable_rewritten_on_the_chain() {
        let mut func = nested_clamp_func();
        func.body.blocks[2].stmts.insert(
            0,
            Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(7))),
                span: SourceSpan::default(),
            },
        );
        assert!(
            branch_merge_definitions(&func, trust_types::BlockId(6), &Default::default())
                .is_empty(),
            "`col` is read by the bb1 arm value and rewritten on the bb2 chain"
        );
    }

    /// NEGATIVE. The nested lane never DROPS a switch destination: every target
    /// and the `otherwise` must resolve to an arm, so the partition is total by
    /// construction and no switch-totality reasoning is needed. A destination that
    /// leaves the region declines the join.
    #[test]
    fn nested_switch_merge_declines_destination_that_leaves_the_region() {
        let mut func = nested_clamp_func();
        func.body.blocks[5].terminator = Terminator::Return;
        assert!(
            branch_merge_definitions(&func, trust_types::BlockId(6), &Default::default())
                .is_empty(),
            "an unresolved switch destination must decline the whole join"
        );
    }

    /// NEGATIVE. A back edge into the chain (`bb5 -> bb2`) makes the region a
    /// loop rather than a tree: the merged local would be re-established each
    /// iteration under guards read at a different iteration. Fail closed.
    #[test]
    fn nested_switch_merge_declines_back_edge_into_the_chain() {
        let mut func = nested_clamp_func();
        func.body.blocks[5].terminator = Terminator::Goto(trust_types::BlockId(2));
        assert!(
            branch_merge_definitions(&func, trust_types::BlockId(6), &Default::default())
                .is_empty(),
            "a back edge into the switch chain must decline the join"
        );
    }

    /// NEGATIVE. A loop header is a join with two predecessors and no switch
    /// partition at all; the lane must not invent one.
    #[test]
    fn nested_switch_merge_declines_loop_header_join() {
        let mut func = nested_clamp_func();
        // bb0 -> bb1(header) ; bb1 -> bb2 (body) or bb3 (exit) ; bb2 -> bb1
        func.body.blocks = vec![
            BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(trust_types::BlockId(1)),
            },
            BasicBlock {
                id: trust_types::BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(4),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local(3)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(4)),
                    targets: vec![(0, trust_types::BlockId(3))],
                    otherwise: trust_types::BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: trust_types::BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(trust_types::BlockId(1)),
            },
            BasicBlock {
                id: trust_types::BlockId(3),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ];
        assert!(
            branch_merge_definitions(&func, trust_types::BlockId(1), &Default::default())
                .is_empty(),
            "a loop header is not a switch partition"
        );
    }

    /// The two lanes are DISJOINT: the nested lane requires at least two switches,
    /// so a plain diamond is still decided entirely by the single-switch lane and
    /// its result is byte-identical to before this extension.
    #[test]
    fn nested_switch_merge_leaves_the_single_switch_lane_untouched() {
        let mut func = nested_clamp_func();
        // Collapse the chain to one switch: bb0 -> bb1 / bb5, both Goto(bb6).
        func.body.blocks[0].terminator = Terminator::SwitchInt {
            discr: Operand::Move(Place::local(4)),
            targets: vec![(0, trust_types::BlockId(5))],
            otherwise: trust_types::BlockId(1),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        };
        func.body.blocks[2].terminator = Terminator::Return;
        func.body.blocks[3].terminator = Terminator::Return;
        func.body.blocks[4].terminator = Terminator::Return;
        let preds = block_predecessors(&func);
        assert!(
            nested_switch_branch_merge_definitions(&func, trust_types::BlockId(6), &preds)
                .is_empty(),
            "one switch is not a chain"
        );
        assert_eq!(
            branch_merge_definitions(&func, trust_types::BlockId(6), &Default::default()),
            single_switch_branch_merge_definitions(
                &func,
                trust_types::BlockId(6),
                &Default::default(),
                &preds
            ),
            "the single-switch lane must still decide the plain diamond"
        );
    }

    /// The emitted `Ite` selector must be the boolean discriminant's DEFINING
    /// COMPARISON, not the opaque temp. This is not cosmetic: MEASURED on the real
    /// MIR of `proved/cursor_clamp_assert.rs`, the opaque spelling makes
    /// `trust_certify::certify_violation` refuse two of the three grounded path
    /// residuals AND their disjunction (the whole-function panic-freedom
    /// catch-all's residual), so the kernel mints no certificate and a `Proved`
    /// without a kernel token reports `Unknown`. With the comparison inlined all
    /// three, and the disjunction, certify.
    #[test]
    fn nested_switch_merge_inlines_the_boolean_discriminant_definition() {
        let func = nested_clamp_func();
        let merged = branch_merge_definitions(&func, trust_types::BlockId(6), &Default::default());
        assert_eq!(merged.len(), 1, "expected exactly the `clamped` merge, got {merged:?}");
        let Formula::Eq(_, rhs) = &merged[0] else {
            panic!("expected an equality, got {:?}", merged[0]);
        };
        let Formula::Ite(outer_guard, inner, _) = rhs.as_ref() else {
            panic!("expected an Ite, got {rhs:?}");
        };
        // Outer switch routes value 0 (`!(col < width)`) to the inner chain.
        assert_eq!(
            outer_guard.as_ref(),
            &Formula::Not(Box::new(Formula::Lt(
                Box::new(Formula::Var("col".into(), Sort::Int)),
                Box::new(Formula::Var("width".into(), Sort::Int)),
            ))),
            "outer selector must carry the comparison, not the bool temp `_4`"
        );
        let Formula::Ite(inner_guard, ..) = inner.as_ref() else {
            panic!("expected a nested Ite, got {inner:?}");
        };
        assert_eq!(
            inner_guard.as_ref(),
            &Formula::Not(Box::new(Formula::Gt(
                Box::new(Formula::Var("width".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))),
            "inner selector must carry the comparison, not the bool temp `_5`"
        );
    }

    /// FALLBACK, not a false equality. When a compared operand is reassigned
    /// anywhere in the function the inlined comparison would be STALE — a false
    /// merge equality, unsound in both directions. `latest_same_block_bool_definition`
    /// declines, and the lane falls back to the opaque discriminant, which the
    /// clobber check pins directly.
    #[test]
    fn nested_switch_merge_falls_back_to_the_opaque_discriminant_when_an_operand_moves() {
        let mut func = nested_clamp_func();
        func.body.locals.push(LocalDecl { index: 7, ty: Ty::u32(), name: None });
        let assign = |local: usize, rvalue: Rvalue| Statement::Assign {
            place: Place::local(local),
            rvalue,
            span: SourceSpan::default(),
        };
        // `_7 = width` in bb0, and the outer test becomes `col < _7`.
        func.body.blocks[0].stmts.insert(0, assign(7, Rvalue::Use(Operand::Copy(Place::local(2)))));
        func.body.blocks[0].stmts[1] = assign(
            4,
            Rvalue::BinaryOp(
                BinOp::Lt,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(7)),
            ),
        );
        // A SECOND write to `_7`, below the switch: the block-0 comparison no longer
        // describes `_7`'s value at the join.
        func.body.blocks[2].stmts.push(assign(7, Rvalue::Use(Operand::Copy(Place::local(1)))));
        let merged = branch_merge_definitions(&func, trust_types::BlockId(6), &Default::default());
        assert_eq!(merged.len(), 1, "expected exactly the `clamped` merge, got {merged:?}");
        let Formula::Eq(_, rhs) = &merged[0] else {
            panic!("expected an equality, got {:?}", merged[0]);
        };
        let Formula::Ite(outer_guard, ..) = rhs.as_ref() else {
            panic!("expected an Ite, got {rhs:?}");
        };
        assert_eq!(
            outer_guard.as_ref(),
            &Formula::Not(Box::new(Formula::Var("_4".into(), Sort::Bool))),
            "a stale comparison must NOT be inlined; the opaque temp is the sound \
             fallback, got {outer_guard:?}"
        );
    }

    /// The clobber check must cover the symbols the RESOLVED guard reads, not just
    /// the raw discriminant place. A PROJECTED comparison operand (`_7.0`) is
    /// invisible to the plain-local staleness gates, so without adding the guard's
    /// own free variables to the below-switch write set the lane would emit
    /// `Ite(!(_7.0 < width), …)` while an arm block rewrites `_7.0` — a FALSE
    /// equality, and a false proof of panic-freedom on exactly this shape.
    #[test]
    fn nested_switch_merge_declines_clobbered_inlined_guard_operand() {
        let mut func = nested_clamp_func();
        func.body.locals.push(LocalDecl {
            index: 7,
            ty: Ty::Tuple(vec![Ty::u32(), Ty::u32()]),
            name: None,
        });
        let field0 = || Place { local: 7, projections: vec![trust_types::Projection::Field(0)] };
        // Outer test reads a tuple FIELD: `col < _7.0`.
        func.body.blocks[0].stmts[0] = Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::BinaryOp(
                BinOp::Lt,
                Operand::Copy(Place::local(1)),
                Operand::Copy(field0()),
            ),
            span: SourceSpan::default(),
        };
        let clobbered = |func: &VerifiableFunction| {
            branch_merge_definitions(func, trust_types::BlockId(6), &Default::default())
        };
        // Control: with no write to `_7.0`, the guard inlines and the merge is emitted.
        let clean = clobbered(&func);
        assert_eq!(clean.len(), 1, "control: the merge must be emitted, got {clean:?}");
        // Now an on-chain block rewrites the field the inlined guard reads.
        func.body.blocks[2].stmts.push(Statement::Assign {
            place: field0(),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: SourceSpan::default(),
        });
        assert!(
            clobbered(&func).is_empty(),
            "a below-switch write to the inlined guard's operand must DECLINE the join"
        );
    }

    /// The MIR shape whose inlined guard is stale WITHIN the switch block itself:
    ///
    /// ```text
    ///   bb0: _7.0 = width;  _4 = col < _7.0;  _7.0 = 0;  SwitchInt(_4)
    /// ```
    ///
    /// A revision of this lane that trusted
    /// `latest_same_block_bool_definition`'s own staleness gates emitted
    /// `Ite(!(col < _7.0), col, …)` here and was REJECTED for minting a false
    /// proof. All three of those gates miss this shape by construction:
    /// `compared_operand_reassigned_after` collects only projection-free
    /// comparison operands AND matches only projection-free writes (`_7.0` fails
    /// both halves), `value_local_is_unstable` is consulted only for plain
    /// locals, and the `discrs_below` clobber set is checked only against blocks
    /// STRICTLY BELOW the switch — never the switch block itself.
    ///
    /// Two things are asserted, and the second is the real one: the guard must be
    /// the opaque temp, and the emitted equality must hold on EVERY concrete
    /// execution. The stale spelling fails the second at (col=10, width=5) —
    /// `_7.0` is 0 at the join, so `!(col < _7.0)` is vacuously true and the
    /// formula claims `clamped == col == 10` where the program computes 4.
    #[test]
    fn nested_switch_merge_refuses_a_guard_the_switch_block_itself_staled() {
        let mut func = nested_clamp_func();
        func.body.locals.push(LocalDecl {
            index: 7,
            ty: Ty::Tuple(vec![Ty::u32(), Ty::u32()]),
            name: None,
        });
        let field0 = || Place { local: 7, projections: vec![trust_types::Projection::Field(0)] };
        let stmt = |place: Place, rvalue: Rvalue| Statement::Assign {
            place,
            rvalue,
            span: SourceSpan::default(),
        };
        func.body.blocks[0].stmts = vec![
            stmt(field0(), Rvalue::Use(Operand::Copy(Place::local(2)))),
            stmt(
                Place::local(4),
                Rvalue::BinaryOp(
                    BinOp::Lt,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(field0()),
                ),
            ),
            // The clobber: AFTER the comparison, in the switch block, through a
            // projection.
            stmt(field0(), Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32)))),
        ];

        let merged = branch_merge_definitions(&func, trust_types::BlockId(6), &Default::default());
        assert_eq!(merged.len(), 1, "expected exactly the `clamped` merge, got {merged:?}");
        let Formula::Eq(_, rhs) = &merged[0] else {
            panic!("expected an equality, got {:?}", merged[0]);
        };

        // FIRST, the property the whole lane rests on: the emitted equality must
        // hold on every concrete execution. Asserted before the spelling check so
        // this test reports the FALSE EQUALITY itself, not merely a spelling
        // regression. (Measured: with the staleness check removed, this fires at
        // col=10 width=5 — the formula claims `clamped == 10`, the program
        // computes 4.)
        for col in 0i128..=40 {
            for width in 0i128..=40 {
                let clamped = if col < width {
                    col
                } else if width > 0 {
                    width - 1
                } else {
                    0
                };
                let env = [
                    ("col", col),
                    ("width", width),
                    ("_4", i128::from(col < width)),
                    ("_5", i128::from(width > 0)),
                    ("_6.0", if width > 0 { width - 1 } else { 0 }),
                    ("_6.1", 0),
                    // `_7.0`'s value AT THE JOIN — the clobbered one, which is
                    // exactly what makes the inlined spelling false.
                    ("_7.0", 0),
                ];
                assert_eq!(
                    eval_ground(rhs, &env),
                    Some(clamped),
                    "merge equality is false at col={col} width={width}: {rhs:?}"
                );
            }
        }

        let Formula::Ite(outer_guard, ..) = rhs.as_ref() else {
            panic!("expected an Ite, got {rhs:?}");
        };
        assert_eq!(
            outer_guard.as_ref(),
            &Formula::Not(Box::new(Formula::Var("_4".into(), Sort::Bool))),
            "the switch block staled its own comparison; the opaque temp is the only \
             sound spelling, got {outer_guard:?}"
        );
    }

    /// Same staleness, reached through the `BitAnd` recursion rather than the top
    /// comparison: `_1 = col < _7.0; _2 = width > 0; _4 = _1 & _2; _7.0 = 0;`.
    /// The resolved definition is `And(Lt(col, _7.0), Gt(width, 0))`, so the
    /// disturbed symbol appears only in a LEAF — which is why the check is stated
    /// over the resolved formula's free variables rather than over the operands
    /// of the single statement that defines the discriminant.
    #[test]
    fn cross_block_bitand_leaf_is_refused_even_when_the_switch_block_is_clean() {
        // THE SHAPE THAT LEAKED PAST THE PREVIOUS TWO REPAIRS (adversarial review
        // reproduced it). The switch block writes nothing the guard reads, so
        // `switch_block_preserves_inlined_guard` is satisfied — but a BitAnd leaf is
        // defined in ANOTHER block and its operand is staled in between:
        //   bb0: _7.0 = width; _8 = col < _7.0;   Goto bb1
        //   bb1: _7.0 = 0;                        Goto bb2
        //   bb2: _9 = width > 0; _4 = _8 & _9;    SwitchInt(_4)
        // `_8` resolves cross-block (unique definition, forward Goto), so the stale
        // `col < _7.0` would be inlined at bb2 and the emitted Ite would be a FALSE
        // equality. `bool_definition_is_switch_block_local` refuses it at the resolver.
        let stmt = |place: Place, rvalue: Rvalue| Statement::Assign {
            place,
            rvalue,
            span: SourceSpan::default(),
        };
        let mut switch_block = BasicBlock {
            id: trust_types::BlockId(2),
            stmts: vec![
                stmt(
                    Place::local(9),
                    Rvalue::BinaryOp(
                        BinOp::Gt,
                        Operand::Copy(Place::local(2)),
                        Operand::Constant(ConstValue::Uint(0, 32)),
                    ),
                ),
                stmt(
                    Place::local(4),
                    Rvalue::BinaryOp(
                        BinOp::BitAnd,
                        Operand::Copy(Place::local(8)),
                        Operand::Copy(Place::local(9)),
                    ),
                ),
            ],
            terminator: Terminator::Return,
        };
        let func = nested_clamp_func();
        assert!(
            !bool_definition_is_switch_block_local(&func, &switch_block, 4, 8),
            "a BitAnd leaf defined OUTSIDE the switch block must refuse inlining — its \
             operands can be staled on the path in between"
        );

        // Control: define the leaf in the switch block too, and it is admitted.
        switch_block.stmts.insert(
            0,
            stmt(
                Place::local(8),
                Rvalue::BinaryOp(
                    BinOp::Lt,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
            ),
        );
        assert!(
            bool_definition_is_switch_block_local(&func, &switch_block, 4, 8),
            "control: every leaf same-block must be admitted"
        );
    }

    #[test]
    fn nested_switch_merge_refuses_a_staled_bitand_leaf_operand() {
        let mut func = nested_clamp_func();
        func.body.locals.push(LocalDecl {
            index: 7,
            ty: Ty::Tuple(vec![Ty::u32(), Ty::u32()]),
            name: None,
        });
        func.body.locals.push(LocalDecl { index: 8, ty: Ty::Bool, name: None });
        func.body.locals.push(LocalDecl { index: 9, ty: Ty::Bool, name: None });
        let field0 = || Place { local: 7, projections: vec![trust_types::Projection::Field(0)] };
        let stmt = |place: Place, rvalue: Rvalue| Statement::Assign {
            place,
            rvalue,
            span: SourceSpan::default(),
        };
        func.body.blocks[0].stmts = vec![
            stmt(field0(), Rvalue::Use(Operand::Copy(Place::local(2)))),
            stmt(
                Place::local(8),
                Rvalue::BinaryOp(
                    BinOp::Lt,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(field0()),
                ),
            ),
            stmt(
                Place::local(9),
                Rvalue::BinaryOp(
                    BinOp::Gt,
                    Operand::Copy(Place::local(2)),
                    Operand::Constant(ConstValue::Uint(0, 32)),
                ),
            ),
            stmt(
                Place::local(4),
                Rvalue::BinaryOp(
                    BinOp::BitAnd,
                    Operand::Copy(Place::local(8)),
                    Operand::Copy(Place::local(9)),
                ),
            ),
            // Clobbers a symbol read by the FIRST leaf only.
            stmt(field0(), Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32)))),
        ];
        let merged = branch_merge_definitions(&func, trust_types::BlockId(6), &Default::default());
        assert_eq!(merged.len(), 1, "expected exactly the `clamped` merge, got {merged:?}");
        let Formula::Eq(_, rhs) = &merged[0] else {
            panic!("expected an equality, got {:?}", merged[0]);
        };
        let Formula::Ite(outer_guard, ..) = rhs.as_ref() else {
            panic!("expected an Ite, got {rhs:?}");
        };
        assert_eq!(
            outer_guard.as_ref(),
            &Formula::Not(Box::new(Formula::Var("_4".into(), Sort::Bool))),
            "a staled BitAnd LEAF must refuse the inlining just like a staled top-level \
             comparison, got {outer_guard:?}"
        );
    }

    // ── split_path_feasibility_disjuncts ────────────────────────────────────

    #[test]
    fn split_distributes_shared_conjuncts_over_every_path() {
        let def =
            Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(1)));
        let p0 =
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let p1 =
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(9)));
        let combined = Formula::And(vec![def.clone(), Formula::Or(vec![p0.clone(), p1.clone()])]);
        assert_eq!(
            split_path_feasibility_disjuncts(&combined),
            vec![Formula::And(vec![def.clone(), p0]), Formula::And(vec![def, p1])],
            "every part must keep the shared definitional conjuncts"
        );
    }

    #[test]
    fn split_reaches_an_or_nested_under_an_and_spine() {
        let range =
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let p0 = Formula::Bool(true);
        let p1 = Formula::Bool(false);
        let inner = Formula::And(vec![range.clone(), Formula::Or(vec![p0.clone(), p1.clone()])]);
        let outer = Formula::And(vec![range.clone(), inner]);
        assert_eq!(
            split_path_feasibility_disjuncts(&outer),
            vec![
                Formula::And(vec![range.clone(), Formula::And(vec![range.clone(), p0])]),
                Formula::And(vec![range.clone(), Formula::And(vec![range, p1])]),
            ],
            "the And spine is descended; every other node stays byte-identical"
        );
    }

    #[test]
    fn split_declines_shapes_it_must_not_touch() {
        let x = Formula::Var("x".into(), Sort::Int);
        // No top-level Or at all.
        let plain = Formula::And(vec![Formula::Ge(Box::new(x.clone()), Box::new(Formula::Int(0)))]);
        assert_eq!(split_path_feasibility_disjuncts(&plain), vec![plain.clone()]);
        // Distributivity does not apply under `Not` / `Ite` / an `Or` arm.
        let under_not = Formula::And(vec![Formula::Not(Box::new(Formula::Or(vec![
            Formula::Bool(true),
            Formula::Bool(false),
        ])))]);
        assert_eq!(split_path_feasibility_disjuncts(&under_not), vec![under_not.clone()]);
        // Over the cap: keep ONE obligation (the pre-split behaviour).
        let many = Formula::Or(
            (0..=MAX_SPLIT_PATHS as i128)
                .map(|k| Formula::Eq(Box::new(x.clone()), Box::new(Formula::Int(k))))
                .collect(),
        );
        assert_eq!(split_path_feasibility_disjuncts(&many), vec![many.clone()]);
    }

    /// EXACTNESS, checked by exhaustive ground evaluation: the disjunction of the
    /// parts and the original formula agree on every assignment. This is the whole
    /// soundness argument of the split — UNSAT iff every part is UNSAT, and any
    /// part's model is verbatim a model of the original.
    #[test]
    fn split_is_ground_equivalent_to_the_formula_it_replaces() {
        let x = || Formula::Var("x".into(), Sort::Int);
        let y = || Formula::Var("y".into(), Sort::Int);
        let combined = Formula::And(vec![
            Formula::And(vec![
                Formula::Ge(Box::new(x()), Box::new(Formula::Int(0))),
                Formula::Le(Box::new(x()), Box::new(Formula::Int(6))),
            ]),
            Formula::Eq(
                Box::new(y()),
                Box::new(Formula::Ite(
                    Box::new(Formula::Lt(Box::new(x()), Box::new(Formula::Int(3)))),
                    Box::new(x()),
                    Box::new(Formula::Int(3)),
                )),
            ),
            Formula::Or(vec![
                Formula::And(vec![
                    Formula::Lt(Box::new(x()), Box::new(Formula::Int(3))),
                    Formula::Gt(Box::new(y()), Box::new(Formula::Int(2))),
                ]),
                Formula::And(vec![
                    Formula::Ge(Box::new(x()), Box::new(Formula::Int(3))),
                    Formula::Not(Box::new(Formula::Eq(Box::new(y()), Box::new(Formula::Int(3))))),
                ]),
            ]),
        ]);
        let parts = split_path_feasibility_disjuncts(&combined);
        assert_eq!(parts.len(), 2);
        for xv in -2i128..=8 {
            for yv in -2i128..=8 {
                let env = [("x", xv), ("y", yv)];
                let whole = eval_ground(&combined, &env).expect("in fragment");
                let any = parts
                    .iter()
                    .map(|p| eval_ground(p, &env).expect("in fragment"))
                    .fold(0, |a, b| a | b);
                assert_eq!(whole, any, "split disagrees with the original at x={xv} y={yv}");
            }
        }
    }

    #[test]
    fn test_branch_merge_definitions_encodes_diamond_as_ite() {
        // `let x = if flag { 10 } else { 20 };`
        //   bb0: SwitchInt(flag) -> [0: bb2, otherwise: bb1]
        //   bb1 (flag true):  x = 10; goto bb3
        //   bb2 (flag false): x = 20; goto bb3
        //   bb3 (join):       return
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("flag".into()) },
        ];
        func.body.blocks = vec![
            BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(0, trust_types::BlockId(2))],
                    otherwise: trust_types::BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: trust_types::BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(10))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(trust_types::BlockId(3)),
            },
            BasicBlock {
                id: trust_types::BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(20))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(trust_types::BlockId(3)),
            },
            BasicBlock {
                id: trust_types::BlockId(3),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ];

        let merged = branch_merge_definitions(&func, trust_types::BlockId(3), &Default::default());
        assert_eq!(merged.len(), 1, "expected one merged-local invariant, got {merged:?}");
        match &merged[0] {
            Formula::Eq(lhs, rhs) => {
                assert_eq!(lhs.var_name(), Some("x"), "lhs must be the merged local x: {lhs:?}");
                match rhs.as_ref() {
                    Formula::Ite(cond, then_v, else_v) => {
                        // value 0 selects the match arm (bb2, x=20) when flag is
                        // false, so the guard is Not(flag) and the then-branch is 20.
                        assert!(
                            matches!(cond.as_ref(), Formula::Not(inner) if inner.var_name() == Some("flag")),
                            "guard must be Not(flag): {cond:?}"
                        );
                        assert_eq!(**then_v, Formula::Int(20), "match arm (flag false) is x=20");
                        assert_eq!(**else_v, Formula::Int(10), "otherwise arm (flag true) is x=10");
                    }
                    other => panic!("rhs must be an Ite, got: {other:?}"),
                }
            }
            other => panic!("merged invariant must be an Eq, got: {other:?}"),
        }
    }

    #[test]
    fn test_branch_merge_keeps_switch_identity_across_checked_assert_success() {
        // `let x = if flag { checked_add_value } else { 10 };`
        //
        // rustc splits the checked arm through an overflow Assert:
        //
        //   bb0: SwitchInt(flag) -> [0: bb2, otherwise: bb1]
        //   bb1: x = 10; goto bb4
        //   bb2: checked = AddWithOverflow(..);
        //        Assert(!checked.1) -> bb3
        //   bb3: x = checked.0; goto bb4
        //   bb4: return
        //
        // The Assert failure edge never reaches bb4, so bb0 still partitions
        // every execution that reaches the join. Losing that identity leaves x
        // free and falsely refutes valid postconditions over guarded arithmetic.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("flag".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                name: Some("checked".into()),
            },
            LocalDecl { index: 4, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 5, ty: Ty::u32(), name: Some("b".into()) },
        ];
        func.body.blocks = vec![
            BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(0, trust_types::BlockId(2))],
                    otherwise: trust_types::BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: trust_types::BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(10))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(trust_types::BlockId(4)),
            },
            BasicBlock {
                id: trust_types::BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(4)),
                        Operand::Copy(Place::local(5)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert {
                    cond: Operand::Move(Place {
                        local: 3,
                        projections: vec![trust_types::Projection::Field(1)],
                    }),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Add),
                    target: trust_types::BlockId(3),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Continue,
                },
            },
            BasicBlock {
                id: trust_types::BlockId(3),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 3,
                        projections: vec![trust_types::Projection::Field(0)],
                    })),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(trust_types::BlockId(4)),
            },
            BasicBlock {
                id: trust_types::BlockId(4),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ];
        let pristine = func.clone();

        let merged = branch_merge_definitions(&func, trust_types::BlockId(4), &Default::default());
        assert_eq!(merged.len(), 1, "expected one exact checked-arm merge, got {merged:?}");
        let Formula::Eq(lhs, rhs) = &merged[0] else {
            panic!("merged invariant must be an Eq, got: {:?}", merged[0]);
        };
        assert_eq!(lhs.var_name(), Some("x"));
        let Formula::Ite(cond, checked, fallback) = rhs.as_ref() else {
            panic!("merged rhs must be an Ite, got: {rhs:?}");
        };
        assert!(
            matches!(cond.as_ref(), Formula::Not(inner) if inner.var_name() == Some("flag")),
            "value 0 must select the checked arm under Not(flag): {cond:?}"
        );
        assert_eq!(
            **checked,
            Formula::Add(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Var("b".into(), Sort::Int)),
            ),
            "the uniquely dominated checked result must be inlined before the join"
        );
        assert_eq!(**fallback, Formula::Int(10));

        // A write in the value arm changes the meaning of the unversioned name
        // `a` but not the snapshot already stored in `checked.0`. Inlining to
        // the arm-exit `a + b` here would be a false fact and could false-PROVE.
        // Keep the exact control-flow merge, but leave the checked field opaque.
        func.body.blocks[3].stmts.insert(
            0,
            Statement::Assign {
                place: Place::local(4),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(99))),
                span: SourceSpan::default(),
            },
        );
        let stale = branch_merge_definitions(&func, trust_types::BlockId(4), &Default::default());
        let Formula::Eq(_, stale_rhs) = &stale[0] else {
            panic!("stale-arm merge must remain an Eq, got: {:?}", stale[0]);
        };
        let Formula::Ite(_, stale_checked, _) = stale_rhs.as_ref() else {
            panic!("stale-arm merge rhs must remain an Ite, got: {stale_rhs:?}");
        };
        assert_eq!(
            stale_checked.var_name(),
            Some("checked.0"),
            "a clobbered checked operand must block snapshot substitution"
        );

        // The Ite selector is the raw switch discriminator. Reassigning it on an
        // incoming arm makes the unversioned name stale, so the entire merge
        // must be withheld (not merely the checked-result substitution).
        func.body.blocks[3].stmts.push(Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(true))),
            span: SourceSpan::default(),
        });
        assert!(
            branch_merge_definitions(&func, trust_types::BlockId(4), &Default::default())
                .is_empty(),
            "a post-switch discriminant write must fail closed"
        );

        let false_route = exact_switch_value_guard(&pristine, &Operand::Copy(Place::local(2)), 0);
        assert!(
            matches!(false_route, Some(Formula::Not(inner)) if inner.var_name() == Some("flag")),
            "a branch selector needs exact raw Bool polarity, never a weakened `true` guard"
        );
        let mut signed = pristine.clone();
        signed.body.locals[2].ty = Ty::Int { width: 8, signed: true };
        let signed_route = exact_switch_value_guard(&signed, &Operand::Copy(Place::local(2)), 0xff);
        let Some(Formula::Eq(_, signed_value)) = signed_route else {
            panic!("a signed SwitchInt target must now resolve: {signed_route:?}");
        };
        assert_eq!(
            *signed_value,
            Formula::Int(-1),
            "the raw i8 SwitchInt target 0xff must SIGN-EXTEND to -1, never the magnitude 255 \
             (matching `contracts::switch_edge_formula`'s decode)"
        );
        assert!(
            exact_switch_value_guard(&signed, &Operand::Copy(Place::local(2)), 0x1ff).is_none(),
            "a label with bits above the scrutinee's width is malformed and must fail closed"
        );
        assert_eq!(
            exact_switch_value_guard(&signed, &Operand::Copy(Place::local(2)), 0x7f),
            Some(Formula::Eq(
                Box::new(operand_to_formula(&signed, &Operand::Copy(Place::local(2)))),
                Box::new(Formula::Int(127)),
            )),
            "a non-negative signed label keeps its magnitude"
        );
        let mut unsigned = pristine.clone();
        unsigned.body.locals[2].ty = Ty::Int { width: 8, signed: false };
        assert_eq!(
            exact_switch_value_guard(&unsigned, &Operand::Copy(Place::local(2)), 0xff),
            Some(Formula::Eq(
                Box::new(operand_to_formula(&unsigned, &Operand::Copy(Place::local(2)))),
                Box::new(Formula::Int(255)),
            )),
            "the UNSIGNED row is unchanged: u8 0xff still denotes 255"
        );

        let mut duplicate = pristine.clone();
        let Terminator::SwitchInt { targets, .. } = &mut duplicate.body.blocks[0].terminator else {
            unreachable!("fixture root is a SwitchInt");
        };
        targets.push((0, trust_types::BlockId(1)));
        assert!(
            branch_merge_definitions(&duplicate, trust_types::BlockId(4), &Default::default())
                .is_empty(),
            "duplicate raw switch values must not mint overlapping Ite arms"
        );

        let mut failure_reaches_value_arm = pristine.clone();
        let Terminator::Assert { unwind, .. } =
            &mut failure_reaches_value_arm.body.blocks[2].terminator
        else {
            unreachable!("fixture checked block is an Assert");
        };
        *unwind = UnwindEdge::Cleanup(trust_types::BlockId(3));
        assert!(
            branch_merge_definitions(
                &failure_reaches_value_arm,
                trust_types::BlockId(4),
                &Default::default(),
            )
            .is_empty(),
            "an Assert failure edge reaching its value arm is not success-authenticated"
        );

        // The shared checked-Assert recognizer is itself proof authority for
        // semantic/path maps. Multiple reaching tuple definitions or a write
        // after the checked snapshot must yield no facts in either direction.
        let mut multiple_checked = pristine.clone();
        multiple_checked.body.blocks[2].stmts.push(Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::CheckedBinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(4)),
                Operand::Copy(Place::local(5)),
            ),
            span: SourceSpan::default(),
        });
        assert!(
            extract_assert_passed_semantics(&multiple_checked, &multiple_checked.body.blocks[2])
                .is_empty()
        );
        assert!(
            extract_overflow_flag_semantics(&multiple_checked, &multiple_checked.body.blocks[2])
                .is_empty()
        );

        let mut post_snapshot_write = pristine;
        post_snapshot_write.body.blocks[2].stmts.push(Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 32))),
            span: SourceSpan::default(),
        });
        assert!(
            extract_assert_passed_semantics(
                &post_snapshot_write,
                &post_snapshot_write.body.blocks[2]
            )
            .is_empty()
        );
        assert!(
            extract_overflow_flag_semantics(
                &post_snapshot_write,
                &post_snapshot_write.body.blocks[2]
            )
            .is_empty()
        );
    }

    // Helpers shared by the n-arm merge tests below.
    fn arm_assign(id: usize, value: i128, goto: usize) -> BasicBlock {
        BasicBlock {
            id: trust_types::BlockId(id),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(value))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Goto(trust_types::BlockId(goto)),
        }
    }

    // Asserts `f` is `Eq(Var("d"), Int(value))` — the guard for switch arm `value`.
    fn assert_discr_guard(f: &Formula, value: i128) {
        match f {
            Formula::Eq(lhs, rhs) => {
                assert_eq!(lhs.var_name(), Some("d"), "guard lhs must be discr d: {f:?}");
                assert_eq!(**rhs, Formula::Int(value), "guard rhs must be Int({value}): {f:?}");
            }
            other => panic!("expected Eq(d, Int({value})), got: {other:?}"),
        }
    }

    // Three-arm enum `let base = match e { A => 10, B => 20, C => 30 }` where the
    // exhaustive lowering routes the last variant through `otherwise` (which still
    // reaches the join). Expect base == Ite(d==0,10,Ite(d==1,20,30)).
    fn assert_three_arm_merge(merged: &[Formula]) {
        assert_eq!(merged.len(), 1, "expected one merged-local invariant, got {merged:?}");
        let Formula::Eq(lhs, rhs) = &merged[0] else {
            panic!("merged invariant must be an Eq, got: {:?}", merged[0]);
        };
        assert_eq!(lhs.var_name(), Some("base"), "lhs must be the merged local base: {lhs:?}");
        // Outer: Ite(d==0, 10, <inner>)
        let Formula::Ite(g0, v0, inner) = rhs.as_ref() else {
            panic!("rhs must be an Ite, got: {rhs:?}");
        };
        assert_discr_guard(g0, 0);
        assert_eq!(**v0, Formula::Int(10), "arm d==0 is base=10");
        // Inner: Ite(d==1, 20, 30)   (30 is the else / catch-all arm)
        let Formula::Ite(g1, v1, else_v) = inner.as_ref() else {
            panic!("inner must be an Ite, got: {inner:?}");
        };
        assert_discr_guard(g1, 1);
        assert_eq!(**v1, Formula::Int(20), "arm d==1 is base=20");
        assert_eq!(**else_v, Formula::Int(30), "catch-all arm is base=30");
    }

    fn three_arm_func() -> VerifiableFunction {
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("base".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("d".into()) },
        ];
        func
    }

    #[test]
    fn test_branch_merge_three_arm_otherwise_is_last_variant() {
        // bb0: SwitchInt(d) -> [0: bb1, 1: bb2, otherwise: bb3]
        // bb1: base=10; goto bb4   bb2: base=20; goto bb4   bb3: base=30; goto bb4
        // bb4 (join): return
        let mut func = three_arm_func();
        func.body.blocks = vec![
            BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(0, trust_types::BlockId(1)), (1, trust_types::BlockId(2))],
                    otherwise: trust_types::BlockId(3),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            arm_assign(1, 10, 4),
            arm_assign(2, 20, 4),
            arm_assign(3, 30, 4),
            BasicBlock {
                id: trust_types::BlockId(4),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ];
        assert_three_arm_merge(&branch_merge_definitions(
            &func,
            trust_types::BlockId(4),
            &Default::default(),
        ));
    }

    #[test]
    fn test_branch_merge_three_arm_separate_unreachable_otherwise() {
        // bb0: SwitchInt(d) -> [0: bb1, 1: bb2, 2: bb3, otherwise: bb5]
        // bb1/2/3: base=10/20/30; goto bb4    bb4 (join): return    bb5: unreachable
        // The unreachable otherwise never reaches the join, so the last explicit
        // target (bb3) is promoted to the catch-all; same Ite as above.
        let mut func = three_arm_func();
        func.body.blocks = vec![
            BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![
                        (0, trust_types::BlockId(1)),
                        (1, trust_types::BlockId(2)),
                        (2, trust_types::BlockId(3)),
                    ],
                    otherwise: trust_types::BlockId(5),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            arm_assign(1, 10, 4),
            arm_assign(2, 20, 4),
            arm_assign(3, 30, 4),
            BasicBlock {
                id: trust_types::BlockId(4),
                stmts: vec![],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: trust_types::BlockId(5),
                stmts: vec![],
                terminator: Terminator::Unreachable,
            },
        ];
        assert_three_arm_merge(&branch_merge_definitions(
            &func,
            trust_types::BlockId(4),
            &Default::default(),
        ));
    }

    #[test]
    fn test_branch_merge_bails_when_arm_not_from_switch() {
        // bb3 reaches the join but descends from bb2 (an extra hop), not the
        // switch bb0 — the arms do not share one conditional predecessor, so no
        // partition claim is sound and the result must be empty.
        // bb0: SwitchInt(d) -> [0: bb1, otherwise: bb2]
        // bb1: base=10; goto bb4    bb2: goto bb3    bb3: base=20; goto bb4
        // bb4 (join): return
        let mut func = three_arm_func();
        func.body.blocks = vec![
            BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(0, trust_types::BlockId(1))],
                    otherwise: trust_types::BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            arm_assign(1, 10, 4),
            BasicBlock {
                id: trust_types::BlockId(2),
                stmts: vec![],
                terminator: Terminator::Goto(trust_types::BlockId(3)),
            },
            arm_assign(3, 20, 4),
            BasicBlock {
                id: trust_types::BlockId(4),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ];
        let merged = branch_merge_definitions(&func, trust_types::BlockId(4), &Default::default());
        assert!(merged.is_empty(), "non-partition join must yield no claim, got {merged:?}");
    }

    #[test]
    fn test_guard_assert_holds_expected_true() {
        let func = test_func();
        let guard =
            GuardCondition::AssertHolds { cond: Operand::Copy(Place::local(2)), expected: true };
        let formula = guard_to_formula(&func, &guard);
        // expected=true: cond holds, so formula is just the condition var
        // Formula::var() now creates SymVar; match both Var and SymVar.
        assert!(formula.var_name() == Some("flag"), "expected flag var, got: {formula:?}");
    }

    #[test]
    fn test_guard_assert_holds_expected_false() {
        let func = test_func();
        let guard =
            GuardCondition::AssertHolds { cond: Operand::Copy(Place::local(2)), expected: false };
        let formula = guard_to_formula(&func, &guard);
        // expected=false: assert passes when cond is false, so NOT(cond)
        // Match both Var and SymVar via var_name().
        assert!(
            matches!(&formula, Formula::Not(inner) if inner.var_name() == Some("flag")),
            "expected Not(flag), got: {formula:?}"
        );
    }

    #[test]
    fn test_guard_assert_fails_expected_true() {
        let func = test_func();
        let guard = GuardCondition::AssertFails {
            cond: Operand::Copy(Place::local(2)),
            expected: true,
            msg: AssertMessage::Custom("test".into()),
        };
        let formula = guard_to_formula(&func, &guard);
        // Assert failed: expected true but got false => NOT(cond)
        // Match both Var and SymVar via var_name().
        assert!(
            matches!(&formula, Formula::Not(inner) if inner.var_name() == Some("flag")),
            "expected Not(flag), got: {formula:?}"
        );
    }

    #[test]
    fn test_guards_to_assumption_empty() {
        let func = test_func();
        let assumption = guards_to_assumption(&func, &[]);
        assert_eq!(assumption, Formula::Bool(true));
    }

    #[test]
    fn test_guards_to_assumption_single() {
        let func = test_func();
        let guards = vec![GuardCondition::SwitchIntMatch {
            discr: Operand::Copy(Place::local(1)),
            value: 1,
        }];
        let assumption = guards_to_assumption(&func, &guards);
        // Single guard should not wrap in And
        assert!(matches!(&assumption, Formula::Eq(_, _)), "single guard: {assumption:?}");
    }

    #[test]
    fn test_guards_to_assumption_multiple() {
        let func = test_func();
        let guards = vec![
            GuardCondition::SwitchIntMatch { discr: Operand::Copy(Place::local(1)), value: 1 },
            GuardCondition::AssertHolds { cond: Operand::Copy(Place::local(2)), expected: true },
        ];
        let assumption = guards_to_assumption(&func, &guards);
        match &assumption {
            Formula::And(clauses) => assert_eq!(clauses.len(), 2),
            other => panic!("expected And, got: {other:?}"),
        }
    }

    #[test]
    fn test_guarded_formula_empty_guards() {
        let func = test_func();
        let vc = Formula::Not(Box::new(Formula::Bool(true)));
        let result = guarded_formula(&func, &[], vc.clone());
        assert_eq!(result, vc, "empty guards should return formula unchanged");
    }

    #[test]
    fn test_guarded_formula_with_guards() {
        let func = test_func();
        let guards = vec![GuardCondition::SwitchIntMatch {
            discr: Operand::Copy(Place::local(1)),
            value: 1,
        }];
        let vc = Formula::Not(Box::new(Formula::Bool(true)));
        let result = guarded_formula(&func, &guards, vc);
        // Should be And([guard_assumption, vc_formula])
        assert!(matches!(&result, Formula::And(clauses) if clauses.len() == 2));
    }

    /// A label above `i128::MAX` keeps the `Formula::UInt` spelling rather than
    /// being silently truncated — but ONLY where such a label is well formed,
    /// i.e. on a `u128` scrutinee. The fixture used to state this over
    /// `test_func`'s `u32` local, where `2^127` has 95 bits set above the
    /// scrutinee's width: that is a malformed target, and the guard lane now
    /// declines it (contributing no conjunct) instead of asserting an equality
    /// the type can never satisfy.
    #[test]
    fn test_guard_switch_int_match_u128_above_i128_max() {
        let mut func = test_func();
        func.body.locals[1].ty = Ty::Int { width: 128, signed: false };
        let large_value: u128 = (i128::MAX as u128) + 1;
        let guard = GuardCondition::SwitchIntMatch {
            discr: Operand::Copy(Place::local(1)),
            value: large_value,
        };
        let formula = guard_to_formula(&func, &guard);
        assert!(
            matches!(&formula, Formula::Eq(_, rhs) if matches!(rhs.as_ref(), Formula::UInt(v) if *v == large_value)),
            "u128 value above i128::MAX should use Formula::UInt, got: {formula:?}"
        );

        assert_eq!(
            guard_to_formula(&test_func(), &guard),
            Formula::Bool(true),
            "the same label on the u32 fixture is out of width: decline, never constrain"
        );
    }

    /// A raw `SwitchInt` label is a two's-complement BIT PATTERN at the
    /// scrutinee's width. Reading it as a magnitude put `n == 4294967295` on an
    /// `i32` `-1` arm; conjoined with `n`'s own range fact that is UNSAT, so the
    /// arm was VACUOUS and `match n { -1 => x + 1, _ => 0 }` FALSE-PROVED while
    /// `f(-1, 255)` panics. Pin the decode at every signed width, and pin that
    /// the unsigned row did not move.
    #[test]
    fn signed_switch_labels_sign_extend_and_unsigned_labels_do_not() {
        let signed_widths: [(u32, u128, i128); 5] = [
            (8, 0xff, -1),
            (16, 0xffff, -1),
            (32, 0xffff_ffff, -1),
            (64, 0xffff_ffff_ffff_ffff, -1),
            (32, 0xffff_fff9, -7),
        ];
        for (width, raw, expected) in signed_widths {
            let mut func = test_func();
            func.body.locals[1].ty = Ty::Int { width, signed: true };
            let guard = GuardCondition::SwitchIntMatch {
                discr: Operand::Copy(Place::local(1)),
                value: raw,
            };
            let formula = guard_to_formula(&func, &guard);
            assert!(
                matches!(&formula, Formula::Eq(lhs, rhs)
                    if lhs.var_name() == Some("x")
                    && matches!(rhs.as_ref(), Formula::Int(v) if *v == expected)),
                "i{width} label {raw:#x} must decode to {expected}, got: {formula:?}"
            );
        }

        // isize, and the sign-extending `otherwise` exclusion beside it.
        let mut ptr = test_func();
        ptr.body.locals[1].ty = Ty::PtrSizedInt { signed: true };
        let otherwise = guard_to_formula(
            &ptr,
            &GuardCondition::SwitchIntOtherwise {
                discr: Operand::Copy(Place::local(1)),
                excluded_values: vec![0xffff_ffff_ffff_ffff],
            },
        );
        assert!(
            matches!(&otherwise, Formula::Not(inner)
                if matches!(inner.as_ref(), Formula::Eq(_, rhs)
                    if matches!(rhs.as_ref(), Formula::Int(-1)))),
            "the isize `otherwise` arm must exclude -1, not the tautology `x != 2^64-1`: \
             {otherwise:?}"
        );

        // MUST NOT CHANGE: the unsigned row. `test_func`'s `x` is a `u32`.
        let unsigned = guard_to_formula(
            &test_func(),
            &GuardCondition::SwitchIntMatch {
                discr: Operand::Copy(Place::local(1)),
                value: 0xffff_ffff,
            },
        );
        assert!(
            matches!(&unsigned, Formula::Eq(_, rhs)
                if matches!(rhs.as_ref(), Formula::Int(4294967295))),
            "u32 0xffff_ffff still denotes the magnitude 4294967295, got: {unsigned:?}"
        );

        // A label wider than the scrutinee is malformed: contribute NO conjunct
        // rather than a wrong one (weaker path condition, fails closed).
        let mut narrow = test_func();
        narrow.body.locals[1].ty = Ty::Int { width: 8, signed: true };
        assert_eq!(
            guard_to_formula(
                &narrow,
                &GuardCondition::SwitchIntMatch {
                    discr: Operand::Copy(Place::local(1)),
                    value: 0x1ff,
                },
            ),
            Formula::Bool(true),
            "an out-of-width label must weaken the path condition, never constrain it wrongly"
        );
    }

    #[test]
    fn test_guard_switch_int_otherwise_u128_above_i128_max() {
        let mut func = test_func();
        func.body.locals[1].ty = Ty::Int { width: 128, signed: false };
        let large_value: u128 = u128::MAX;
        let guard = GuardCondition::SwitchIntOtherwise {
            discr: Operand::Copy(Place::local(1)),
            excluded_values: vec![large_value],
        };
        let formula = guard_to_formula(&func, &guard);
        // Should produce Not(Eq(discr, UInt(u128::MAX)))
        assert!(
            matches!(&formula, Formula::Not(inner)
                if matches!(inner.as_ref(), Formula::Eq(_, rhs)
                    if matches!(rhs.as_ref(), Formula::UInt(v) if *v == u128::MAX))),
            "u128::MAX excluded value should use Formula::UInt, got: {formula:?}"
        );

        assert_eq!(
            guard_to_formula(&test_func(), &guard),
            Formula::Bool(true),
            "an out-of-width exclusion drops out: the `otherwise` arm keeps one \
             constraint fewer (weaker, fails closed), never a tautological one"
        );
    }

    #[test]
    fn float_comparisons_use_sound_fp_encoding() {
        // Float ordering and general `==`/`!=` are modeled with the IEEE-754
        // FloatingPoint theory (was UNMODELED/fail-closed before the FP theory
        // existed). `fp.*` matches Rust PartialOrd/PartialEq exactly.
        let f = test_func();
        let one = Operand::Constant(ConstValue::Float(1.0));
        let two = Operand::Constant(ConstValue::Float(2.0));

        let lt = super::float_binop_to_formula(&f, BinOp::Lt, &one, &two, 64)
            .expect("float `<` is now modeled");
        assert!(matches!(lt, Formula::FpLt(..)), "expected FpLt, got {lt:?}");
        assert!(matches!(
            super::float_binop_to_formula(&f, BinOp::Le, &one, &two, 64),
            Some(Formula::FpLe(..))
        ));
        assert!(matches!(
            super::float_binop_to_formula(&f, BinOp::Gt, &one, &two, 64),
            Some(Formula::FpGt(..))
        ));
        assert!(matches!(
            super::float_binop_to_formula(&f, BinOp::Ge, &one, &two, 64),
            Some(Formula::FpGe(..))
        ));
        assert!(matches!(
            super::float_binop_to_formula(&f, BinOp::Eq, &one, &two, 64),
            Some(Formula::FpEq(..))
        ));
        assert!(matches!(
            super::float_binop_to_formula(&f, BinOp::Ne, &one, &two, 64),
            Some(Formula::Not(_))
        ));
        // Operands are reinterpreted from their bit patterns via FpFromBits.
        if let Formula::FpLt(l, r) = lt {
            assert!(matches!(*l, Formula::FpFromBits { eb: 11, sb: 53, .. }));
            assert!(matches!(*r, Formula::FpFromBits { eb: 11, sb: 53, .. }));
        }

        // `x == 0.0` keeps its proven magnitude encoding (Eq over a bit-extract).
        let zero = Operand::Constant(ConstValue::Float(0.0));
        let eq0 = super::float_binop_to_formula(&f, BinOp::Eq, &one, &zero, 64)
            .expect("`x == 0.0` stays soundly modeled");
        assert!(matches!(eq0, Formula::Eq(..)), "x==0.0 keeps magnitude encoding, got {eq0:?}");
        assert!(super::float_binop_to_formula(&f, BinOp::Ne, &one, &zero, 64).is_some());

        // Unsupported float widths fail closed.
        assert!(
            super::float_binop_to_formula(&f, BinOp::Lt, &one, &two, 80).is_none(),
            "non-IEEE width must fail closed"
        );
    }

    #[test]
    fn modeled_identity_cast_only_value_preserving() {
        use crate::is_modeled_identity_cast as id;
        // Value-preserving (no-op or non-signed->unsigned widening): identity OK.
        assert!(id(&Ty::u32(), &Ty::u32()));
        assert!(id(&Ty::i32(), &Ty::i32()));
        assert!(id(&Ty::u8(), &Ty::u32()), "unsigned widening (zero-extend) preserves value");
        assert!(id(&Ty::i8(), &Ty::i32()), "signed->signed widening (sign-extend) preserves value");
        assert!(id(&Ty::u8(), &Ty::i32()), "unsigned->wider signed: value fits");
        // Value-changing casts: must NOT be identity (fail-closed).
        assert!(!id(&Ty::u32(), &Ty::u8()), "narrowing truncates");
        assert!(!id(&Ty::i32(), &Ty::u32()), "same-width signedness reinterpret changes value");
        assert!(!id(&Ty::i8(), &Ty::u32()), "signed->unsigned widening wraps negatives");
        assert!(!id(&Ty::i32(), &Ty::i8()), "signed narrowing truncates");

        // Trust (verified-sysroot §5 step 3, slice 1): thin-pointer address
        // EXPOSE is identity over the collapsed allocation model's value.
        let thin_const = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
        let thin_mut = Ty::RawPtr { mutable: true, pointee: Box::new(Ty::i32()) };
        let thin_ref = Ty::Ref { mutable: false, inner: Box::new(Ty::u64()) };
        let nonnull_newtype = Ty::adt(
            "core::ptr::non_null::NonNull",
            vec![("pointer".to_string(), thin_const.clone())],
        );
        assert!(id(&thin_const, &Ty::usize()), "thin *const expose is the addr() shape");
        assert!(id(&thin_mut, &Ty::usize()), "thin *mut expose is the addr() shape");
        assert!(
            id(&thin_ref, &Ty::usize()),
            "thin &T expose (transmute leg) preserves the address"
        );
        assert!(
            id(&nonnull_newtype, &Ty::usize()),
            "thin single-pointer newtype expose (NonNull::addr)"
        );
        // FALSIFYING refusals — each goes red if the semantics are widened
        // wrongly rather than merely if the accept case works:
        assert!(
            !id(&Ty::usize(), &thin_const),
            "RECOVER direction manufactures provenance; must refuse"
        );
        assert!(
            !id(&thin_const, &Ty::u32()),
            "narrowing expose truncates the address; must refuse"
        );
        assert!(
            !id(&thin_const, &Ty::i64()),
            "signed expose reinterprets high addresses; must refuse"
        );
        let fat_slice = Ty::RawPtr {
            mutable: false,
            pointee: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
        };
        let fat_str = Ty::Ref { mutable: false, inner: Box::new(Ty::Str) };
        let fat_dyn = Ty::Ref {
            mutable: false,
            inner: Box::new(Ty::Dynamic { trait_name: "t::Tr".into(), principal_key: None }),
        };
        assert!(
            !id(&fat_slice, &Ty::usize()),
            "fat *const [T] has no single-address value; must refuse"
        );
        assert!(!id(&fat_str, &Ty::usize()), "fat &str has no single-address value; must refuse");
        assert!(!id(&fat_dyn, &Ty::usize()), "fat &dyn has no single-address value; must refuse");
    }

    /// Trust (verified-sysroot §5 step 3, slice 1) — VALUE-LANE falsifier for
    /// the provenance-EXPOSE cast. The accept case must yield the pointer's OWN
    /// term (`dest == p`, the statability seam); every guarded refusal must
    /// yield `None` (dest stays unconstrained / fail-closed). Red if the accept
    /// case regresses to opaque, and red if any refusal is wrongly admitted.
    #[test]
    fn ptr_expose_value_lane_identity_vs_refusal() {
        let thin = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
        let fat = Ty::RawPtr {
            mutable: false,
            pointee: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
        };
        let func_with = |src_ty: Ty, dest_ty: Ty| {
            let mut func = test_func();
            func.body.locals = vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: src_ty, name: Some("p".into()) },
                LocalDecl { index: 2, ty: dest_ty, name: Some("addr_w".into()) },
            ];
            func.body.arg_count = 1;
            func.body.return_ty = Ty::Unit;
            func
        };
        let op = Operand::Copy(Place::local(1));
        let dest = Place::local(2);

        // ACCEPT: thin expose is identity over the pointer's model value.
        let func = func_with(thin.clone(), Ty::usize());
        let value = super::cast_definition_formula(&func, &dest, &op, &Ty::usize())
            .expect("thin-pointer expose must produce a value fact (statability)");
        assert_eq!(
            value.var_name(),
            Some("p"),
            "the value fact must be the pointer's OWN term, got {value:?}"
        );

        // REFUSE (each falsifies a wrongly-widened semantics):
        let func = func_with(thin.clone(), Ty::u32());
        assert!(
            super::cast_definition_formula(&func, &dest, &op, &Ty::u32()).is_none(),
            "narrowing expose truncates the address; the value lane must decline"
        );
        let func = func_with(thin.clone(), Ty::i64());
        assert!(
            super::cast_definition_formula(&func, &dest, &op, &Ty::i64()).is_none(),
            "signed expose reinterprets high addresses; the value lane must decline"
        );
        let func = func_with(Ty::usize(), thin.clone());
        assert!(
            super::cast_definition_formula(&func, &dest, &op, &thin).is_none(),
            "RECOVER (int->ptr) manufactures provenance; the value lane must decline"
        );
        let func = func_with(fat.clone(), Ty::usize());
        assert!(
            super::cast_definition_formula(&func, &dest, &op, &Ty::usize()).is_none(),
            "a fat pointer has no single-address model value; the value lane must decline"
        );
    }

    /// Build a 2-block function: bb0 calls an ascii predicate `callee(ch)` into a
    /// bool local `_b` and switches on it; bb1 is the predicate-TRUE shift block
    /// `_k = ch as u128; r = 1u128 << _k`. `char` lowers to `u32`, so `ch` is a
    /// plain unsigned local. Locals: 0 ret(u128), 1 ch(u32 ≡ char), 2 _b(bool),
    /// 3 _k(u128), 4 r(u128).
    fn ascii_guarded_shift_func(callee: &str) -> VerifiableFunction {
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u128(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("ch".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("_b".into()) },
            LocalDecl { index: 3, ty: Ty::u128(), name: Some("_k".into()) },
            LocalDecl { index: 4, ty: Ty::u128(), name: Some("r".into()) },
        ];
        func.body.arg_count = 1;
        func.body.return_ty = Ty::u128();
        func.body.blocks = vec![
            // bb0: _b = callee(ch); switch _b -> [0: bb2 (else), otherwise: bb1 (true)]
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: callee.to_string(),
                    args: vec![Operand::Copy(Place::local(1))],
                    dest: Place::local(2),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
                    is_foreign: false,
                },
            },
            // bb1 (is_ascii TRUE): _k = ch as u128; r = 1u128 << _k
            BasicBlock {
                id: BlockId(1),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u128()),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Shl,
                            Operand::Constant(ConstValue::Uint(1, 128)),
                            Operand::Copy(Place::local(3)),
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            },
            // bb2 (else): return 0
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
        ];
        func
    }

    #[test]
    fn ascii_guard_bounds_shift_amount() {
        // `if ch.is_ascii() { 1u128 << (ch as u128) }`: the is_ascii-TRUE guard
        // must imply `ch <= 127`, which bounds the shift amount below 128 and lets
        // the shift-overflow VC PROVE. The TRUE branch is reached via the switch's
        // `otherwise` edge (the `is_ascii() == true` case), so the guard is
        // `SwitchIntMatch { discr: _b, value: 1 }`.
        let func = ascii_guarded_shift_func("core::char::methods::<impl char>::is_ascii");
        let guard =
            GuardCondition::SwitchIntMatch { discr: Operand::Copy(Place::local(2)), value: 1 };
        let formula = guard_to_formula(&func, &guard);
        assert!(
            matches!(&formula, Formula::Le(lhs, rhs)
                if lhs.var_name() == Some("ch")
                && matches!(rhs.as_ref(), Formula::Int(127))),
            "is_ascii-TRUE guard must imply `ch <= 127`, got: {formula:?}"
        );

        // Every other predicate gets its own exact TRUE-set, which is tighter
        // than `[0, 127]`: `is_ascii_digit` is `48 <= ch <= 57`, so
        // `if b.is_ascii_digit() { b - b'0' }` cannot underflow.
        let ch_term = operand_to_formula(&func, &Operand::Copy(Place::local(1)));
        let ch = || Box::new(ch_term.clone());
        let range = |lo: i128, hi: i128| {
            Formula::And(vec![
                Formula::Ge(ch(), Box::new(Formula::Int(lo))),
                Formula::Le(ch(), Box::new(Formula::Int(hi))),
            ])
        };
        for (callee, expected) in [
            ("core::char::methods::<impl char>::is_ascii_digit", range(48, 57)),
            (
                "core::char::methods::<impl char>::is_ascii_alphanumeric",
                Formula::Or(vec![range(48, 57), range(65, 90), range(97, 122)]),
            ),
            ("core::char::methods::<impl char>::is_ascii_uppercase", range(65, 90)),
            (
                "core::num::<impl u8>::is_ascii_hexdigit",
                Formula::Or(vec![range(48, 57), range(65, 70), range(97, 102)]),
            ),
            (
                "core::num::<impl u8>::is_ascii_control",
                Formula::Or(vec![Formula::Le(ch(), Box::new(Formula::Int(31))), range(127, 127)]),
            ),
        ] {
            let func = ascii_guarded_shift_func(callee);
            let guard =
                GuardCondition::SwitchIntMatch { discr: Operand::Copy(Place::local(2)), value: 1 };
            let formula = guard_to_formula(&func, &guard);
            assert_eq!(formula, expected, "{callee} TRUE guard must be its exact TRUE-set");
        }
    }

    #[test]
    fn ascii_guard_does_not_hide_unbounded_shift() {
        // ADVERSARIAL: the predicate-FALSE branch must not bound the shift amount
        // below 128. It gets the COMPLEMENT of the TRUE-set, `!(ch <= 127)`, so a
        // `1u128 << ch` there still refutes. The FALSE case is the explicit
        // `value: 0` target of the switch.
        let func = ascii_guarded_shift_func("core::char::methods::<impl char>::is_ascii");
        let false_guard =
            GuardCondition::SwitchIntMatch { discr: Operand::Copy(Place::local(2)), value: 0 };
        let false_formula = guard_to_formula(&func, &false_guard);
        assert!(
            matches!(&false_formula, Formula::Not(inner)
                if formula_mentions_le_127_on(inner, "ch")),
            "is_ascii-FALSE branch must be the complement `!(ch <= 127)`, got: {false_formula:?}"
        );

        // A genuinely-unbounded shift with NO ascii guard at all gets no `<= 127`
        // fact, so its shift-overflow VC still (correctly) refutes:
        // `fn g(n: u32) -> u128 { 1u128 << n }`.
        let mut g = test_func();
        g.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u128(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
        ];
        g.body.arg_count = 1;
        g.body.return_ty = Ty::u128();
        // No call, no switch — just an unguarded shift block. `bool_switch_semantics`
        // never fires, and there is no ascii fact in scope.
        assert!(
            ascii_predicate_bound(&g, &Operand::Copy(Place::local(1))).is_none(),
            "an operand with no ascii-predicate call defining it must yield no bound"
        );
    }

    /// True iff `formula` contains an `Le(Var(var), Int(127))` anywhere.
    fn formula_mentions_le_127_on(formula: &Formula, var: &str) -> bool {
        match formula {
            Formula::Le(l, r) => {
                l.var_name() == Some(var) && matches!(r.as_ref(), Formula::Int(127))
            }
            Formula::And(cs) | Formula::Or(cs) => {
                cs.iter().any(|c| formula_mentions_le_127_on(c, var))
            }
            Formula::Not(inner) => formula_mentions_le_127_on(inner, var),
            _ => false,
        }
    }

    #[test]
    fn ascii_guard_bounds_referent_through_autoref_receiver() {
        // Real MIR: a method receiver `b.is_ascii()` lowers to `_5 = &b;
        // is_ascii(move _5)`, so the call argument is a REFERENCE. The bound must
        // land on the referent `b` (_1), NOT the inert reference local `_5` —
        // otherwise the fact never connects to the shift amount and the hardened
        // panic_boundary VC false-refutes a provably-safe ascii-guarded shift.
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u128(), name: Some("ret".into()) },
            LocalDecl { index: 1, ty: Ty::Int { width: 8, signed: false }, name: Some("b".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("_b".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: Some("_k".into()) },
            LocalDecl { index: 4, ty: Ty::u128(), name: Some("r".into()) },
            LocalDecl { index: 5, ty: Ty::Bool, name: Some("_ref".into()) },
        ];
        func.body.arg_count = 1;
        func.body.return_ty = Ty::u128();
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            // _5 = &b; then is_ascii(move _5) -> _b
            stmts: vec![Statement::Assign {
                place: Place::local(5),
                rvalue: Rvalue::Ref { place: Place::local(1), mutable: false },
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                func: "core::num::<impl u8>::is_ascii".to_string(),
                args: vec![Operand::Move(Place::local(5))],
                dest: Place::local(2),
                target: Some(BlockId(1)),
                span: SourceSpan::default(),
                atomic: None,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: crate::sep_engine::tests::fixture_key("core::num::<impl u8>::is_ascii"),
                is_foreign: false,
            },
        }];

        let bound = ascii_predicate_bound(&func, &Operand::Copy(Place::local(2)))
            .expect("is_ascii(&b) must still yield a bound");
        assert!(
            matches!(&bound, Formula::Le(lhs, rhs)
                if lhs.var_name() == Some("b")
                && matches!(rhs.as_ref(), Formula::Int(127))),
            "auto-ref receiver bound must be on the referent `b`, not the reference, got: {bound:?}"
        );
    }

    /// Trust (2026-09-30): the borrow-temp recognizer spells the wide write-channel
    /// form (`&mut`, `&raw mut`, `&raw const`), so a `&raw const`
    /// temp passed to a call is a write channel of its referent like `&raw mut`.
    /// (Its two callers' statement scans refuse the same statement first, so no
    /// verdict changed; this pins the recognizer itself.)
    #[test]
    fn a_raw_const_borrow_temp_is_a_write_channel_of_its_referent() {
        let mut func = test_func();
        func.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl {
                index: 2,
                ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) },
                name: None,
            },
        ];
        let temp_of = |rvalue: Rvalue| {
            let mut f = func.clone();
            f.body.blocks = vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue,
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }];
            f
        };
        for (rvalue, want) in [
            (Rvalue::AddressOf(false, Place::local(1)), true),
            (Rvalue::AddressOf(true, Place::local(1)), true),
            (Rvalue::Ref { mutable: true, place: Place::local(1) }, true),
            (Rvalue::Ref { mutable: false, place: Place::local(1) }, false),
        ] {
            let f = temp_of(rvalue.clone());
            assert_eq!(operand_local_is_mut_borrow_of(&f, 2, 1), want, "{rvalue:?}");
        }
    }

    /// VARIANT-ARM-DUP-EDGE-1 (2026-10-06): rustc -O0's lowering of
    /// `match a.get(i) { Some(_) => {}, None => {} }; a[i]` (real extraction,
    /// `tests/fixtures/slice_get_try_dup_target_mir.json`) switches
    /// `[0: bb3, 1: bb3] otherwise bb2`: `bb3` is the join both variants reach, and the
    /// `get`-`Some` recognizer must seed nothing there. A `Some`-only routing seeds
    /// `i < len(a)` at `bb3`; `bb3` as both the `Some` and the `otherwise` target, and a
    /// second edge into `bb3` from elsewhere, seed nothing.
    #[test]
    fn get_some_seeds_nothing_at_an_arm_another_edge_enters() {
        use trust_types::BlockId;
        let load = || -> VerifiableFunction {
            let path = concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/slice_get_try_dup_target_mir.json"
            );
            serde_json::from_str(&std::fs::read_to_string(path).expect("fixture"))
                .expect("fixture parses")
        };
        let set_switch = |f: &mut VerifiableFunction, t: Vec<(u128, BlockId)>, o: BlockId| {
            let Terminator::SwitchInt { targets, otherwise, .. } = &mut f.body.blocks[1].terminator
            else {
                panic!("bb1 switches on the tag");
            };
            *targets = t;
            *otherwise = o;
        };
        let dup = load();
        assert!(
            matches!(&dup.body.blocks[1].terminator, Terminator::SwitchInt { targets, otherwise, .. }
                if *targets == [(0, BlockId(3)), (1, BlockId(3))] && *otherwise == BlockId(2)),
            "the fixture is rustc's duplicate-target lowering"
        );
        assert!(slice_get_some_index_bound_definitions(&dup).is_empty(), "both tags reach bb3");

        let mut some_only = load();
        set_switch(&mut some_only, vec![(0, BlockId(2)), (1, BlockId(3))], BlockId(2));
        let facts = slice_get_some_index_bound_definitions(&some_only);
        assert_eq!(facts.len(), 1, "{facts:?}");
        assert!(facts.get(&BlockId(3)).is_some_and(|f| !f.is_empty()), "{facts:?}");

        let mut some_and_otherwise = load();
        set_switch(&mut some_and_otherwise, vec![(0, BlockId(2)), (1, BlockId(3))], BlockId(3));
        assert!(slice_get_some_index_bound_definitions(&some_and_otherwise).is_empty());

        // A second edge into bb3 from ANOTHER block (bb2 `Goto(bb3)`): bb3's per-edge
        // predecessors are `[bb1, bb2]`.
        let mut second_pred = load();
        set_switch(&mut second_pred, vec![(0, BlockId(2)), (1, BlockId(3))], BlockId(2));
        second_pred.body.blocks[2].terminator = Terminator::Goto(BlockId(3));
        assert!(slice_get_some_index_bound_definitions(&second_pred).is_empty());
    }
}
