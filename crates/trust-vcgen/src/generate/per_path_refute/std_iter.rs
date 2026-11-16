// trust-vcgen/generate/per_path_refute/std_iter: the slice-iterator VALUE
// summary, confined to the refute-only lane.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Trust: a **value** summary for `for &x in <&[T; N]>`, usable ONLY to refute.
//!
//! # What this module is
//!
//! `for &x in a` over `a: &[T; N]` lowers to two calls whose bodies the verifier
//! never sees:
//!
//! ```text
//! _3 = <&[T; N] as IntoIterator>::into_iter(copy _1) -> bb1
//! _5 = <slice::Iter<'_, T> as Iterator>::next(copy _6) -> bb3
//! ```
//!
//! Both are OPAQUE. Per-path symbolic execution cannot thread anything through
//! them, so [`super`] declines every path through the loop and a genuinely
//! reachable `assert!`/`panic!` inside the body is never refuted. Closing that
//! needs a summary of what those two calls RETURN — not merely that they are
//! total, which is what the compiler's existing mechanism already gives.
//!
//! # The axiom, stated exactly
//!
//! For `a: &[T; N]` with `T` a scalar integer type (no interior mutability, so
//! the referent's element values are fixed for the lifetime of the borrow):
//!
//! * `<&[T; N] as IntoIterator>::into_iter(a)` returns a `slice::Iter<'_, T>`
//!   positioned at index 0 over exactly the `N` elements of `*a`.
//! * the `k`-th subsequent `next()` on that iterator returns `Some(&(*a)[k])`
//!   for `k < N`, and `None` for every `k >= N`.
//! * neither call panics, diverges, or mutates anything the caller can observe.
//!
//! This is documented `core` behaviour. Trust cannot PROVE it: `core`'s bodies
//! are not lowered, and `Iter::next` advances a raw pointer with `BinOp::Offset`
//! (see [`trust_types::Rvalue::PtrOffset`]) which is outside the verifiable
//! fragment. It is therefore an ASSUMPTION about the standard library, and the
//! whole design of this module is about bounding the blast radius of that
//! assumption.
//!
//! # Why it is confined to the refutation direction
//!
//! An assumption fed to the bidirectional VC class would license an UNSAT-based
//! PROOF: "no model of `¬post ∧ path` exists" would silently rest on the
//! summary, and a WRONG summary would then manufacture a FALSE PROOF — the one
//! outcome this project treats as unrecoverable.
//!
//! Fed instead to [`trust_types::RefuteOnlyVc`], the same assumption can only
//! ever produce a SAT model, i.e. a WITNESS. A wrong summary there manufactures
//! a spurious witness — a FALSE REFUTATION. That is a real defect (it would
//! reject a correct program) but it is strictly smaller: it is visible as a
//! concrete counterexample the author can run, and it can never certify
//! anything. `RefuteOnlyOutcome::NoRefutation` is payload-free, so there is no
//! expression anywhere downstream that can turn this summary into a `Proved`
//! row.
//!
//! The confinement is structural, not documentary: this module is a PRIVATE
//! submodule of [`super`] (`mod std_iter;`, no `pub`), and [`super`]'s only
//! public entry points return `Vec<RefuteOnlyVc>`. No other module in
//! `trust-vcgen` can name these items, so no other lane can consume the summary
//! even by accident.
//!
//! # Why the compiler's existing mechanism could not be extended
//!
//! `rustc_mir_transform::trust_verify` already has an ADJACENT recognizer,
//! `callee_is_type_verified_total_std_iterator`, feeding
//! `CrateVerificationState::type_total_std_callees`. It is strictly better than
//! this module at IDENTIFYING the callee: it works from real `ty::Ty` +
//! `CrateNum` + `sym::Iterator` diagnostic items rather than from a rendered
//! path. But it is the wrong mechanism here for two independent reasons:
//!
//! 1. **It carries no value information.** It records only "this call runs no
//!    user code and cannot panic" — TOTALITY. It says nothing about what `next`
//!    returns, which is the entire content needed to know that `x` is an element
//!    of `a` and that the loop body is entered at all.
//! 2. **It feeds the PROVING direction.** Its consumer is
//!    `all_calls_target_proven_panic_free`, the interprocedural panic-freedom
//!    discharge — a premise of `Proved` rows. Attaching a value axiom to that
//!    set would put the assumption above squarely on the proof side, which is
//!    exactly the hazard this module is built to avoid.
//!
//! So a separate mechanism is required, and it belongs here rather than there.
//! The cost of living in vcgen (no `TyCtxt`) is that callee IDENTITY must be
//! decided from the rendered path; see [`recognize`] for how that is narrowed
//! and why the TrustIr TYPE cross-checks in [`super`] — not the string — are the
//! load-bearing gate.

use trust_types::{AdtKind, Ty};

/// A `<…>::method` call this lane can reproduce EXACTLY.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum StdIterCall {
    /// `<&[T; N] as IntoIterator>::into_iter` — constructs the iterator.
    IntoIterArrayRef,
    /// `<slice::Iter<'_, T> as Iterator>::next` — advances it.
    SliceIterNext,
}

/// Trait paths admitted for `next`. Definition paths, both spellings the
/// bridge's renderer produces (`trust-ir-bridge` lower.rs renders the same
/// callee as `core::…` or `std::…` depending on the reachable re-export).
const ITERATOR_TRAIT_PATHS: &[&str] = &[
    "core::iter::traits::iterator::Iterator",
    "std::iter::traits::iterator::Iterator",
    "core::iter::Iterator",
    "std::iter::Iterator",
];

/// Trait paths admitted for `into_iter`.
const INTO_ITERATOR_TRAIT_PATHS: &[&str] = &[
    "core::iter::traits::collect::IntoIterator",
    "std::iter::traits::collect::IntoIterator",
    "core::iter::IntoIterator",
    "std::iter::IntoIterator",
];

/// `Self` type prefixes admitted for `next`.
const SLICE_ITER_SELF_PREFIXES: &[&str] = &["core::slice::iter::Iter<", "std::slice::iter::Iter<"];

/// ADT names admitted as the `slice::Iter` produced by `into_iter` and consumed
/// by `next`. Checked against the TrustIr TYPE of the destination local, which
/// is why this is the strong half of the recognizer.
pub(super) const SLICE_ITER_ADT_NAMES: &[&str] =
    &["core::slice::iter::Iter", "std::slice::iter::Iter"];

/// ADT names admitted as the `Option<&T>` `next` returns.
const OPTION_ADT_NAMES: &[&str] = &["core::option::Option", "std::option::Option"];

/// Prefix of the SMT symbol minted for one element of a modeled `&[T; N]`
/// parameter. A lane's symbol is minted when a path READS the lane (see
/// [`super::read_array_lane`]), so no path formula is sized by `N`.
///
/// INJECTIVITY, which is load-bearing exactly as it is for
/// `super::param_var_name`: two element symbols that collide would identify two
/// independent inputs, and a model over the merged symbol would not be a real
/// execution. The full name is `{PREFIX}{local_index}_{element_index}`, which is
/// injective in `(local, element)` because local indices are unique
/// (`super::Ctx::build` rejects the function otherwise). Collisions with a
/// SOURCE name are not argued away — [`super::read_array_lane`] checks every
/// minted name against the function's whole local-name space and drops the
/// path on any clash.
pub(super) const ELEM_VAR_PREFIX: &str = "__trust_ppr_elem_";

/// Is `name` the ADT name of a `core`/`std` slice iterator?
pub(super) fn is_slice_iter_adt(name: &str) -> bool {
    SLICE_ITER_ADT_NAMES.contains(&name)
}

/// Split `<SELF as TRAIT>::ITEM` into its three parts.
///
/// Returns `None` for any callee not in that exact shape — an inherent method,
/// a free function, or a path this parser cannot decompose unambiguously. The
/// trait segment is taken at the LAST ` as ` and the item at the LAST `>::`, so
/// a `Self` type containing either token (`&[Foo<'_, Bar>; 4]`) still splits at
/// the outermost boundary.
fn split_qualified(callee: &str) -> Option<(&str, &str, &str)> {
    let inner_end = callee.rfind(">::")?;
    let rest = callee.strip_prefix('<')?;
    // `inner_end` indexes into `callee`; `rest` dropped exactly one leading byte.
    let inner = rest.get(..inner_end.checked_sub(1)?)?;
    let item = callee.get(inner_end.checked_add(3)?..)?;
    let as_at = inner.rfind(" as ")?;
    let self_ty = inner.get(..as_at)?;
    let trait_path = inner.get(as_at.checked_add(4)?..)?;
    if self_ty.is_empty() || trait_path.is_empty() || item.is_empty() {
        return None;
    }
    Some((self_ty, trait_path, item))
}

/// Peel any number of leading `&`/`&mut ` from a rendered type.
fn peel_refs(mut ty: &str) -> &str {
    for _ in 0..4 {
        let Some(rest) = ty.strip_prefix('&') else { break };
        ty = rest.strip_prefix("mut ").unwrap_or(rest).trim_start_matches(|c: char| c == ' ');
    }
    ty
}

/// Trust: is this callee one of the two summarized slice-iterator operations?
///
/// PURELY A NARROWING FILTER. vcgen has no `TyCtxt`, so this can only inspect
/// the rendered definition path, and a rendered path is the weaker half of an
/// identity check (the campaign's own recorded failure mode is exactly
/// "definition-path renderer vs re-export-spelling recognizer"). Three things
/// keep that acceptable here:
///
/// * The trait segment must be one of a CLOSED list of `core`/`std` definition
///   paths. A user trait cannot be spelled `core::iter::…::Iterator`, and a user
///   crate cannot define an item inside `core`/`std`, so a user `fn next` on a
///   `slice::Iter` (`<slice::Iter<'_, u8> as my::Trait>::next`) is rejected here.
/// * Every match is then cross-checked against the TrustIr TYPES at the call
///   site by [`super::apply_std_iter_call`]: the argument must already carry a
///   tracked array/iterator VALUE, and the destination local's declared type
///   must structurally be `slice::Iter` / `Option<&T>` with the SAME element
///   type. A false string match that survives those checks would need a user
///   type that is structurally the slice iterator too.
/// * A residual mismatch cannot manufacture a proof — see the module docs. Its
///   worst outcome is a spurious witness, which the lane's tests probe directly.
pub(super) fn recognize(callee: &str) -> Option<StdIterCall> {
    let (self_ty, trait_path, item) = split_qualified(callee)?;
    match item {
        "into_iter" => {
            if !INTO_ITERATOR_TRAIT_PATHS.contains(&trait_path) {
                return None;
            }
            // `&[T; N]` — a SHARED reference to a FIXED-SIZE array.
            //
            // * `&mut [T; N]` is not admitted: its `IntoIter` yields `&mut T`,
            //   and a caller-visible mutation channel would break the "element
            //   values are fixed" half of the axiom.
            // * `[T; N]` by value is not admitted: it yields `T`, not `&T`.
            // * `&[T]` — a SLICE — is not admitted: its length is a runtime
            //   value, so there is no fixed `N` to symbolize. The `;` is what
            //   separates the two spellings. (A nested spelling such as
            //   `&[[u8; 2]]` would slip past this text test; the TYPE
            //   cross-check in `super::apply_std_iter_call` is what actually
            //   rejects it, since only a `&[T; N]` parameter with SCALAR
            //   elements ever carries a tracked array value.)
            let body = self_ty.strip_prefix("&")?;
            if body.starts_with("mut ") || !body.starts_with('[') || !body.ends_with(']') {
                return None;
            }
            if !body.contains(';') {
                return None;
            }
            Some(StdIterCall::IntoIterArrayRef)
        }
        "next" => {
            if !ITERATOR_TRAIT_PATHS.contains(&trait_path) {
                return None;
            }
            let base = peel_refs(self_ty);
            if !SLICE_ITER_SELF_PREFIXES.iter().any(|p| base.starts_with(p)) {
                return None;
            }
            Some(StdIterCall::SliceIterNext)
        }
        _ => None,
    }
}

/// The variant indices of an `Option<&T>` whose payload is `&elem_ty`.
#[derive(Debug, Clone, Copy)]
pub(super) struct OptionRefShape {
    /// Index (within `Ty::Adt::variants`) of the field-less `None` variant.
    pub(super) none_index: usize,
    /// Index of the one-field `Some(&elem_ty)` variant.
    pub(super) some_index: usize,
}

/// Trust: read the `Option<&T>` variant structure off the DESTINATION's declared
/// TrustIr type, for a `next` returning references to `elem_ty`.
///
/// Nothing about `Option`'s layout is assumed: the variant INDICES are located
/// by matching the declared `VariantDef`s (one field-less `None`, one
/// single-field `Some` whose field is exactly `&elem_ty`), and the caller maps
/// an index to its `SwitchInt` tag through the same `VariantDef::discriminant`
/// the extractor recorded. `Option<&T>` is niche-encoded, so hard-coding
/// `None = 0` / `Some = 1` would be an assumption about layout on top of the
/// assumption about semantics; this is the version that makes neither.
///
/// Fail-closed on every mismatch: a wrong shape means the callee is not the
/// `next` this module summarizes, and the path is dropped.
pub(super) fn option_ref_variant_shape(ty: Option<&Ty>, elem_ty: &Ty) -> Option<OptionRefShape> {
    let Ty::Adt { name, variants, adt_kind, .. } = ty? else {
        return None;
    };
    if !OPTION_ADT_NAMES.contains(&name.as_str()) {
        return None;
    }
    // `adt_kind` is `None` on pre-W19 serialized types; require the positive
    // classification rather than optimistically treating an unclassified ADT as
    // an enum.
    if *adt_kind != Some(AdtKind::Enum) || variants.len() != 2 {
        return None;
    }
    let payload_ty = Ty::Ref { mutable: false, inner: Box::new(elem_ty.clone()) };
    let mut none_index = None;
    let mut some_index = None;
    for (index, variant) in variants.iter().enumerate() {
        match (variant.name.as_str(), variant.fields.as_slice()) {
            ("None", []) if none_index.is_none() => none_index = Some(index),
            ("Some", [(_, field_ty)]) if some_index.is_none() && *field_ty == payload_ty => {
                some_index = Some(index);
            }
            _ => return None,
        }
    }
    let (none_index, some_index) = (none_index?, some_index?);
    if none_index == some_index {
        return None;
    }
    Some(OptionRefShape { none_index, some_index })
}

#[cfg(test)]
mod tests {
    use trust_types::VariantDef;

    use super::*;

    /// The two callee spellings the stage2 `trustc` actually emits for
    /// `for &x in a` over `a: &[u8; 4]` (copied from the `-Ztrust-dump=mir`
    /// output of `tests/trust-falsification/mutant/pf_subsume_foreach_assert.rs`).
    #[test]
    fn recognizes_the_real_foreach_callees() {
        assert_eq!(
            recognize("<&[u8; 4] as core::iter::traits::collect::IntoIterator>::into_iter"),
            Some(StdIterCall::IntoIterArrayRef)
        );
        assert_eq!(
            recognize(
                "<core::slice::iter::Iter<'_, u8> as core::iter::traits::iterator::Iterator>::next"
            ),
            Some(StdIterCall::SliceIterNext)
        );
    }

    /// The `std::` re-export spelling of the same two definitions must be
    /// recognized identically — the recorded failure mode for path recognizers
    /// in this tree.
    #[test]
    fn recognizes_the_std_reexport_spelling() {
        assert!(
            recognize("<&[u8; 4] as std::iter::IntoIterator>::into_iter").is_some(),
            "std re-export spelling must match"
        );
        assert!(
            recognize("<std::slice::iter::Iter<'_, u8> as std::iter::Iterator>::next").is_some()
        );
    }

    /// A USER trait implemented ON the slice iterator must NOT match: the trait
    /// segment is checked against a closed `core`/`std` list.
    #[test]
    fn user_trait_on_the_slice_iterator_is_rejected() {
        assert_eq!(recognize("<core::slice::iter::Iter<'_, u8> as my_crate::Advance>::next"), None);
        assert_eq!(recognize("<&[u8; 4] as my_crate::IntoIterator>::into_iter"), None);
    }

    /// A DIFFERENT std iterator that happens to implement `Iterator` is not this
    /// summary's subject; its `next` must not be summarized as a slice advance.
    #[test]
    fn other_std_iterators_are_rejected() {
        assert_eq!(
            recognize(
                "<core::ops::range::Range<u8> as core::iter::traits::iterator::Iterator>::next"
            ),
            None
        );
        assert_eq!(
            recognize(
                "<core::slice::iter::IterMut<'_, u8> as core::iter::traits::iterator::Iterator>::next"
            ),
            None
        );
    }

    /// `&mut [T; N]` yields `&mut T` and is excluded — its elements are not
    /// fixed for the borrow, so the value summary would not be exact.
    #[test]
    fn mutable_array_reference_into_iter_is_rejected() {
        assert_eq!(
            recognize("<&mut [u8; 4] as core::iter::traits::collect::IntoIterator>::into_iter"),
            None
        );
        // Owned `[T; N]` by-value `into_iter` yields `T`, not `&T`; not summarized.
        assert_eq!(
            recognize("<[u8; 4] as core::iter::traits::collect::IntoIterator>::into_iter"),
            None
        );
        // A slice (unsized, runtime length) is not a fixed-size array.
        assert_eq!(
            recognize("<&[u8] as core::iter::traits::collect::IntoIterator>::into_iter"),
            None
        );
    }

    /// Neither an inherent method nor a free function decomposes.
    #[test]
    fn non_qualified_paths_do_not_decompose() {
        assert_eq!(split_qualified("core::slice::iter::Iter::next"), None);
        assert_eq!(split_qualified("my_crate::next"), None);
        assert_eq!(recognize("core::panicking::panic"), None);
        assert_eq!(recognize(""), None);
        assert_eq!(recognize("<"), None);
        assert_eq!(recognize("<>::"), None);
    }

    fn option_ref_u8(none_first: bool) -> Ty {
        let payload =
            Ty::Ref { mutable: false, inner: Box::new(Ty::Int { width: 8, signed: false }) };
        let none = VariantDef { name: "None".into(), discriminant: 0, fields: Vec::new() };
        let some = VariantDef {
            name: "Some".into(),
            discriminant: 1,
            fields: vec![("0".into(), payload)],
        };
        let variants = if none_first { vec![none, some] } else { vec![some, none] };
        Ty::Adt {
            name: "core::option::Option".into(),
            fields: Vec::new().into(),
            variants: variants.into(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            layout: None,
            enum_layout: None,
            adt_kind: Some(AdtKind::Enum),
            arbitrary_precision: None,
            validity_wrapper: None,
        }
    }

    #[test]
    fn option_shape_is_located_by_structure_not_by_position() {
        let u8ty = Ty::Int { width: 8, signed: false };
        let a = option_ref_variant_shape(Some(&option_ref_u8(true)), &u8ty).expect("shape");
        assert_eq!((a.none_index, a.some_index), (0, 1));
        let b = option_ref_variant_shape(Some(&option_ref_u8(false)), &u8ty).expect("shape");
        assert_eq!((b.none_index, b.some_index), (1, 0));
    }

    /// The element type must MATCH: an `Option<&u16>` is not the return of a
    /// `next` over `[u8; N]`, and admitting it would decorrelate the payload
    /// from the array it is supposed to come from.
    #[test]
    fn element_type_mismatch_is_rejected() {
        assert!(
            option_ref_variant_shape(
                Some(&option_ref_u8(true)),
                &Ty::Int { width: 16, signed: false }
            )
            .is_none()
        );
        // A non-`Option` ADT, an un-classified ADT, and a non-ADT all decline.
        assert!(option_ref_variant_shape(Some(&Ty::Bool), &Ty::Bool).is_none());
        assert!(option_ref_variant_shape(None, &Ty::Bool).is_none());
    }
}
