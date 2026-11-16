// Trust: 2026-09-16 (rounds A6–A8) — THE `__slice_len` NAME LICENCE, shared by EVERY
// producer that INLINES `slice_len_formula(..)` into a fact keyed on another name.
//
// `slice_len_formula(s)` returns the VARIABLE `{s}__slice_len`, and
// `path_defs::write_covers_derived_slice_len` makes every whole write of `s` a write of
// that derived name too: the version rename rebinds it exactly as it rebinds `s`. A
// producer that inlines the name into a GLOBAL fact — a range payload's `i < end`, an
// enumerate index's `0 <= i < len`, `Ord::min`'s `dest <= len`, a modulo divisor, a
// downward-induction bound — states a claim about EVERY version of `s`, and
// `generate::safety` conjoins it onto every VC AFTER the rename, so it lands on
// whichever version is terminal in the block under proof. False the moment `s` is
// reseated:
//
//   * the yield lane: `for i in 0..s.len() { s = b; s[i] }` PROVED, kernel-certified,
//     at `-Copt-level=1` on the pristine driver (round A6/A7 — `a7_*` rows of
//     `tests/escaped_local_seam_realmir.rs`);
//   * the min lane, round A8 (the second adversarial review): `fn f(mut s: &[u8],
//     b: &[u8]) { let n = s.len().min(100); s = b; s[..n] }` — `callee_summaries::
//     param_slice_len` licensed the root by `is_parameter(root)` ALONE ("only then is
//     the length immutable"), `build_min_max_facts` emitted `n <= s__slice_len`, the
//     rename bound it to the post-reseat version `#s1_0`, and the `RangeTo` violation
//     `n > s__slice_len#s1_0` went UNSAT: PROVED, `assurance = Certified`, on the sealed
//     driver and on stage1, at `-O0` and `-O1`, while `f(&[1,2,3,4,5], &[1])` panics.
//     Same on `min_reseat_index_bug`, `min_reseat_local_bug` (a `let mut s = a` that
//     `-O1` copy-propagates onto the parameter) and the loop form `min_loop_bug`, where
//     the yield lane's bare bound `i < _5` composed with the min lane's `_5 <=
//     s__slice_len` (`a8_min_*` rows).
//
// THE LICENCE IS ONE QUESTION, asked here and nowhere else: the name is a name of ONE
// value iff the place that OWNS the length metadata ([`metadata_owner`]) is
// `local_defs::path_is_single_static_assignment` — bound once for the whole body,
// never mutably aliased, with writes STRICTLY INSIDE it ignored — and the same holds
// of every place the block encoder's length ties can equate it with
// ([`slice_len_name_is_stable`]'s chain). A miss returns `None`, and every caller
// declines: no fact, never a fact on a bare fallback name.
//
// WHY THE PATH QUESTION AND NOT `is_single_static_assignment(root)`. Round A7 asked
// the local question and additionally refused any projected write of the root. On a
// `&mut [T]` root that refuses the element store `(*s)[i] = v` (a projected write) and
// rustc's `&raw const (*s)` / `&mut (*s)` reborrows (an `Escape` of `s`) — neither of
// which can change the fat pointer's length, as the encoder itself asserts
// (`guards::push_borrow_slice_len` ties `{dest}__slice_len == referent_len` for both).
// Measured at `-O1`: fifteen correct functions / nineteen `SliceBoundsCheck` rows,
// including `for i in 0..s.len() { s[i] = 0 }`, regressed PROVED → refuted. The path
// question ignores everything strictly inside the owner and refuses everything at or
// above it (`a8_ctl_mut_*` rows, MUST-PROVE, both levels).

use super::*;

/// [`crate::slice_len_formula`] for a slice/str place, when the term it returns may be
/// INLINED into a fact keyed on another name or into a violation; `None` when the
/// length is a `{root}__slice_len` NAME whose owner is not single-valued
/// ([`slice_len_name_is_stable`]).
///
/// A constant length (`&[T; N]`, `[T; N]`, a const-generic array's per-param symbol)
/// is not a name of any local and is returned as is.
pub(super) fn licensed_slice_len_formula_place(
    func: &VerifiableFunction,
    place: &Place,
    fuel: u32,
) -> Option<Formula> {
    let len = crate::place_slice_len_formula(func, place)?;
    if !formula_is_slice_len_name(&len) {
        return Some(len);
    }
    slice_len_name_is_stable(func, place, fuel).then_some(len)
}

pub(super) fn licensed_slice_len_formula(
    func: &VerifiableFunction,
    operand: &Operand,
    fuel: u32,
) -> Option<Formula> {
    let (Operand::Copy(place) | Operand::Move(place)) = operand else { return None };
    licensed_slice_len_formula_place(func, place, fuel)
}

/// Whether `f` is a `{place}__slice_len` variable — a NAME the version rename rebinds
/// on every whole write of `place`'s owner — as opposed to a constant or a
/// const-generic per-param symbol (which deliberately does not carry the suffix).
pub(super) fn formula_is_slice_len_name(f: &Formula) -> bool {
    matches!(f, Formula::Var(name, _) if name.ends_with(SLICE_LEN_SUFFIX))
}

/// The place whose STORAGE carries the length that `slice_len_formula(place)` names.
///
/// A fat pointer or reference (`&[T]`, `&mut [T]`, `*const [T]`, `&str`) carries its
/// length as metadata: the owner is the place itself. An UNSIZED `[T]` / `str` place is
/// reached through a `Deref` of such a pointer, and its length IS that pointer's
/// metadata: the owner is the place with the trailing `Deref` removed — so a borrow or
/// an element store of `(*s)` is `Inside` the owner `s`, not a rebinding of it. A
/// sized array's length is part of its type and needs no licence at all (the formula
/// is a constant, and [`licensed_slice_len_formula`] never asks). Anything else is
/// not a place this lane names a length of: `None`.
pub(super) fn metadata_owner(func: &VerifiableFunction, place: &Place) -> Option<Place> {
    // Trust: 2026-09-16 (round A9) — an owner reached through `Index(l)` with a
    // multi-valued `l` (`(*s)[j]` with `j` reseated) is not ONE place: the name
    // `s*[_j]__slice_len` is the length of whichever slice `j` selects at each read,
    // and no chain hop below can make it single-valued. Refused here so every caller
    // — the owner and every re-rooted hop of `slice_len_name_is_stable` — declines.
    // (`index_local_min_bug`, `index_local_min_let_bug`, `index_local_len_end_bug`.)
    if !crate::local_defs::place_index_locals_are_single_static_assignment(func, place) {
        return None;
    }
    let ty = crate::place_ty_cow(func, place)?;
    match ty.as_ref() {
        Ty::Ref { .. } | Ty::RawPtr { .. } => Some(place.clone()),
        Ty::Slice { .. } | Ty::Str => {
            let mut owner = place.clone();
            // An unsized place that is NOT behind a `Deref` (a field of an unsized
            // struct) has no pointer prefix this lane can name: fail closed.
            (owner.projections.pop()? == trust_types::Projection::Deref).then_some(owner)
        }
        _ => None,
    }
}

/// True iff the `{place}__slice_len` name is a name of ONE value: the place that owns
/// its metadata ([`metadata_owner`]) is `local_defs::path_is_single_static_assignment`
/// — every prefix bound exactly once (a never-written parameter's entry definition
/// counts), no destruction or mutable alias of a prefix, writes strictly inside it
/// ignored — is not read through a raw deref, and the same holds of every place along
/// the chain of whole-local `Use`/`Ref`/`CopyForDeref` hops from the owner's root's
/// one definition — the chain the block encoder ties lengths along (`_7 = copy _2;
/// PtrMetadata(move _7)` ties `_7__slice_len` to `_2__slice_len`, so a reseat of `_2`
/// can reach the name through the tie even though `_7` itself is written once). An
/// `as_bytes` result is keyed on its RECEIVER (`slice_len_formula` redirects there), so
/// the receiver's chain is what is gated.
///
/// A projected owner (`(*h).s`) hops by RE-ROOTING: `h = copy g` makes it `(*g).s`,
/// `h = &r` makes it `r.s`; a root with no whole-local hop (a parameter, a call
/// destination, an aggregate) ends the chain at the owner already licensed above.
///
/// A hop onto a place whose length is a constant ends the chain stable: a reference to
/// a fixed-size array has the same length whatever the array holds. `fuel` bounds the
/// walk; exhausted fuel is a refusal.
///
/// WHY THE WHOLE CHAIN AND NOT ONLY THE KEYED PLACE. A fact keyed on a single-write
/// temp's derived name is true of that name; what makes the chain load-bearing is that
/// the encoder's length ties and canonicalizations can equate the temp's name with a
/// root's: the `let n = s.len(); for i in 0..n { s = ..; s[i] }` shape (`let_n_reseat`,
/// `-O1`) PROVED on round A6 of this tree through exactly such a substitution — `n`'s
/// one definition `PtrMetadata(copy s)` was canonicalized to the reseatable
/// `s__slice_len` although `n` itself has one version. Gating every place on the chain
/// means the name inlined into the fact can be tied only to names with one version.
pub(super) fn slice_len_name_is_stable(
    func: &VerifiableFunction,
    place: &Place,
    fuel: u32,
) -> bool {
    if fuel == 0 || crate::place_has_raw_deref(func, place) {
        return false;
    }
    let Some(owner) = metadata_owner(func, place) else { return false };
    // `path_is_single_static_assignment` checks `place_index_locals_are_single_static_assignment`
    // first (`body_path_is_single_static_assignment` refuses a multi-valued `Index(l)`), so a
    // re-rooted hop that carries the owner's projections onto a new root is gated on
    // every level it is asked at.
    if !crate::local_defs::path_is_single_static_assignment(func, &owner) {
        return false;
    }
    let local = owner.local;
    if crate::local_defs::is_parameter(func, local) {
        return true;
    }
    // `slice_len_formula` keys an `as_bytes()` result on its receiver's length: the
    // receiver is the local the name is really about.
    if owner.projections.is_empty()
        && let Some(receiver) = crate::guards::as_bytes_length_receiver(func, local)
    {
        return match receiver {
            Operand::Copy(q) | Operand::Move(q) => slice_len_name_is_stable(func, q, fuel - 1),
            _ => false,
        };
    }
    // The hop: the owner's root re-rooted onto its one whole-local definition.
    let hop = match crate::local_defs::unique_value_def(func, local) {
        Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q))) | Some(Rvalue::CopyForDeref(q)) => {
            let mut hop = q.clone();
            hop.projections.extend(owner.projections.iter().cloned());
            hop
        }
        Some(Rvalue::Ref { place: q, .. }) => {
            // `root = &q`: `(*root)` IS `q`, so a `Deref`-first owner re-roots onto `q`
            // and a projection-free owner (the reference itself) hops to `q`, whose
            // length its metadata was copied from.
            let mut hop = q.clone();
            match owner.projections.split_first() {
                None => {}
                Some((trust_types::Projection::Deref, rest)) => {
                    hop.projections.extend(rest.iter().cloned())
                }
                // A projected owner that does not go through the reference's deref
                // (`root.f` on a reference type) is not a shape this lane names.
                Some(_) => return false,
            }
            hop
        }
        // A call destination, a cast, an aggregate, a never-written parameter: the
        // chain ends here, at a place already licensed above.
        _ => return true,
    };
    match crate::place_slice_len_formula(func, &hop) {
        // A constant length is not a name; the chain ends stable.
        Some(len) if !formula_is_slice_len_name(&len) => true,
        _ => slice_len_name_is_stable(func, &hop, fuel - 1),
    }
}
