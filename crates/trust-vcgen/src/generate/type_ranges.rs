// Range hypotheses implied by a local's declared type: scalar carrier bounds,
// datatype field bounds reached through projections, and slice-length bounds
// for non-zero-sized element types. These are the always-true facts every VC
// in the function may assume.

use super::*;

/// Conjoin the declared-type carrier onto every integer/`char` LOCAL/temp
/// the `formula` references — the sibling of `conjoin_arg_type_ranges` for the
/// NON-parameter locals (return slot + temporaries). VC-gen lowers an
/// `i8`/`u32`/…/`char`
/// local to the unbounded `Sort::Int`, dropping the invariant that the value is
/// within its type range; an overflow/cast/index VC over such a local can then be
/// FALSE-REFUTED by the solver picking an out-of-type-range value (e.g. a `u32`
/// local set to `i128::MAX`). Re-attaching the true range fact `in_range(local)`
/// discharges those spurious refutations.
///
/// SOUNDNESS: DROP-ONLY in the FALSE-PROVE direction — `in_range(local)` is a TRUE
/// fact about a Rust scalar local (its value always lies within its declared
/// type range), so conjoining it can only PROVE a genuinely-safe obligation, never
/// hide a real violation (a value genuinely able to overflow is still in range, and
/// the overflow VC over it stays refutable). It is GENERAL — fixed-width integers
/// plus the exact Unicode-scalar `char` carrier, with no datatype modeling.
/// Parameters are skipped (already bounded by
/// `conjoin_arg_type_ranges`); FIELD-projecting vars keep their projection chars in
/// the var name and so never alias a bare-local key (field bounds are a separate,
/// datatype-aware concern not modeled here).
pub(super) fn conjoin_local_type_ranges(func: &VerifiableFunction, formula: Formula) -> Formula {
    conjoin_local_type_ranges_excluding(func, formula, &FxHashSet::default())
}

/// Base var names of checked-arith RESULT VALUES and their COPY CLOSURE: the
/// `_R.0` of every local `_R: (intT, bool)` (rustc's `*WithOverflow` checked-op
/// tuple; `.0` is the wrapped value, `.1` the overflow flag), plus every local
/// whose unique whole-local definition is a pure `Use` copy chain ending in one
/// (`_0 = _R.0`, `let c = a - b;` → `c = _R.0`). The closure matters: the value
/// flows out of the tuple immediately, and any copy carries the same circularity.
///
/// SOUNDNESS ROLE (the unsigned-subtraction vacuous-UNSAT false-accept,
/// confirmed live on `pub fn sub(a: usize, b: usize) -> usize { a - b }`, which
/// verified CLEAN though it underflows for `a < b` — and interprocedurally
/// `caller { sub(2, 5) }` was PROVED): the VC lane conjoins the usize type-range
/// `0 <= X` for every integer local X onto ArithmeticOverflow VCs; block-defs
/// tie `X = a - b` (through the copy chain), so the underflow goal `a - b < 0`
/// plus `0 <= X` is UNSAT — the obligation is vacuously "proved" by ASSUMING the
/// very no-underflow property it checks. Excluding the closure's type-ranges
/// from ArithmeticOverflow VCs removes exactly that circular premise. SOUND by
/// construction: it only WITHHOLDS a premise, so the solver can only refute
/// MORE, never less — no false PROVE can be introduced. Precision is preserved
/// where it is legitimate: a guard (`if a >= b`) discharges via path guards, a
/// checked op's passed assert discharges downstream reads via the semantic
/// assert-passed guards, and reassigned/multi-def locals (loop accumulators)
/// are NOT in the closure (unique-def only), so their ranges remain.
pub(super) fn checked_arith_result_value_vars(func: &VerifiableFunction) -> FxHashSet<String> {
    let mut set = FxHashSet::default();
    for decl in &func.body.locals {
        if let Ty::Tuple(fields) = &decl.ty
            && fields.len() == 2
            && fields[0].int_width().is_some()
            && matches!(fields[1], Ty::Bool)
        {
            let place =
                Place { local: decl.index, projections: vec![trust_types::Projection::Field(0)] };
            set.insert(place_to_var_name(func, &place));
        }
    }
    if set.is_empty() {
        return set;
    }
    // Copy closure: a local whose UNIQUE whole-local def is `Use(copy/move p)`
    // with `p` already in the set holds the same checked-result value. Iterate
    // to fixpoint (chains like `_0 = c; c = _R.0` resolve regardless of order).
    loop {
        let mut grew = false;
        for decl in &func.body.locals {
            let name = place_to_var_name(func, &Place::local(decl.index));
            if set.contains(&name) {
                continue;
            }
            if let Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p))) =
                crate::local_defs::unique_value_def(func, decl.index)
                && set.contains(&place_to_var_name(func, p))
            {
                set.insert(name);
                grew = true;
            }
        }
        if !grew {
            break;
        }
    }
    set
}

/// As [`conjoin_local_type_ranges`], but skips any local whose base var name is
/// in `exclude`. Used on ArithmeticOverflow VCs to drop the CHECKED-OP RESULT
/// copy closure's own type-ranges (see [`checked_arith_result_value_vars`]).
pub(super) fn conjoin_local_type_ranges_excluding(
    func: &VerifiableFunction,
    formula: Formula,
    exclude: &FxHashSet<String>,
) -> Formula {
    let ranges = local_scalar_range_map(func);
    if ranges.is_empty() {
        return formula;
    }
    let mut names: FxHashSet<String> = FxHashSet::default();
    collect_formula_var_names(&formula, &mut names);
    let mut bounds = Vec::new();
    for name in &names {
        // Strip the `#…` SSA-version suffix to recover the base local name; a
        // field/deref var keeps its projection chars and so never matches a key.
        let base = name.split('#').next().unwrap_or(name.as_str());
        if exclude.contains(base) {
            continue;
        }
        if let Some(&range) = ranges.get(base) {
            bounds.push(crate::range::rust_scalar_range_constraint(
                &Formula::Var(name.clone(), trust_types::Sort::Int),
                range,
            ));
        }
    }
    if bounds.is_empty() {
        return formula;
    }
    bounds.push(formula);
    Formula::And(bounds)
}

/// Build `base_local_var_name -> RustScalarRange` for every integer/`char`
/// LOCAL/temp that `conjoin_local_type_ranges` may soundly range-bound. Keyed by
/// `place_to_var_name(func, Place::local(i))` so the key is the EXACT base var name
/// the formula uses for that bare local. PARAMETERS are skipped (already bounded by
/// `conjoin_arg_type_ranges`). Local 0 (the return slot) IS included: it is a
/// scalar local like any other when the return type is supported, and its
/// bound is a true fact about the returned value.
pub(super) fn local_scalar_range_map(
    func: &VerifiableFunction,
) -> FxHashMap<String, crate::range::RustScalarRange> {
    let mut map = FxHashMap::default();
    for decl in &func.body.locals {
        // Skip parameters: `conjoin_arg_type_ranges` already bounds 1..=arg_count.
        if decl.index >= 1 && decl.index <= func.body.arg_count {
            continue;
        }
        let Some(range) = crate::range::rust_scalar_range(&decl.ty) else {
            continue;
        };
        let name = place_to_var_name(func, &Place::local(decl.index));
        map.insert(name, range);
    }
    map
}

/// Conjoin exact scalar-carrier bounds for every integer/`char` datatype
/// FIELD the `formula` references (Lever A). `conjoin_arg_type_ranges` bounds only
/// PARAMETERS and `conjoin_local_type_ranges` bounds only bare LOCALS; a `u32`/`u64`
/// FIELD read off a modeled `Expr`/`Level`/`Name` datatype value is modeled as
/// `Formula::Var(name, Sort::Int)` (the unbounded mathematical Int), so it loses its
/// `0 ..= u32::MAX` Rust-type invariant and the solver false-refutes a safe
/// overflow/index check by setting the field to `u64::MAX`. Conjoin `min ≤ x ≤ max`
/// for the field's OWN declared type.
///
/// SOUNDNESS: a Rust-type invariant that holds for EVERY inhabitant of the field, so
/// it can only delete impossible counterexamples, never a real violation (whose
/// witness also respects the type range) and never a false PROVE. Constrained ONLY
/// to the field's ACTUAL declared integer width/signedness or Unicode-scalar
/// `char` carrier; keyed by the EXACT
/// `place_to_var_name` of a FIELD-projecting place so it attaches only to a name the
/// formula references; conjoining an in-range fact onto an already-in-range value is
/// a harmless `true`.
pub(super) fn conjoin_datatype_field_ranges(
    func: &VerifiableFunction,
    formula: Formula,
) -> Formula {
    conjoin_datatype_field_ranges_excluding(func, formula, &FxHashSet::default())
}

/// As [`conjoin_datatype_field_ranges`], but skips any field whose base var name
/// (SSA-version suffix stripped) is in `exclude`. On an ArithmeticOverflow VC
/// this drops the CHECKED-OP RESULT's own field-range `0 <= _R.0` — the tuple
/// value of a `*WithOverflow` op is a field-projecting place, so the raw result
/// read is bounded by THIS conjoin, while its bare-local copies are bounded by
/// `conjoin_local_type_ranges` (see [`checked_arith_result_value_vars`]).
pub(super) fn conjoin_datatype_field_ranges_excluding(
    func: &VerifiableFunction,
    formula: Formula,
    exclude: &FxHashSet<String>,
) -> Formula {
    let ranges = datatype_field_range_map(func);
    if ranges.is_empty() {
        return formula;
    }
    let mut names: FxHashSet<String> = FxHashSet::default();
    collect_formula_var_names(&formula, &mut names);
    let mut bounds = Vec::new();
    for name in &names {
        let base = name.split('#').next().unwrap_or(name.as_str());
        if exclude.contains(base) {
            continue;
        }
        // `datatype_field_range_map` is keyed by the unversioned place spelling
        // (`value.0`), while a VC normally reads the reaching-definition spelling
        // (`value.0#sB_K`). Look up by the same base used by the exclusion gate,
        // but constrain the exact versioned symbol that occurs in this formula.
        // Looking up by `name` silently dropped every range as soon as SSA
        // versioning was present, allowing out-of-type-range false witnesses.
        if let Some(&range) = ranges.get(base) {
            bounds.push(crate::range::rust_scalar_range_constraint(
                &Formula::Var(name.clone(), trust_types::Sort::Int),
                range,
            ));
        }
    }
    if bounds.is_empty() {
        return formula;
    }
    bounds.push(formula);
    Formula::And(bounds)
}

/// Build `var_name -> RustScalarRange` for every `Copy`/`Move`/place-valued
/// position in the body that projects through a FIELD and resolves to an
/// integer/`char` scalar — the fields `conjoin_datatype_field_ranges` may soundly
/// range-bound.
/// Keyed by `place_to_var_name` so the names match the formula's free vars EXACTLY.
///
/// Restricted to field-PROJECTING places: a bare integer local is already bounded by
/// `conjoin_local_type_ranges` / `conjoin_arg_type_ranges`, and bounding only fields
/// keeps this orthogonal. Built from every place the body mentions (a total walk that
/// fails closed on any operand position it does not recognize — a missed field merely
/// gets no bound, conservative, never a false prove).
pub(super) fn datatype_field_range_map(
    func: &VerifiableFunction,
) -> FxHashMap<String, crate::range::RustScalarRange> {
    let mut map = FxHashMap::default();
    let mut record = |place: &Place| {
        // Only FIELD-projecting places (a bare local is bounded elsewhere).
        if !place.projections.iter().any(|p| matches!(p, trust_types::Projection::Field(_))) {
            return;
        }
        // The field must resolve to an integer/`char` scalar — those are the
        // carriers whose lowering to unbounded `Sort::Int` erases a Rust range.
        let Some(range) = resolve_field_scalar_range(func, place) else {
            return;
        };
        map.insert(place_to_var_name(func, place), range);
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            for_each_stmt_copy_move_place(stmt, &mut record);
        }
        for_each_terminator_copy_move_place(&block.terminator, &mut record);
    }
    map
}

/// Resolve a field-projecting place to an exact Rust scalar carrier IFF it lands
/// on an integer or `char` field. Datatype-AWARE: the core `place_ty`/`project_ty`
/// field arms resolve `Ty::Tuple`/`Ty::Adt`/`Ty::Closure` fields but NOT
/// `Ty::Datatype` fields (the Lever A modeled `Expr`/`Level`/`Name` cluster), so
/// a field read off a modeled datatype value otherwise resolves to `None` and the
/// `u32` field is left unbounded — exactly the gap. This walks the projections
/// itself, descending `Ty::Datatype` field-by-field (an enum field via
/// `Downcast(v).Field(i)`, a struct-like datatype field via a bare `Field(i)` on
/// variant 0), and defers to `project_ty` for every non-datatype step. Returns
/// `None` (no bound — conservative) for anything it cannot type as a supported
/// scalar. SOUNDNESS: read-only type resolution; it never changes a VC, only
/// decides whether a sound range fact is attachable to the field's var.
///
/// The same variant-aware walk is required for a REAL Rust enum (`Ty::Adt`), and
/// for the same reason `project_ty` cannot supply it: `Ty::Adt::fields` is the
/// FLAT union/struct view an enum carries for the `SetDiscriminant` lowering —
/// `[("__tag", i64), ("__v0_0", …), ("__v1_0", …)]` — so `project_ty` answers a
/// variant-relative `Field(i)` with the flat slot `i`, which for every
/// `Downcast(v).Field(0)` is `__tag: i64`. That is not a missing bound but a
/// WRONG one, and it is wrong in BOTH directions:
///
///   * a payload NARROWER than `i64` (`u8`/`u16`/`u32`) gets only the useless
///     `i64` range, so a safe obligation whose safety comes from the payload's
///     own declared width is FALSE-REFUTED;
///   * a payload WIDER in the unsigned direction (`u64`, `u128`, `i128`) gets a
///     range that EXCLUDES its real values, deleting the genuine counterexample
///     — a FALSE PROOF (`enum_payload_range_tests` pins both directions).
///
/// The variant field type read here is the one the ADT declares, so the emitted
/// range is exactly the `u8 -> [0,255]` authority class `type_ranges` already
/// uses for locals and parameters — no new axiom.
///
/// An enum carries the declared payload type in TWO places, and this walk reads
/// the one the REST of the pipeline reads. `crate::place_ty_cow` — the resolver
/// every other lane types this same place with — answers a `Downcast(v).Field(i)`
/// on a `Ty::Adt` from the FLAT view's `__v{v}_*` slots and never consults
/// `variants` at all. The SMT var this range fact is attached to is the one
/// `place_to_var_name` mints for that place, and everything else said about that
/// var is derived from `place_ty`'s answer; a bound taken from a DIFFERENT
/// declaration of the same field would be a bound about a different type. So
/// [`enum_variant_field_ty`] resolves the flat `__v{v}_*` slots FIRST, exactly as
/// `place_ty_cow` does, and only falls back to the P4 `variants` list for shapes
/// that declare variants without the synthetic flat names.
///
/// FAIL-CLOSED on a bare `Field` over a `Ty::Adt` enum, and deliberately NOT
/// resolved through variant 0 the way the `Ty::Datatype` arm does. Without a
/// `Downcast` there is no variant to read a declared type FROM: the flat step's
/// answer for `Field(0)` is the synthetic `__tag`, the wrong bound this walk
/// exists to stop emitting, and resolving it through variant 0 instead would
/// bound a slot that is not variant 0's payload by variant 0's declared type.
/// The var name carries the downcast (`e@0.0` vs `e.0`), so declining the
/// un-downcast spelling withholds a bound from a DIFFERENT var than the payload
/// reads use, and costs them nothing
/// (`bare_field_on_multivariant_adt_enum_is_unbounded`).
///
/// NO BOUND BEATS A WRONG BOUND — and the enum decision may NOT be keyed on
/// `Ty::Adt::variants` being non-empty. That field is `#[serde(default)]` on
/// purpose (`trust_types::Ty::Adt`), so EVERY pre-P4 serialized `Ty::Adt` — dump
/// fixtures, solver caches, proof certificates — deserializes with
/// `variants: []` while KEEPING the enum-shaped flat view. Gating the
/// variant-aware walk on `!variants.is_empty()` would send exactly those inputs
/// back down the flat step and answer `Downcast(v).Field(0)` with `__tag: i64`
/// again — the false-proof direction, measured (see
/// `variants_erased_by_serde_default_answers_the_payload_slot_not_the_tag`).
/// So the walk decides ENUM-NESS from what is PRESENT — a pending `Downcast`,
/// the declared `variants`, the `adt_kind` stamp, or the synthetic flat-view
/// field names — and DECLINES (returns `None`, emitting no range fact) whenever
/// the shape is enum-relative and NEITHER declaration of the payload's type can
/// answer it. See [`adt_shape_is_enum`] and [`enum_variant_field_ty`].
///
/// Declining is the last resort, not the first: the pre-P4 wire shape still
/// carries the payload's declared type in its `__v{v}_*` slots, so on that shape
/// the walk answers with the DECLARED type rather than dropping the fact. It
/// drops the fact only where no declaration of that field survives at all.
pub(super) fn resolve_field_scalar_range(
    func: &VerifiableFunction,
    place: &Place,
) -> Option<crate::range::RustScalarRange> {
    // verifier-perf: walk the declared type by REFERENCE (no fat-root clone), cloning
    // only the small resolved field — this classifies its scalar carrier at the end.
    use std::borrow::Cow;
    let mut ty: Cow<'_, Ty> = Cow::Borrowed(crate::local_ty_ref(func, place.local)?);
    let mut pending_variant: Option<usize> = None;
    for proj in &place.projections {
        match proj {
            trust_types::Projection::Downcast(v) => {
                pending_variant = Some(*v);
            }
            trust_types::Projection::Field(idx) => {
                // Decide the step from the type ALONE first: the flat arm MOVES
                // `ty`, which cannot happen while `ty.as_ref()` is borrowed.
                let step = match ty.as_ref() {
                    Ty::Datatype { variants, .. } => {
                        // A `Field` after a `Downcast(v)` selects variant v's
                        // i-th field; a bare `Field` on a single-variant
                        // (struct-like) datatype selects variant 0's i-th
                        // field. A multi-variant datatype with no preceding
                        // downcast is ambiguous — fail closed (no bound).
                        let v = match pending_variant {
                            Some(v) => Some(v),
                            None if variants.len() == 1 => Some(0),
                            None => None,
                        };
                        match v.and_then(|v| variants.get(v)).and_then(|(_, f)| f.get(*idx)) {
                            Some((_, field_ty)) => FieldStep::Variant(field_ty.clone()),
                            None => FieldStep::Decline,
                        }
                    }
                    Ty::Adt { variants, fields, adt_kind, .. } => {
                        if pending_variant.is_some()
                            || adt_shape_is_enum(variants, fields, adt_kind)
                        {
                            // Enum-relative: ONLY a DECLARED per-variant field
                            // type may answer it. A bare `Field` (no `Downcast`)
                            // names the flat aggregate slot every variant's
                            // payload is written to, so no variant's declared
                            // type bounds it — decline. With a `Downcast(v)`,
                            // `enum_variant_field_ty` answers from whichever
                            // declaration this value still carries.
                            match pending_variant
                                .and_then(|v| enum_variant_field_ty(variants, fields, v, *idx))
                            {
                                Some(field_ty) => FieldStep::Variant(field_ty),
                                None => FieldStep::Decline,
                            }
                        } else {
                            // A struct/union `Ty::Adt`: the flat view IS the
                            // field list, so `project_ty`'s step is correct.
                            FieldStep::Flat
                        }
                    }
                    // Tuples/closures/arrays have no variants, so a pending
                    // `Downcast` means the place is variant-relative against a
                    // type that cannot express variants (a coroutine frame's
                    // state field, a corrupted place). `project_ty` would answer
                    // with slot `idx` of the un-downcast view — a DIFFERENT slot.
                    _ if pending_variant.is_some() => FieldStep::Decline,
                    _ => FieldStep::Flat,
                };
                pending_variant = None;
                match step {
                    FieldStep::Decline => return None,
                    FieldStep::Variant(field_ty) => ty = Cow::Owned(field_ty),
                    FieldStep::Flat => ty = crate::step_place_ty_cow(ty, proj)?,
                }
            }
            _ => {
                pending_variant = None;
                ty = crate::step_place_ty_cow(ty, proj)?;
            }
        }
    }
    crate::range::rust_scalar_range(ty.as_ref())
}

/// How [`resolve_field_scalar_range`] takes one `Field` step.
enum FieldStep {
    /// Resolved through the ADT's declared variant list.
    Variant(Ty),
    /// Resolved through `project_ty`'s flat field view (struct/tuple/closure).
    Flat,
    /// Enum-relative but unanswerable from the declared variants: emit NO range
    /// fact. Losing a bound costs precision; keeping a wrong one is a false
    /// proof.
    Decline,
}

/// Variant `v`'s `idx`-th DECLARED field type on a `Ty::Adt` enum, read from
/// whichever of the two declarations this value still carries.
///
/// `lower_enum_adt` writes the payload's type into the enum TWICE, in one loop,
/// in one order: the flat union view gets `("__v{v}_{field_name}", ty)` and the
/// P4 per-variant view gets `VariantDef { fields: [(field_name, ty)] }`. Only the
/// flat half is `Serialize`d unconditionally — `variants` is `#[serde(default)]`,
/// so it is ABSENT from every `Ty::Adt` written before PHASE 4 (dump fixtures,
/// solver caches, proof certificates) while the flat half survives verbatim.
///
/// The flat half is therefore consulted FIRST, and not only because it is the
/// half that survives: it is the half `crate::place_ty_cow` uses. That function
/// resolves a `Downcast(v).Field(i)` on a `Ty::Adt` by taking the `i`-th field
/// whose name carries the `__v{v}_` prefix and does not read `variants` at all,
/// so it is the flat view that decides what type the rest of vcgen ascribes to
/// this place. A range fact is a statement about the var `place_to_var_name`
/// mints for that place; taking its width from the other declaration would state
/// it about a different type than every other fact on the same var.
///
/// The prefix identifies the variant exactly — `__v1_` cannot match variant 11's
/// `__v11_0`, because the trailing `_` of the prefix is a digit there — and the
/// slots are pushed variant-by-variant in declaration order, so the `i`-th
/// `__v{v}_`-prefixed slot IS variant `v`'s `i`-th declared field.
///
/// Returns `None` when neither declaration answers — no `__v{v}_` slot at index
/// `idx` and no `variants[v].fields[idx]` — and the caller then emits no range
/// fact. `__tag` carries no `__v` prefix and is not in any variant's field list,
/// so no path through here can ever answer with it.
fn enum_variant_field_ty(
    variants: &[trust_types::VariantDef],
    fields: &[(String, Ty)],
    v: usize,
    idx: usize,
) -> Option<Ty> {
    let prefix = format!("__v{v}_");
    fields
        .iter()
        .filter(|(name, _)| name.starts_with(&prefix))
        .nth(idx)
        .or_else(|| variants.get(v).and_then(|variant| variant.fields.get(idx)))
        .map(|(_, field_ty)| field_ty.clone())
}

/// Whether a `Ty::Adt` is an ENUM, decided from what is PRESENT in the value.
///
/// `variants` alone is not a sound test: it is `#[serde(default)]`, so a
/// serialized enum whose JSON predates PHASE 4 (or whose `variants` key is
/// otherwise absent) deserializes with an EMPTY list and would read as a
/// struct. The other three signals survive that erasure independently:
///
///   * `adt_kind: Some(Enum)` — stamped by `trust-mir-extract`'s enum arm from
///     rustc's `AdtDef`;
///   * a `__tag` field — `lower_enum_adt` unconditionally leads the flat union
///     view with the discriminant slot, and nothing else emits that name;
///   * a `__v{variant}_{field}` field — the same lowering's per-variant payload
///     slots.
///
/// A struct that literally declares a field named `__tag`/`__v0_x` is
/// misclassified as an enum and simply loses its field range fact — a precision
/// cost in the SAFE direction, and the reserved-looking spelling makes it rare.
fn adt_shape_is_enum(
    variants: &[trust_types::VariantDef],
    fields: &[(String, Ty)],
    adt_kind: &Option<trust_types::AdtKind>,
) -> bool {
    !variants.is_empty()
        || matches!(adt_kind, Some(trust_types::AdtKind::Enum))
        || fields.iter().any(|(name, _)| is_enum_flat_view_field_name(name))
}

/// The synthetic field names `trust-mir-extract`'s `lower_enum_adt` gives an
/// enum's FLAT union view: the leading `__tag` discriminant slot and the
/// per-variant `__v{variant_index}_{field_name}` payload slots.
fn is_enum_flat_view_field_name(name: &str) -> bool {
    if name == "__tag" {
        return true;
    }
    let Some(rest) = name.strip_prefix("__v") else { return false };
    let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
    digits > 0 && rest.as_bytes().get(digits) == Some(&b'_')
}

/// Invoke `f` on EVERY place a statement mentions — operand reads AND place-valued
/// positions (assignment destination, `Discriminant`/`Len`/`Ref`/`CopyForDeref`
/// place reads, `SetDiscriminant`/`Drop`/`Deinit`/`Retag`/`PlaceMention`). The
/// modeled-datatype field vars the solver picks `u64::MAX` for enter VCs through
/// MANY of these channels, so the walk must be broad to build a complete map.
/// Over-collecting is SOUND: a place that never reaches a VC simply never has its
/// bound conjoined (the conjoin is gated on the name appearing FREE in the formula).
/// An unrecognized position is skipped (conservative).
pub(crate) fn for_each_stmt_copy_move_place(stmt: &Statement, f: &mut impl FnMut(&Place)) {
    match stmt {
        Statement::Assign { place, rvalue, .. } => {
            f(place);
            for_each_rvalue_copy_move_place(rvalue, f);
        }
        Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place }
        | Statement::Retag { place }
        | Statement::PlaceMention(place) => f(place),
        Statement::Intrinsic { args, .. } | Statement::Unsupported { operands: args, .. } => {
            for op in args {
                for_each_operand_copy_move_place(op, f);
            }
        }
        _ => {}
    }
}

/// Invoke `f` on every place an rvalue reads.
pub(super) fn for_each_rvalue_copy_move_place(rvalue: &Rvalue, f: &mut impl FnMut(&Place)) {
    match rvalue {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
            for_each_operand_copy_move_place(op, f);
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            for_each_operand_copy_move_place(a, f);
            for_each_operand_copy_move_place(b, f);
        }
        Rvalue::Aggregate(_, operands) | Rvalue::Unsupported { operands, .. } => {
            for op in operands {
                for_each_operand_copy_move_place(op, f);
            }
        }
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => f(place),
        _ => {}
    }
}

/// Invoke `f` on every place a terminator mentions — operand reads AND the
/// place-valued `Call` destination and `Drop` place.
pub(crate) fn for_each_terminator_copy_move_place(term: &Terminator, f: &mut impl FnMut(&Place)) {
    match term {
        Terminator::SwitchInt { discr, .. } => for_each_operand_copy_move_place(discr, f),
        Terminator::Assert { cond, .. } => for_each_operand_copy_move_place(cond, f),
        Terminator::Call { args, dest, .. } => {
            f(dest);
            for op in args {
                for_each_operand_copy_move_place(op, f);
            }
        }
        Terminator::Drop { place, .. } => f(place),
        _ => {}
    }
}

/// Invoke `f` on the place of a `Copy`/`Move` operand (no-op for constants/symbolic).
pub(super) fn for_each_operand_copy_move_place(op: &Operand, f: &mut impl FnMut(&Place)) {
    if let Operand::Copy(place) | Operand::Move(place) = op {
        f(place);
    }
}

/// Trust (NEGATIVE-LENGTH class — a FALSE REFUTATION of correct code): conjoin
/// `0 <= len` for every LENGTH quantity the `formula` already mentions.
///
/// A collection length is a `usize`, but vcgen lowers it to the UNBOUNDED
/// `Sort::Int`, so nothing stops a solver from choosing a value no execution can
/// hold. MEASURED at clean HEAD on the ordinary, non-async, loop-free
///
/// ```ignore
/// match a { [] => .., [x] => .., [x, .., y] => .. }
/// ```
///
/// whose three arms share ONE `Terminator::Unreachable` sink: the sink's path
/// condition is `len != 0 ∧ len != 1 ∧ ¬(len >= 2)`, satisfied over the integers
/// by `a__slice_len = -1`. A NEGATIVE SLICE LENGTH — so the `[unreach]` row is
/// REFUTED: the verifier ACCUSES correct code, with a witness no execution can
/// produce.
///
/// WHAT THIS CLOSES AND WHAT IT DOES NOT — read this before quoting the change as
/// a fix for a red build, because on most of these shapes it is not one.
/// RE-MEASURED per row through the real `generate_vcs` +
/// `Router::deterministic_in_process_ay` + `trust_certify::certify_vc`, at HEAD and
/// with this change, over a slice-pattern matrix (`[x, ..]`, `[.., y]`, the merged
/// 3-arm match, `&mut [T]`, `&[()]`, `match v.as_slice()`, `s.as_bytes()`,
/// `&String`, a nested `&[&[T]]` match, two slices in one body, 4- and 6-arm
/// ladders, `&[u32; 4]`, and a dozen UB canaries). Row TOTALS are deliberately not
/// quoted: they are a property of whatever matrix the measuring lane happened to
/// build, successive lanes have reported different ones, and a total in prose
/// cannot be rechecked. The INVARIANTS can be, and they are what a reader needs:
///
///  * NOTHING is lost. No row anywhere in the matrix stops refuting, and no row
///    that was `Proved` at HEAD regresses.
///  * Every row that LEAVES `Failed` is a genuinely dead `Unreachable` sink.
///  * At HEAD every one of those sinks is refuted at a NEGATIVE length; with this
///    change no surviving refutation in the matrix carries one.
///
/// The gain splits by SHAPE, not by element type. In a TWO-arm match the
/// `Unreachable` sink reaches `Proved` AND kernel-certified —
/// `tests/slice_length_nonneg_real_mir.rs` pins that on
/// `slice_two_arm_head_proved_mir.json`, whose sink is refuted at pristine HEAD.
/// Closing the SINK does not always close the FUNCTION: see the measured
/// `match a { [] => 0, [.., y] => *y }` counterexample below, whose sink is
/// discharged while its last-element `SliceBoundsCheck` stays refuted.
/// Every THREE-or-more-arm shape stops short of `Proved`. Most land in UNKNOWN,
/// including BOTH `Unreachable` fixtures this lane ships:
/// `slice_match_merged_unreachable_mir.json` (the very shape in the code block
/// above) and its `&[()]` twin `slice_match_zst_unreachable_mir.json`. With
/// `0 <= len` in context ay reports those goals UNSAT but its own proof self-check
/// rejects the multi-disequality LIA refutation
/// ("(incomplete self-check-rejected)"), a separate ay-side incompleteness this
/// lane does not touch. The one NESTED `&[&[T]]` shape in the matrix stays
/// REFUTED rather than declining — but on a witness whose lengths are all
/// non-negative, where HEAD's were not, which is the two-sided property this pass
/// claims and not a counterexample to it.
///
/// WHAT A NON-REFUTED ROW BUYS DEPENDS ON THE POLICY, and the shipped text used to
/// get this backwards. `VcKind::Unreachable` and `VcKind::Assertion` both report
/// `has_runtime_fallback == true` (`trust_types::VcKind`), so an `Unknown` or
/// `Timeout` on either is counted `failure.runtime_checked`
/// (`compiler/rustc_mir_transform/src/trust_verify.rs`) — the one bucket
/// `strict_failure_is_fatal` EXCLUDES under the default strict policy, and
/// INCLUDES under `-Ztrust-policy=certify`, whose `require_full_discharge` arm
/// fails on any non-empty failure. MEASURED end to end with the stage2 compiler on
/// the merged 3-arm program above, forcing the row's verdict with
/// `-Ztrust-verify-timeout-ms`:
///
/// ```text
/// strict  + row refuted      rc = 1  "1 failed, 0 unknown or timed out, 0 runtime-checked"
/// strict  + row not refuted  rc = 0  "0 failed, 0 unknown or timed out, 1 runtime-checked", 2 warnings
/// certify + row refuted      rc = 1
/// certify + row not refuted  rc = 1
/// ```
///
/// So `Failed -> Unknown` takes that build from RED to GREEN-with-warnings under
/// the default policy, and leaves it red under `certify` until the row is PROVED.
/// Compose that honestly: the four cells are the compiler's CLASSIFICATION,
/// measured at HEAD; the row verdicts are measured through
/// `Router::deterministic_in_process_ay`, and the compiler routes this obligation
/// to its native trust-mc lane. No patched compiler was built, so the end-to-end
/// red-to-green claim is an inference from two measurements, not one run.
///
/// The residual inside the rows that stay refuted is that BOUNDS/OVERFLOW rows are
/// deliberately EXCLUDED here, so they keep whatever verdict they already had.
/// Measured example: `match a { [] => 0, [.., y] => *y }` has its `Unreachable`
/// row proved and certified by this change while its last-element
/// `SliceBoundsCheck` read stays refuted — at `a__slice_len = 1`, a witness a real
/// execution can hold. That row is untouched by this lane in either direction
/// (`conjoin_slice_len_bounds` also skips it while `count_back_edges(func) == 0`).
///
/// SCOPE AND AUTHORITY, and the distinction a reader is most likely to get wrong:
/// this is NOT purely a VC-kind widening of an existing pass.
/// [`conjoin_slice_len_bounds`] admits exactly TWO families — a formula name ending
/// `__slice_len`, and a `coll_len_bound_vars` (`Vec`/`String`) local.
/// [`length_nonneg_base_names`] admits those two AND A THIRD: the DESTINATION of a
/// length read, an ordinary integer local rather than a length symbol.
/// `conjoin_slice_len_bounds` never admitted that family on ANY kind, so the third
/// family is NEW authority and carries its own derivation — see
/// [`length_nonneg_base_names`], which states it and its containment.
///
/// For the first two families the "not new" reading does hold: the fact is the one
/// `conjoin_slice_len_bounds` has attached for years, and only the VC-KIND
/// allowlist (`ArithmeticOverflow` and bounds — `range_kind` in
/// `generate::safety`) kept `Unreachable` / `Assertion` / panic-path rows from
/// seeing it. This is the complement for the kinds that pass does not reach.
///
/// THE FACT IS `0 <= len`, AND NOTHING ELSE. The companion `len <= isize::MAX` is
/// deliberately not attached here: it is FALSE for a zero-sized element (`&[()]`
/// may hold `usize::MAX` items) and it is TARGET-DEPENDENT (a pointer-width
/// constant), whereas `0 <= len` holds on every target because `usize` is
/// unsigned. `conjoin_slice_len_bounds` keeps emitting the non-ZST-gated upper
/// bound exactly where it did before.
///
/// NAME-DRIVEN, and that is load-bearing rather than stylistic: the bound is
/// attached only to names the `formula` ALREADY has, so this can never introduce
/// a free variable. `introduces_no_free_variable` (`length_nonneg_facts_tests`)
/// asserts exactly that, and fires when the pass is mutated to mint a bound for
/// every admitted base rather than for the names in hand. It matters because a
/// downstream lane gates on free variables: `composed_formula_is_caller_entry_grounded`
/// (see `callsite_replay_tests`) rejects a composed candidate carrying any free
/// var that is not entry-state or def-pinned, so publishing these facts
/// unconditionally — as a `build_global_invariant_facts` entry — would put an
/// unpinned name into composed candidates. Matching on the formula's own names
/// also picks up SSA-VERSIONED spellings (`_5__slice_len#s4_1`), which a fact
/// built from bare local names would miss.
///
/// SOUNDNESS — no blessed UB. `0 <= len` is a TRUE fact of every execution, so
/// conjoining it can only delete IMPOSSIBLE models, never a real witness. The
/// evidence for that is three REACHABLE traps whose rows are ON the changed path
/// — `if a.len() > b.len() { unreachable!() }` over `&[u32]`, over the ZST `&[()]`,
/// and over a `&Vec` receiver (whose length local is admitted by the
/// length-read-destination family, NOT by `coll_len_bound_vars` — that family
/// matches a bare `Ty::Adt` and ships with no coverage here). Each
/// is refuted with AND without this change, and each moves its witness off an
/// impossible negative length: MEASURED, the two slice traps go from
/// `a__slice_len = 0, b__slice_len = -1` at HEAD to `a__slice_len = 1,
/// b__slice_len = 0`, and the `Vec` trap from `v = 0, b__slice_len = -1` to
/// `v = 1, b__slice_len = 0`. The fact deletes only models no execution can reach.
/// `tests/slice_length_nonneg_real_mir.rs` asserts both halves, and each of the
/// three FAILS against pristine HEAD, which is what makes them evidence.
///
/// THE OTHER DIRECTION — an OFF-BY-ONE in the published bound. `0 <= len` is the
/// theorem; `1 <= len` is one character away and is FALSE for an empty container.
/// MEASURED with the bound minted that way: `fn f(a: &[u32], k: usize) -> usize
/// { k / a.len() }` has its `DivisionByZero` row proved and kernel-certified, and
/// so does the `Assertion` of `match a { [] => unreachable!(), .. }` — a real
/// division by zero and a real reachable panic, both laundered. Both are shipped
/// as fixtures (`slice_div_by_len_zero_mir.json`,
/// `slice_empty_match_trap_mir.json`) and both assertions fire under that mutant.
/// The blunter canaries in the same file — `a[i]` with unconstrained `i`,
/// `a[a.len()]`, `a.len() + k` overflow, and a reachable `_ => unreachable!()`
/// behind a slice match — pass identically with this change reverted (the first
/// three are EXCLUDED kinds; the fourth already had a `len = 2` witness at HEAD).
/// They guard the never-bless-UB direction and are labelled there as not being
/// evidence for the fix. Do not read them as coverage.
///
/// COVERAGE — what the falsification corpora do and do NOT show. Every fixture in
/// `tests/trust-falsification/{mutant,proved}` was dumped and re-run per row with
/// the same backend, at HEAD and with this change. Several of them carry no
/// `#![crate_type = "lib"]` inner attribute and dump nothing unless
/// `--crate-type lib` is passed on the command line — `countdown_div_by_one`, the
/// one fixture this lane touches at all, among them; a run that omits the flag
/// silently measures a smaller corpus. THE INVARIANT, which cannot drift with the
/// corpus the way a row total does (successive lanes measuring this have reported
/// different totals; every one of them reproduced the invariant):
///
///  * every row's VERDICT, kernel-certification and WITNESS are identical between
///    HEAD and this change;
///  * no mutant fixture loses its refutation;
///  * EXACTLY ONE formula in either corpus changes —
///    `countdown_div_by_one::div_by_one`'s second `DivisionByZero` row, which
///    gains `Ge(Var("offset#s3_0"), Int(0))` and stays `Proved`.
///
/// Read that correctly: almost no corpus row receives this bound at all, and NOT
/// ONE corpus fixture combines a container length with a non-bounds VC kind.
/// Corpus green therefore establishes NO COLLATERAL DAMAGE and nothing whatever
/// about whether the fix WORKS. The fixtures in
/// `tests/slice_length_nonneg_real_mir.rs` are the coverage.
///
/// RESIDUAL — the SCALE cliff, which is deterministic vcgen code and NOT the
/// solver. It is a MECHANISM, readable in `v2_build_path_guard_map`
/// (`generate::safety`): once a block has accumulated `MAX_PATHS_PER_BLOCK` (= 64)
/// distinct paths, the next one takes the `paths.clear(); paths.push(Vec::new())`
/// arm — the block's guard set is replaced by a single UNGUARDED path — and when
/// the global BFS budget is exhausted (`steps > cap`) the function returns
/// `vec![Vec::new()]` for EVERY block at once. A VC that has lost its path
/// condition asserts only "this block is reachable", which is SAT no matter what
/// facts are conjoined, so no length bound can help it. Supplying the missing
/// reachability condition is the collapse invariant's job, in
/// `generate::safety`: a content-free row on a degraded block is re-conditioned
/// on that block's in-edge disjunction, or DECLINED when no summary is
/// available. This pass neither causes nor cures the cliff, and nothing here
/// should be tuned around it.
///
/// AUTHORITY: every name admitted here is derived from the input PROGRAM — a
/// declared local type (`&[T]`/`&str`/`[T]`/`*const [T]`/`Vec<T>`/`String`), or
/// the declared UNSIGNED type of the destination of a length read (`Rvalue::Len`,
/// `UnOp::PtrMetadata`, a `len()`-family call). No serialized verdict bit is
/// consulted; an unrecognized shape yields no fact.
pub(super) fn conjoin_length_nonneg_bounds(func: &VerifiableFunction, formula: Formula) -> Formula {
    let bases = length_nonneg_base_names(func);
    if bases.is_empty() {
        return formula;
    }
    let mut names: FxHashSet<String> = FxHashSet::default();
    collect_formula_var_names(&formula, &mut names);
    let mut bounds: Vec<Formula> = Vec::new();
    let mut sorted: Vec<String> = names
        .into_iter()
        .filter(|name| bases.contains(name.split('#').next().unwrap_or(name.as_str())))
        .collect();
    // Deterministic emission order: the formula is a proof input.
    sorted.sort();
    for name in sorted {
        bounds.push(Formula::Ge(
            Box::new(Formula::var_owned(name, trust_types::Sort::Int)),
            Box::new(Formula::Int(0)),
        ));
    }
    if bounds.is_empty() {
        return formula;
    }
    bounds.push(formula);
    Formula::And(bounds)
}

/// Base var names of every LENGTH quantity `func` can name — the admission set
/// for [`conjoin_length_nonneg_bounds`]. Three families, each derived from a
/// declared type:
///
///  * `{place}__slice_len`, asked of [`crate::slice_len_formula`] itself rather
///    than re-derived, so the fact lands on the SAME symbol the obligations use.
///    A constant-length array / const-generic receiver returns an `Int` or a
///    const-param symbol instead of a length var and is skipped — it already
///    carries its exact bound.
///  * owned std containers abstracted to their length under the local's own var
///    name (`Vec`/`String`; the `coll_len_bound_vars` set, which is what
///    `conjoin_slice_len_bounds` keys on too). Its `non_zst` half gates the UPPER
///    bound only and is irrelevant to `0 <= len`.
///  * the DESTINATION of a length read — `_n = PtrMetadata(a)` (how `<[T]>::len()`
///    and every slice PATTERN test lower), `_n = Len(p)`, and a `len()`-family
///    call dest. This family is the one `conjoin_slice_len_bounds` never admitted
///    on any VC kind, so it needs its own derivation. THERE IS EXACTLY ONE, and it
///    is the destination's DECLARED UNSIGNED TYPE — checked here
///    (`ty.int_width().is_some() && !ty.is_signed()`), which is why a signed
///    destination is declined.
///
///    "The value IS a slice length" is NOT a second derivation and must not be
///    written as one: admission is by BASE name (everything before `#`), so the
///    bound attaches to EVERY SSA version of that local, including versions a
///    later reassignment wrote. The single falsification-corpus row this whole
///    lane changes is exactly that case — `countdown_div_by_one::div_by_one` has
///    `let mut offset = buf.len();` and then `offset -= 4` inside a loop, so the
///    bounded `offset#s3_0` denotes `buf.len() - 4k`, not a slice length. The
///    unsigned-type derivation still covers it; the length-provenance one does
///    not.
///
///    That derivation is not novel authority in itself: `0 <= x` for a
///    declared-unsigned non-parameter integer local is the LOWER half of the
///    range `conjoin_local_type_ranges_excluding` already publishes for every
///    entry of [`local_scalar_range_map`], attached by the same base-name match.
///    What is new is the KIND coverage — that pass runs only on the `range_kind`
///    VCs (`ArithmeticOverflow` and bounds), so `DivisionByZero`, `Unreachable`,
///    `Assertion` and the panic-path rows never saw it.
///
///    CONTAINMENT of the one documented false-accept for that invariant. The
///    circularity recorded on [`checked_arith_result_value_vars`] — conjoining
///    `0 <= X` for an `X` tied to `a - b` onto the SUBTRACTION'S OWN underflow
///    obligation, which then "proves" itself — cannot be reached from here,
///    because this conjoin is gated `!range_kind` at its only call site
///    (`generate::safety`, `generate_v2_safety_vcs_impl_with_origins`) and
///    `range_kind` includes every `VcKind::ArithmeticOverflow`. VERIFIED end to
///    end as well as by reading the gate: `fn f(a: &[u32], b: &[u32]) -> usize
///    { a.len() - b.len() }` keeps its `ArithmeticOverflow { op: Sub }` row
///    REFUTED, with a byte-identical formula, at HEAD and with this change.
pub(super) fn length_nonneg_base_names(func: &VerifiableFunction) -> FxHashSet<String> {
    let mut names: FxHashSet<String> = FxHashSet::default();
    for decl in &func.body.locals {
        if let Some(Formula::Var(name, _)) =
            crate::slice_len_formula(func, &Operand::Copy(Place::local(decl.index)))
            && name.ends_with("__slice_len")
        {
            names.insert(name);
        }
    }
    let (coll_all, _non_zst) = coll_len_bound_vars(func);
    names.extend(coll_all);
    let mut admit_dest = |dest: &Place| {
        if !dest.projections.is_empty() {
            return;
        }
        let Some(ty) = crate::place_ty_cow(func, dest) else { return };
        if ty.int_width().is_none() || ty.is_signed() {
            return;
        }
        names.insert(place_to_var_name(func, dest));
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue, .. } = stmt else { continue };
            let is_length_read = match rvalue {
                Rvalue::Len(src) => {
                    crate::slice_len_formula(func, &Operand::Copy(src.clone())).is_some()
                }
                Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, op) => matches!(
                    crate::ptr_metadata_model(func, op),
                    crate::PtrMetadataModel::Length(_)
                ),
                _ => false,
            };
            if is_length_read {
                admit_dest(dest);
            }
        }
        if let Terminator::Call { func: callee, dest, .. } = &block.terminator
            && matches!(method_tail(callee), "len" | "count" | "capacity")
        {
            admit_dest(dest);
        }
    }
    names
}

/// Conjoin slice/array length bounds for every `*__slice_len` term (produced by
/// `slice_len_formula`) the `formula` references. The lower bound `0 <= len` holds
/// for ANY element type. The upper bound `len <= isize::MAX` is sound ONLY for a
/// NON-ZERO-SIZED element: `size_of::<T>() * len <= isize::MAX` forces
/// `len <= isize::MAX` only when `size_of::<T>() >= 1`. For a ZST element (`&[()]`)
/// the length can reach `usize::MAX`, so an unconditional upper bound would
/// FALSE-PROVE `zst.len() + k` overflow. So the upper bound is gated on a provably
/// non-ZST element (via the function's slice-typed locals); ZST/unknown elements
/// keep only the lower bound (a false-FAIL at worst, never a false-PROVE). This
/// still discharges `while i < s.len() { i += 1 }` for the overwhelmingly common
/// non-ZST slices, with no soundness hole on the ZST edge.
pub(super) fn conjoin_slice_len_bounds(func: &VerifiableFunction, formula: Formula) -> Formula {
    let mut names: FxHashSet<String> = FxHashSet::default();
    collect_formula_var_names(&formula, &mut names);
    let (coll_all, coll_non_zst) = coll_len_bound_vars(func);
    // MATCH ON THE `#`-STRIPPED BASE, exactly as the owned-container arm below
    // already does. A derived `__slice_len` term is SSA-VERSIONED wherever its
    // base local is written (`_10__slice_len#s1_0`), and a versioned spelling
    // does not `ends_with("__slice_len")` — so a version-blind test silently
    // stops bounding the very term the goal mentions, and the solver is free to
    // pick a length no slice can have. `nonzst_slice_len_vars` keys on the base
    // name, so the non-ZST lookup must be normalized too. The bound is still
    // emitted over the FULL name, because that is the symbol in the goal.
    //
    // EVERY ELIGIBLE SYMBOL IS BOUNDED, INCLUDING ONE THE FORMULA ALREADY
    // BOUNDS THROUGH AN EQUALITY. `proved/r1_length_precond_array` is the
    // measured case: its goal carries `Eq(_N__slice_len#s..., arr__slice_len)`
    // and `arr__slice_len` is bounded here too, so the versioned symbol's own
    // `Ge(.., 0)` is implied. Emitting it anyway is deliberate. Skipping a fact
    // because some other conjunct implies it means the bound survives only as
    // long as that conjunct does, and the implication is nested under the path
    // guards — exactly the shape whose loss is invisible downstream, which is
    // the failure this whole function exists to prevent. The cost is real and
    // is a DECLINE, never a false proof: the extra conjunct is enough to move
    // that fixture off an exact proof and onto a weaker path, and its
    // obligation is then reported unproved (it keeps its runtime check).
    let base_of = |n: &str| n.split('#').next().unwrap_or(n).to_string();
    if !names
        .iter()
        .any(|n| base_of(n).ends_with("__slice_len") || coll_all.contains(&base_of(n)))
    {
        return formula;
    }
    let non_zst = nonzst_slice_len_vars(func);
    let mut bounds = Vec::new();
    for name in names {
        let base = base_of(&name);
        if base.ends_with("__slice_len") {
            let var = Formula::var(&name, trust_types::Sort::Int);
            bounds.push(Formula::Ge(Box::new(var.clone()), Box::new(Formula::Int(0))));
            if non_zst.contains(&base) {
                bounds.push(Formula::Le(Box::new(var), Box::new(Formula::Int(i64::MAX as i128))));
            }
            continue;
        }
        // Owned-container LENGTH abstraction (Vec/String live as an integer —
        // their length — under the local's own var name; see `coll_len_var`).
        // The same allocation-size type invariant as the slice-len case above
        // bounds it: `0 <= len` always; `len <= isize::MAX` only for a
        // crate-anchored std container whose ELEMENT is provably non-ZST
        // (`size_of::<T>() >= 1` forces `len <= isize::MAX`; a ZST container
        // can reach `usize::MAX`, so unknown/ZST elements keep only the lower
        // bound — fail-closed toward NOT bounding).
        if coll_all.contains(&base) {
            let var = Formula::var(&name, trust_types::Sort::Int);
            bounds.push(Formula::Ge(Box::new(var.clone()), Box::new(Formula::Int(0))));
            if coll_non_zst.contains(&base) {
                bounds.push(Formula::Le(Box::new(var), Box::new(Formula::Int(i64::MAX as i128))));
            }
        }
    }
    if bounds.is_empty() {
        return formula;
    }
    bounds.push(formula);
    Formula::And(bounds)
}

/// Var names of LOCALS whose type is a crate-anchored std owned container
/// (`std::vec::Vec`/`alloc::vec::Vec`/`String`) abstracted to its length —
/// `(all, non_zst_subset)`. The element type of a `Vec` is recovered
/// STRUCTURALLY as the pointee of the buffer pointer inside the flat `Ty::Adt`
/// tree (Vec -> RawVec -> Unique -> NonNull -> *const T); `String`'s element is
/// `u8`. Anything unrecognized is simply absent (fail-closed: no bound).
pub(super) fn coll_len_bound_vars(
    func: &VerifiableFunction,
) -> (FxHashSet<String>, FxHashSet<String>) {
    let mut all: FxHashSet<String> = FxHashSet::default();
    let mut non_zst: FxHashSet<String> = FxHashSet::default();
    for decl in &func.body.locals {
        let Ty::Adt { name, fields, .. } = &decl.ty else { continue };
        let base = name.split('<').next().unwrap_or(name);
        let is_vec = base == "std::vec::Vec" || base == "alloc::vec::Vec";
        let is_string = base == "std::string::String" || base == "alloc::string::String";
        if !is_vec && !is_string {
            continue;
        }
        let var = place_to_var_name(func, &Place::local(decl.index));
        all.insert(var.clone());
        let elem_non_zst = if is_string {
            true // element is u8
        } else {
            first_rawptr_pointee_in_fields(fields).map(ty_is_definitely_non_zst).unwrap_or(false)
        };
        if elem_non_zst {
            non_zst.insert(var);
        }
    }
    (all, non_zst)
}

/// First raw-pointer pointee reachable in a flat Adt field tree — for a std
/// `Vec<T>`'s lowered shape this is the buffer element type `T`. Depth-first
/// through nested Adt/Tuple fields; `None` when no pointer exists (fail-closed).
pub(super) fn first_rawptr_pointee_in_fields(fields: &[(String, Ty)]) -> Option<&Ty> {
    for (_, t) in fields {
        match t {
            Ty::RawPtr { pointee, .. } => return Some(pointee.as_ref()),
            Ty::Ref { inner, .. } => return Some(inner.as_ref()),
            Ty::Adt { fields, .. } => {
                if let Some(p) = first_rawptr_pointee_in_fields(fields) {
                    return Some(p);
                }
            }
            Ty::Tuple(tys) => {
                for t in tys {
                    if let Ty::RawPtr { pointee, .. } = t {
                        return Some(pointee.as_ref());
                    }
                }
            }
            _ => {}
        }
    }
    None
}

/// `{place}__slice_len` var names whose slice element is provably non-ZST, from
/// the function's slice-typed locals (params, temps, and loop-yielded sub-slices
/// are all locals). Only these may take the `len <= isize::MAX` upper bound.
pub(super) fn nonzst_slice_len_vars(func: &VerifiableFunction) -> FxHashSet<String> {
    let mut set: FxHashSet<String> = FxHashSet::default();
    for decl in &func.body.locals {
        let elem = match &decl.ty {
            Ty::Ref { inner, .. } => match inner.as_ref() {
                Ty::Slice { elem } => Some(elem.as_ref()),
                _ => None,
            },
            Ty::Slice { elem } => Some(elem.as_ref()),
            _ => None,
        };
        if let Some(elem) = elem
            && ty_is_definitely_non_zst(elem)
        {
            set.insert(format!(
                "{}__slice_len",
                place_to_var_name(func, &Place::local(decl.index))
            ));
        }
    }
    set
}

/// Conservative: true only for element types provably >= 1 byte. Recurses through
/// Array/Tuple/Adt so `&[SomeStruct]` (any non-ZST field) is covered; returns
/// false for `()`, empty/all-ZST tuples/structs, `[T; 0]`, and anything unknown —
/// fail-closed toward NOT bounding, which is the sound direction.
pub(super) fn ty_is_definitely_non_zst(ty: &Ty) -> bool {
    match ty {
        Ty::Bool
        | Ty::Char
        | Ty::Int { .. }
        | Ty::PtrSizedInt { .. }
        | Ty::Float { .. }
        | Ty::Ref { .. }
        | Ty::RawPtr { .. }
        | Ty::FnPtr { .. } => true,
        Ty::Bv(w) => *w > 0,
        Ty::Array { elem, len } => *len > 0 && ty_is_definitely_non_zst(elem),
        Ty::Tuple(tys) => tys.iter().any(ty_is_definitely_non_zst),
        Ty::Adt { fields, .. } => fields.iter().any(|(_, t)| ty_is_definitely_non_zst(t)),
        _ => false,
    }
}

/// True `(width, signed)` of an integer binary operation, recovering from the
/// signed-constant width loss: a `ConstValue::Int` operand carries no width, so
/// `operand_ty` fabricates `i64`. Deriving the overflow bound from such a constant
/// (`100i8 + x`, `(-128i8) / y`) would check at the i64 boundary and MISS a real
/// narrow-width overflow (a false-PROVE). Arithmetic operands share the result
/// type, so prefer the type of a NON-CONSTANT operand (which carries the true
/// width). Picking the narrower true width only TIGHTENS the overflow bound (more
/// violations caught) — fail-closed/sound. The complete fix is to give
/// `ConstValue::Int` a width field at extraction (build-gated, convert.rs); this
/// is the buildable belt-and-suspenders. Trust #soundness (round-19).
pub(crate) fn int_op_type(
    func: &VerifiableFunction,
    lhs: &Operand,
    rhs: &Operand,
) -> Option<(u32, bool)> {
    let ty = if !matches!(lhs, Operand::Constant(_)) {
        crate::operand_ty_cow(func, lhs)
    } else if !matches!(rhs, Operand::Constant(_)) {
        crate::operand_ty_cow(func, rhs)
    } else {
        // Both operands constant (rustc rejects narrow-type const-arithmetic
        // overflow at compile time, so this is rare): take the narrower width.
        match (crate::operand_ty_cow(func, lhs), crate::operand_ty_cow(func, rhs)) {
            (Some(a), Some(b)) => {
                let wa = a.int_width().unwrap_or(u32::MAX);
                let wb = b.int_width().unwrap_or(u32::MAX);
                Some(if wa <= wb { a } else { b })
            }
            (a, b) => a.or(b),
        }
    }?;
    Some((ty.int_width()?, ty.is_signed()))
}
