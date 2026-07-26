// Range hypotheses implied by a local's declared type: integer width bounds,
// datatype field bounds reached through projections, and slice-length bounds
// for non-zero-sized element types. These are the always-true facts every VC
// in the function may assume.

use super::*;

/// Conjoin the declared-type integer range onto every fixed-width-integer LOCAL/temp
/// the `formula` references — the sibling of `conjoin_arg_type_ranges` for the
/// NON-parameter locals (return slot + temporaries). VC-gen lowers an `i8`/`u32`/…
/// local to the unbounded `Sort::Int`, dropping the invariant that the value is
/// within its type range; an overflow/cast/index VC over such a local can then be
/// FALSE-REFUTED by the solver picking an out-of-type-range value (e.g. a `u32`
/// local set to `i128::MAX`). Re-attaching the true range fact `in_range(local)`
/// discharges those spurious refutations.
///
/// SOUNDNESS: DROP-ONLY in the FALSE-PROVE direction — `in_range(local)` is a TRUE
/// fact about a fixed-width integer local (its value always lies within its declared
/// type range), so conjoining it can only PROVE a genuinely-safe obligation, never
/// hide a real violation (a value genuinely able to overflow is still in range, and
/// the overflow VC over it stays refutable). It is GENERAL — fixed-width integers,
/// no datatype modeling. Parameters are skipped (already bounded by
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
                crate::unique_whole_local_def(func, decl.index)
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
    let ranges = local_int_range_map(func);
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
        if let Some(&(width, signed)) = ranges.get(base) {
            bounds.push(crate::range::input_range_constraint(
                &Formula::Var(name.clone(), trust_types::Sort::Int),
                width,
                signed,
            ));
        }
    }
    if bounds.is_empty() {
        return formula;
    }
    bounds.push(formula);
    Formula::And(bounds)
}

/// Build `base_local_var_name -> (width, signed)` for every fixed-width-integer
/// LOCAL/temp that `conjoin_local_type_ranges` may soundly range-bound. Keyed by
/// `place_to_var_name(func, Place::local(i))` so the key is the EXACT base var name
/// the formula uses for that bare local. PARAMETERS are skipped (already bounded by
/// `conjoin_arg_type_ranges`). Local 0 (the return slot) IS included: it is a
/// fixed-width-integer local like any other when the return type is integer, and its
/// bound is a true fact about the returned value.
pub(super) fn local_int_range_map(func: &VerifiableFunction) -> FxHashMap<String, (u32, bool)> {
    let mut map: FxHashMap<String, (u32, bool)> = FxHashMap::default();
    for decl in &func.body.locals {
        // Skip parameters: `conjoin_arg_type_ranges` already bounds 1..=arg_count.
        if decl.index >= 1 && decl.index <= func.body.arg_count {
            continue;
        }
        let Some(width) = decl.ty.int_width() else {
            continue;
        };
        let name = place_to_var_name(func, &Place::local(decl.index));
        map.insert(name, (width, decl.ty.is_signed()));
    }
    map
}

/// Conjoin fixed-width type-range bounds for every fixed-width-integer datatype
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
/// to the field's ACTUAL declared width/signedness; keyed by the EXACT
/// `place_to_var_name` of a FIELD-projecting place so it attaches only to a name the
/// formula references; conjoining an in-range fact onto an already-in-range value is
/// a harmless `true`.
pub(super) fn conjoin_datatype_field_ranges(func: &VerifiableFunction, formula: Formula) -> Formula {
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
        if let Some(&(width, signed)) = ranges.get(name) {
            bounds.push(crate::range::input_range_constraint(
                &Formula::Var(name.clone(), trust_types::Sort::Int),
                width,
                signed,
            ));
        }
    }
    if bounds.is_empty() {
        return formula;
    }
    bounds.push(formula);
    Formula::And(bounds)
}

/// Build `var_name -> (width, signed)` for every `Copy`/`Move`/place-valued
/// position in the body that projects through a FIELD and resolves to a fixed-width
/// integer type — the fields `conjoin_datatype_field_ranges` may soundly range-bound.
/// Keyed by `place_to_var_name` so the names match the formula's free vars EXACTLY.
///
/// Restricted to field-PROJECTING places: a bare integer local is already bounded by
/// `conjoin_local_type_ranges` / `conjoin_arg_type_ranges`, and bounding only fields
/// keeps this orthogonal. Built from every place the body mentions (a total walk that
/// fails closed on any operand position it does not recognize — a missed field merely
/// gets no bound, conservative, never a false prove).
pub(super) fn datatype_field_range_map(func: &VerifiableFunction) -> FxHashMap<String, (u32, bool)> {
    let mut map: FxHashMap<String, (u32, bool)> = FxHashMap::default();
    let mut record = |place: &Place| {
        // Only FIELD-projecting places (a bare local is bounded elsewhere).
        if !place.projections.iter().any(|p| matches!(p, trust_types::Projection::Field(_))) {
            return;
        }
        // The field must resolve to a fixed-width integer type — that is the only
        // case where the sort lowering collapses it to the unbounded `Sort::Int` and
        // the range invariant is lost.
        let Some((width, signed)) = resolve_field_int_ty(func, place) else {
            return;
        };
        map.insert(place_to_var_name(func, place), (width, signed));
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            for_each_stmt_copy_move_place(stmt, &mut record);
        }
        for_each_terminator_copy_move_place(&block.terminator, &mut record);
    }
    map
}

/// Resolve a field-projecting place to `(width, signed)` IFF it lands on a
/// fixed-width integer field. Datatype-AWARE: the core `place_ty`/`project_ty`
/// field arms resolve `Ty::Tuple`/`Ty::Adt`/`Ty::Closure` fields but NOT
/// `Ty::Datatype` fields (the Lever A modeled `Expr`/`Level`/`Name` cluster), so
/// a field read off a modeled datatype value otherwise resolves to `None` and the
/// `u32` field is left unbounded — exactly the gap. This walks the projections
/// itself, descending `Ty::Datatype` field-by-field (an enum field via
/// `Downcast(v).Field(i)`, a struct-like datatype field via a bare `Field(i)` on
/// variant 0), and defers to `project_ty` for every non-datatype step. Returns
/// `None` (no bound — conservative) for anything it cannot type as a fixed-width
/// integer. SOUNDNESS: read-only type resolution; it never changes a VC, only
/// decides whether a sound range fact is attachable to the field's var.
pub(super) fn resolve_field_int_ty(func: &VerifiableFunction, place: &Place) -> Option<(u32, bool)> {
    // verifier-perf: walk the declared type by REFERENCE (no fat-root clone), cloning
    // only the small resolved field — this only reads `int_width`/`is_signed` at the end.
    use std::borrow::Cow;
    let mut ty: Cow<'_, Ty> = Cow::Borrowed(crate::local_ty_ref(func, place.local)?);
    let mut pending_variant: Option<usize> = None;
    for proj in &place.projections {
        match proj {
            trust_types::Projection::Downcast(v) => {
                pending_variant = Some(*v);
            }
            trust_types::Projection::Field(idx) => {
                if let Ty::Datatype { variants, .. } = ty.as_ref() {
                    // A `Field` after a `Downcast(v)` selects variant v's i-th
                    // field; a bare `Field` on a single-variant (struct-like)
                    // datatype selects variant 0's i-th field. A multi-variant
                    // datatype with no preceding downcast is ambiguous — fail
                    // closed (no bound).
                    let v = match pending_variant.take() {
                        Some(v) => v,
                        None if variants.len() == 1 => 0,
                        None => return None,
                    };
                    let field_ty = variants.get(v)?.1.get(*idx)?.1.clone();
                    ty = Cow::Owned(field_ty);
                } else {
                    pending_variant = None;
                    ty = crate::step_place_ty_cow(ty, proj)?;
                }
            }
            _ => {
                pending_variant = None;
                ty = crate::step_place_ty_cow(ty, proj)?;
            }
        }
    }
    Some((ty.int_width()?, ty.is_signed()))
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
    if !names
        .iter()
        .any(|n| n.ends_with("__slice_len") || coll_all.contains(n.split('#').next().unwrap_or(n)))
    {
        return formula;
    }
    let non_zst = nonzst_slice_len_vars(func);
    let mut bounds = Vec::new();
    for name in names {
        if name.ends_with("__slice_len") {
            let var = Formula::var(&name, trust_types::Sort::Int);
            bounds.push(Formula::Ge(Box::new(var.clone()), Box::new(Formula::Int(0))));
            if non_zst.contains(&name) {
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
        let base = name.split('#').next().unwrap_or(&name);
        if coll_all.contains(base) {
            let var = Formula::var(&name, trust_types::Sort::Int);
            bounds.push(Formula::Ge(Box::new(var.clone()), Box::new(Formula::Int(0))));
            if coll_non_zst.contains(base) {
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
pub(super) fn coll_len_bound_vars(func: &VerifiableFunction) -> (FxHashSet<String>, FxHashSet<String>) {
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
        | Ty::Int { .. }
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
