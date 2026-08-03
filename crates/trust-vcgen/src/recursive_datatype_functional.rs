// trust-vcgen/recursive_datatype_functional.rs: WALL C — the RECURSIVE-
// datatype-function INDUCTION VC lane.
//
// This is the recursion-specific sibling of the non-recursive
// `datatype_functional` equation lane. It is the RECURSION PRIMITIVE on the emission side: for a
// SELF-recursive function over a modeled `Ty::Datatype` (a call_graph SCC of
// size 1 with a self edge — e.g. the extracted fixture
// `mirror : &Level -> Level`, zero -> zero, succ p -> succ (mirror p)), it
// emits the STRUCTURAL-INDUCTION obligations for the function's declared
// postcondition `P(params, _0)`:
//
//   * one INDUCTION-CASE VC per constructor arm, in constructor (variant-tag)
//     order, with the arm's recursive-call results replaced by fresh
//     inductive-hypothesis variables:
//       `Forall [ctor fields, IH results]
//          (Implies (And IH-atoms) P(pattern, arm-result))`
//     where each IH atom is `P(call-args, __ih_k)` (the postcondition assumed
//     at the recursive call), `pattern` is `Ctor(C, fields)`, and base arms
//     (no recursive call) carry no IH;
//   * one CONCLUSION VC `Forall [params] P(params, _0)` (the return slot `_0`
//     is deliberately free — it denotes the function's output, exactly as in
//     the non-recursive lane), tagged `[induction:<datatype>;cases=<n>]` so a
//     consumer knows it is discharged BY INDUCTION FROM THE CASES, never on
//     its own.
//
// For the fixture `mirror` with postcondition `Eq(_0, l)` this emits
//   case Zero: `Eq(Ctor Zero, Ctor Zero)`
//   case Succ: `Forall [__fld_Succ_0, __ih0]
//                 (Implies (Eq(__ih0, __fld_Succ_0))
//                          (Eq(Ctor(Succ,[__ih0]), Ctor(Succ,[__fld_Succ_0]))))`
//   conclusion: `Forall [l] Eq(_0, l)`   [induction:level::Level;cases=2]
// which is the exact `Level.rec` minor-premise/major-conclusion split that
// trust-certify's `recursive_datatype_functional` lane reconstructs as a
// kernel-checked CIC induction term.
//
// SCOPE (the recursion PRIMITIVE, honestly bounded):
//   * SELF-recursion only (SCC of size 1). Mutual induction over an SCC of
//     size N > 1 (the `infer_type <-> whnf <-> is_def_eq` cluster shape) is
//     the sibling `mutual_recursive_datatype_functional` lane.
//   * one constructor-match layer over one scrutinee parameter; every
//     `Return`-reaching arm must be under exactly one constructor of the
//     scrutinee's datatype, the arms must cover ALL constructors, and every
//     `Call` must be a self-call. Anything else fails CLOSED (emits nothing) —
//     a partial induction bundle is not a proof plan.
//
// SOUNDNESS: this module only PRODUCES proof obligations (VCs); it discharges
// none. The conclusion VC's `[induction:..]` tag binds it to its cases so no
// consumer can treat the bare `Forall params P` as independently discharged.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::HashMap;

use trust_types::{
    AggregateKind, BlockId, ConstValue, Formula, Operand, Place, Projection, Rvalue, Sort,
    Statement, Terminator, Ty, VcKind, VerifiableFunction, VerificationCondition,
};

use crate::call_graph::{build_call_graph, is_self_recursive};

/// Property tag prefix of an induction-CASE VC (`..._case::<Ctor>`).
pub const CASE_PROPERTY_PREFIX: &str = "recursive_datatype_functional_case::";
/// Property tag prefix of the induction CONCLUSION VC (suffixed with the
/// `[induction:<datatype>;cases=<n>]` bundle marker).
pub const CONCLUSION_PROPERTY_PREFIX: &str = "recursive_datatype_functional_conclusion";

/// Per-arm symbolic walk state. `pub(crate)` so the mutual-SCC lane
/// (`mutual_recursive_datatype_functional`) extends this machinery instead of
/// forking it.
#[derive(Clone, Default)]
pub(crate) struct WalkState {
    /// MIR local index -> the datatype/scalar `Formula` term it holds.
    pub(crate) store: HashMap<usize, Formula>,
    /// MIR local index -> the place whose `Discriminant` was read into it.
    pub(crate) disc_of: HashMap<usize, Place>,
    /// The constructor arm this path is under: `(variant_tag, ctor_name)`.
    /// `None` before the match fork; at most ONE fork is modeled (the mutual
    /// lane layers its own fuel fork OUTSIDE this state).
    pub(crate) ctor: Option<(usize, String)>,
    /// Fresh binders introduced along this arm: the pattern's field variables
    /// followed by the recursive-call IH result variables, in order.
    pub(crate) binders: Vec<(String, Sort)>,
    /// One inductive-hypothesis atom per recursive call:
    /// `P(call-args, __ih_k)`.
    pub(crate) ih_atoms: Vec<Formula>,
}

/// One completed constructor arm.
struct CaseArm {
    tag: usize,
    ctor: String,
    formula: Formula,
}

/// Emit the recursive-datatype induction VC bundle for `func`: the per-
/// constructor case VCs (variant order) followed by the tagged conclusion VC.
/// Empty (fail-closed) unless `func` is SELF-recursive, involves a modeled
/// `Ty::Datatype`, carries a declared postcondition, and every `Return` arm
/// fits the one-match/self-calls-only shape covering all constructors.
#[must_use]
pub fn recursive_datatype_functional_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    if func.postconditions.is_empty() || !involves_modeled_datatype(func) {
        return Vec::new();
    }
    let graph = build_call_graph(std::slice::from_ref(func));
    if !is_self_recursive(&graph, &func.def_path) {
        return Vec::new();
    }
    let Some(entry) = func.body.blocks.first() else {
        return Vec::new();
    };
    let post = conjoin_all(func.postconditions.clone());

    let mut arms: Vec<CaseArm> = Vec::new();
    let mut ih_counter = 0usize;
    let ok = walk(func, &post, entry.id, WalkState::default(), 0, &mut ih_counter, &mut arms);
    if !ok {
        return Vec::new();
    }

    // The scrutinee datatype: every arm's ctor came from the same fork; recover
    // it from the (single) matched datatype. All constructors must be covered,
    // exactly once each.
    let Some(dt) = scrutinee_datatype(func) else {
        return Vec::new();
    };
    let Ty::Datatype { name: dt_name, variants } = &dt else {
        return Vec::new();
    };
    let mut tags: Vec<usize> = arms.iter().map(|a| a.tag).collect();
    tags.sort_unstable();
    tags.dedup();
    if tags.len() != arms.len() || tags != (0..variants.len()).collect::<Vec<_>>() {
        return Vec::new();
    }
    arms.sort_by_key(|a| a.tag);

    let mut vcs: Vec<VerificationCondition> = arms
        .iter()
        .map(|arm| VerificationCondition {
            kind: VcKind::FunctionalCorrectness {
                property: format!("{CASE_PROPERTY_PREFIX}{}", arm.ctor),
                context: func.name.clone(),
            },
            function: func.name.as_str().into(),
            location: func.span.clone(),
            formula: arm.formula.clone(),
            contract_metadata: None,
            obligation: None,
        })
        .collect();

    // The conclusion `Forall [params] P` — `_0` stays free (the output), and the
    // property tag binds it to the case bundle above.
    let binders = param_binders(func);
    let refs: Vec<(&str, Sort)> = binders.iter().map(|(n, s)| (n.as_str(), s.clone())).collect();
    let conclusion = if refs.is_empty() { post.clone() } else { Formula::forall(&refs, post) };
    vcs.push(VerificationCondition {
        kind: VcKind::FunctionalCorrectness {
            property: format!(
                "{CONCLUSION_PROPERTY_PREFIX}[induction:{dt_name};cases={}]",
                arms.len()
            ),
            context: func.name.clone(),
        },
        function: func.name.as_str().into(),
        location: func.span.clone(),
        formula: conclusion,
        contract_metadata: None,
        obligation: None,
    });
    // Only this point establishes that the function is in this lane's COMPLETE
    // one-match/self-recursive shape.  Outside that shape the documented result
    // is empty, even when an unrelated postcondition happens to use arithmetic.
    if let Some(gap) = crate::contracts::functional_lane_unmodeled_postcondition_vc(
        func,
        "recursive-datatype functional induction",
    ) {
        return vec![gap];
    }
    vcs
}

/// Whether the return type or any parameter is (a reference/pointer to) a
/// modeled `Ty::Datatype`.
pub(crate) fn involves_modeled_datatype(func: &VerifiableFunction) -> bool {
    if peel_indirection(&func.body.return_ty).is_datatype() {
        return true;
    }
    (1..=func.body.arg_count)
        .filter_map(|i| local_ty(func, i))
        .any(|ty| peel_indirection(ty).is_datatype())
}

/// The datatype the function's match scrutinee carries: the first parameter
/// whose (indirection-peeled) type is a FULL datatype (non-empty variants).
fn scrutinee_datatype(func: &VerifiableFunction) -> Option<Ty> {
    (1..=func.body.arg_count).filter_map(|i| local_ty(func, i)).find_map(
        |ty| match peel_indirection(ty) {
            dt @ Ty::Datatype { variants, .. } if !variants.is_empty() => Some(dt.clone()),
            _ => None,
        },
    )
}

/// Peel reference / raw-pointer indirection (the modeled datatype erases the
/// `Arc`/pointer wrappers of recursive children — trust-mir-extract steps 2/5).
pub(crate) fn peel_indirection(ty: &Ty) -> &Ty {
    match ty {
        Ty::Ref { inner, .. } => peel_indirection(inner),
        Ty::RawPtr { pointee, .. } => peel_indirection(pointee),
        _ => ty,
    }
}

/// Universally-bound parameter binders for the conclusion VC. Parameter sorts
/// are the peeled datatype sorts (the model erases the `&`/`*const`).
pub(crate) fn param_binders(func: &VerifiableFunction) -> Vec<(String, Sort)> {
    (1..=func.body.arg_count)
        .filter_map(|i| {
            let ty = local_ty(func, i)?;
            Some((
                crate::place_to_var_name(func, &Place::local(i)),
                crate::sort_for_ty(peel_indirection(ty)),
            ))
        })
        .collect()
}

/// Bounded CFG walk. Returns `false` (fail-closed for the WHOLE bundle) on any
/// unmodeled construct along a `Return`-reaching path.
#[allow(clippy::too_many_lines)]
fn walk(
    func: &VerifiableFunction,
    post: &Formula,
    block_id: BlockId,
    mut state: WalkState,
    depth: usize,
    ih_counter: &mut usize,
    arms: &mut Vec<CaseArm>,
) -> bool {
    if depth > 64 {
        return false;
    }
    let Some(block) = func.body.blocks.iter().find(|b| b.id == block_id) else {
        return false;
    };

    for stmt in &block.stmts {
        apply_stmt(func, &mut state, stmt);
    }

    match &block.terminator {
        Terminator::Return => {
            // A Return outside any constructor arm cannot be a per-constructor
            // induction case.
            let Some((tag, ctor)) = state.ctor.clone() else {
                return false;
            };
            let Some(result) = resolve_place(func, &state, &Place::local(0)) else {
                return false;
            };
            let conclusion = subst_post(func, post, &state, result);
            let body = if state.ih_atoms.is_empty() {
                conclusion
            } else {
                Formula::Implies(
                    Box::new(conjoin_all(state.ih_atoms.clone())),
                    Box::new(conclusion),
                )
            };
            let formula = if state.binders.is_empty() {
                body
            } else {
                let refs: Vec<(&str, Sort)> =
                    state.binders.iter().map(|(n, s)| (n.as_str(), s.clone())).collect();
                Formula::forall(&refs, body)
            };
            arms.push(CaseArm { tag, ctor, formula });
            true
        }
        Terminator::Goto(target) => walk(func, post, *target, state, depth + 1, ih_counter, arms),
        Terminator::Assert { target, .. } | Terminator::Drop { target, .. } => {
            walk(func, post, *target, state, depth + 1, ih_counter, arms)
        }
        // A dead arm (rustc's exhaustive-match `otherwise -> Unreachable`)
        // contributes no case and does not poison the bundle.
        Terminator::Unreachable => true,
        Terminator::SwitchInt { discr, targets, .. } => {
            // Only ONE constructor-match layer is modeled.
            if state.ctor.is_some() {
                return false;
            }
            let Some(matched) = discriminant_place(&state, discr) else {
                return false;
            };
            let Some(matched_ty) = local_ty(func, matched.local) else {
                return false;
            };
            let dt = peel_indirection(matched_ty).clone();
            let Ty::Datatype { variants, .. } = &dt else {
                return false;
            };
            if variants.is_empty() {
                return false;
            }
            // The scrutinee must be (a projection-free indirection of) a
            // parameter — the induction variable.
            if matched.local == 0
                || matched.local > func.body.arg_count
                || !matched.projections.iter().all(|p| matches!(p, Projection::Deref))
            {
                return false;
            }
            let dt_sort = crate::sort_for_ty(&dt);
            for (tag, target) in targets {
                let tag = *tag as usize;
                let Some((ctor, fields)) = variants.get(tag).cloned() else {
                    return false;
                };
                // Fresh pattern-field variables; rebind the scrutinee local to
                // the explicit pattern `Ctor(C, fields)` so payload reads
                // (`Downcast`+`Field`) resolve to the field variables and the
                // substituted postcondition sees the pattern.
                let mut arm_state = state.clone();
                let mut field_vars = Vec::with_capacity(fields.len());
                for (i, (_, fty)) in fields.iter().enumerate() {
                    let name = format!("__fld_{ctor}_{i}");
                    let sort = crate::sort_for_ty(peel_indirection(fty));
                    arm_state.binders.push((name.clone(), sort.clone()));
                    field_vars.push(Formula::var_owned(name, sort));
                }
                arm_state.store.insert(
                    matched.local,
                    Formula::Ctor { ctor: ctor.clone(), args: field_vars, sort: dt_sort.clone() },
                );
                arm_state.ctor = Some((tag, ctor));
                if !walk(func, post, *target, arm_state, depth + 1, ih_counter, arms) {
                    return false;
                }
            }
            true
        }
        Terminator::Call { func: callee, args, dest, target, .. } => {
            // Only SELF-calls are modeled (the recursive occurrence); any other
            // call poisons the bundle (fail-closed).
            if callee != &func.name && callee != &func.def_path {
                return false;
            }
            let Some(target) = target else {
                return false;
            };
            if args.len() != func.body.arg_count || !dest.projections.is_empty() {
                return false;
            }
            let mut arg_terms = Vec::with_capacity(args.len());
            for arg in args {
                let Some(term) = resolve_operand(func, &state, arg) else {
                    return false;
                };
                arg_terms.push(term);
            }
            // Fresh IH result variable standing for the recursive call's output.
            let ih_name = format!("__ih{ih_counter}");
            *ih_counter += 1;
            let ret_sort = crate::sort_for_ty(peel_indirection(&func.body.return_ty));
            let ih_var = Formula::var_owned(ih_name.clone(), ret_sort.clone());
            state.binders.push((ih_name, ret_sort));
            state.store.insert(dest.local, ih_var.clone());
            // IH atom: the postcondition assumed at the recursive call —
            // `P(call-args, __ih_k)`.
            let mut map: HashMap<String, Formula> = HashMap::new();
            for (i, term) in arg_terms.into_iter().enumerate() {
                map.insert(crate::place_to_var_name(func, &Place::local(i + 1)), term);
            }
            map.insert("_0".to_string(), ih_var);
            state.ih_atoms.push(subst_vars(post.clone(), &map));
            walk(func, post, *target, state, depth + 1, ih_counter, arms)
        }
        _ => false,
    }
}

/// The arm's conclusion: `P` with each parameter replaced by its current arm
/// term (the scrutinee by its pattern) and `_0` by the arm's result term.
pub(crate) fn subst_post(
    func: &VerifiableFunction,
    post: &Formula,
    state: &WalkState,
    result: Formula,
) -> Formula {
    let mut map: HashMap<String, Formula> = HashMap::new();
    for i in 1..=func.body.arg_count {
        if let Some(term) = state.store.get(&i) {
            map.insert(crate::place_to_var_name(func, &Place::local(i)), term.clone());
        }
    }
    map.insert("_0".to_string(), result);
    subst_vars(post.clone(), &map)
}

/// Capture-free variable substitution for the (quantifier-free) postcondition.
pub(crate) fn subst_vars(f: Formula, map: &HashMap<String, Formula>) -> Formula {
    if let Some(name) = f.var_name() {
        if let Some(t) = map.get(name) {
            return t.clone();
        }
        return f;
    }
    f.map_children(&mut |child| subst_vars(child, map))
}

pub(crate) fn conjoin_all(mut parts: Vec<Formula>) -> Formula {
    if parts.len() == 1 { parts.remove(0) } else { Formula::And(parts) }
}

/// Fold one statement into the arm's symbolic state. `AddressOf` is
/// transparent for the extracted `&m as *const _` coercion.
pub(crate) fn apply_stmt(func: &VerifiableFunction, state: &mut WalkState, stmt: &Statement) {
    let Statement::Assign { place, rvalue, .. } = stmt else {
        return;
    };
    if !place.projections.is_empty() {
        return;
    }
    match rvalue {
        Rvalue::Discriminant(p) => {
            state.disc_of.insert(place.local, p.clone());
        }
        Rvalue::Use(op) | Rvalue::Cast(op, _) => {
            if let Some(term) = resolve_operand(func, state, op) {
                state.store.insert(place.local, term);
            }
        }
        Rvalue::Ref { place: referent, .. }
        | Rvalue::CopyForDeref(referent)
        | Rvalue::AddressOf(_, referent) => {
            if let Some(term) = resolve_place(func, state, referent) {
                state.store.insert(place.local, term);
            }
        }
        Rvalue::Aggregate(AggregateKind::Adt { variant, .. }, ops) => {
            if let Some(term) = aggregate_to_ctor(func, state, place.local, *variant, ops) {
                state.store.insert(place.local, term);
            }
        }
        _ => {}
    }
}

/// Build the `Formula::Ctor` for an ADT-aggregate assigned to `dest_local`
/// (structural: the ctor name is the destination's own datatype variant name).
fn aggregate_to_ctor(
    func: &VerifiableFunction,
    state: &WalkState,
    dest_local: usize,
    variant: usize,
    ops: &[Operand],
) -> Option<Formula> {
    let dest_ty = peel_indirection(local_ty(func, dest_local)?);
    let Ty::Datatype { variants, .. } = dest_ty else {
        return None;
    };
    let (ctor, _fields) = variants.get(variant)?;
    let mut args = Vec::with_capacity(ops.len());
    for op in ops {
        // Every field operand must resolve — an opaque field would make the
        // induction-case conclusion unprovable-by-construction; fail closed.
        args.push(resolve_operand(func, state, op)?);
    }
    Some(Formula::Ctor { ctor: ctor.clone(), args, sort: crate::sort_for_ty(dest_ty) })
}

pub(crate) fn resolve_operand(
    func: &VerifiableFunction,
    state: &WalkState,
    op: &Operand,
) -> Option<Formula> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => resolve_place(func, state, p),
        Operand::Constant(cv) => const_to_formula(cv),
        Operand::Symbolic(f) => Some(f.clone()),
        _ => None,
    }
}

/// Resolve a place to its term. Adds one rule over the non-recursive lane's
/// resolver: a `Downcast(v)+Field(i)` over a term that is ALREADY the pattern
/// `Ctor(C_v, fields)` (the arm rebinding) reduces directly to `fields[i]`.
pub(crate) fn resolve_place(
    func: &VerifiableFunction,
    state: &WalkState,
    place: &Place,
) -> Option<Formula> {
    if place.projections.is_empty() {
        if let Some(term) = state.store.get(&place.local) {
            return Some(term.clone());
        }
        return param_var(func, place.local);
    }
    let mut term =
        state.store.get(&place.local).cloned().or_else(|| param_var(func, place.local))?;
    let mut base_ty = peel_indirection(local_ty(func, place.local)?).clone();
    let mut pending_variant: Option<usize> = None;

    for proj in &place.projections {
        match proj {
            Projection::Deref => {}
            Projection::Downcast(v) => pending_variant = Some(*v),
            Projection::Field(idx) => {
                let Ty::Datatype { name, variants } = &base_ty else {
                    return None;
                };
                let v = match pending_variant.take() {
                    Some(v) => v,
                    None if variants.len() == 1 => 0,
                    None => return None,
                };
                let (vctor, fields) = variants.get(v)?;
                let (fname, fty) = fields.get(*idx)?;
                // Pattern reduction: selecting off the arm's own pattern term.
                if let Formula::Ctor { ctor, args, .. } = &term {
                    if ctor != vctor {
                        return None;
                    }
                    term = args.get(*idx)?.clone();
                } else {
                    term = Formula::Sel {
                        datatype: name.clone(),
                        field: fname.clone(),
                        field_sort: crate::sort_for_ty(peel_indirection(fty)),
                        arg: Box::new(term),
                    };
                }
                base_ty = peel_indirection(fty).clone();
            }
            _ => return None,
        }
    }
    Some(term)
}

pub(crate) fn param_var(func: &VerifiableFunction, local: usize) -> Option<Formula> {
    if local == 0 || local > func.body.arg_count {
        return None;
    }
    let ty = local_ty(func, local)?;
    Some(Formula::var_owned(
        crate::place_to_var_name(func, &Place::local(local)),
        crate::sort_for_ty(peel_indirection(ty)),
    ))
}

pub(crate) fn discriminant_place(state: &WalkState, discr: &Operand) -> Option<Place> {
    let local = match discr {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p.local,
        _ => return None,
    };
    state.disc_of.get(&local).cloned()
}

pub(crate) fn const_to_formula(cv: &ConstValue) -> Option<Formula> {
    match cv {
        ConstValue::Bool(b) => Some(Formula::Bool(*b)),
        ConstValue::Int(i) => Some(Formula::Int(*i)),
        ConstValue::Uint(u, _) => Some(Formula::Int(*u as i128)),
        _ => None,
    }
}

pub(crate) fn local_ty(func: &VerifiableFunction, local: usize) -> Option<&Ty> {
    func.body.locals.iter().find(|d| d.index == local).map(|d| &d.ty)
}

#[cfg(test)]
mod tests {
    use trust_types::UnwindEdge;
    use trust_types::{
        AggregateKind, BasicBlock, BlockId, LocalDecl, Operand, Place, Projection, Rvalue,
        SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
    };

    use super::*;

    // ── The extracted mirror fixture, transcribed from the REAL MIR ─────────────
    //
    // trust-mir-extract's `real_mir_recursive_mirror_*` tests extract
    // `mirror : &Level -> Level` (fixture `level::Level = Zero | Succ(*const
    // Level)`) to exactly this `VerifiableFunction` shape (locals `_0.._7`,
    // blocks `bb0..bb5`, `-Zmir-opt-level=3`). Kept in lockstep by those tests.

    fn level_ref() -> Ty {
        Ty::Datatype { name: "level::Level".to_string(), variants: Vec::new() }
    }

    fn level_dt() -> Ty {
        Ty::Datatype {
            name: "level::Level".to_string(),
            variants: vec![
                ("Zero".to_string(), vec![]),
                ("Succ".to_string(), vec![("0".to_string(), level_ref())]),
            ],
        }
    }

    fn level_dt_sort() -> Sort {
        crate::sort_for_ty(&level_dt())
    }

    fn local(index: usize, ty: Ty, name: Option<&str>) -> LocalDecl {
        LocalDecl { index, ty, name: name.map(str::to_string) }
    }

    fn assign(place: Place, rvalue: Rvalue) -> Statement {
        Statement::Assign { place, rvalue, span: SourceSpan::default() }
    }

    /// `mirror l = l` — the true postcondition (`_0` = the return slot).
    fn identity_post() -> Formula {
        Formula::Eq(
            Box::new(Formula::var_owned("_0".to_string(), level_dt_sort())),
            Box::new(Formula::var_owned("l".to_string(), level_dt_sort())),
        )
    }

    /// `mirror l = Succ l` — a FALSE postcondition (negative-control input).
    fn wrong_succ_post() -> Formula {
        Formula::Eq(
            Box::new(Formula::var_owned("_0".to_string(), level_dt_sort())),
            Box::new(Formula::Ctor {
                ctor: "Succ".to_string(),
                args: vec![Formula::var_owned("l".to_string(), level_dt_sort())],
                sort: level_dt_sort(),
            }),
        )
    }

    /// True for source-level wrapping `u8`, false over mathematical integers.
    fn u8_wraparound_post() -> Formula {
        Formula::Eq(
            Box::new(Formula::Add(
                Box::new(Formula::Int(u8::MAX.into())),
                Box::new(Formula::Int(1)),
            )),
            Box::new(Formula::Int(0)),
        )
    }

    /// The REAL extracted MIR of the recursive `mirror`, transcribed 1:1.
    fn extracted_mirror_func(post: Formula) -> VerifiableFunction {
        let raw_level = Ty::RawPtr { mutable: false, pointee: Box::new(level_dt()) };
        let body = VerifiableBody {
            locals: vec![
                local(0, level_dt(), None), // _0 : Level (return)
                local(1, Ty::Ref { mutable: false, inner: Box::new(level_dt()) }, Some("l")),
                local(2, Ty::Int { width: 64, signed: true }, None), // _2 : discriminant
                local(3, Ty::Ref { mutable: false, inner: Box::new(raw_level.clone()) }, Some("p")),
                local(4, level_dt(), Some("m")), // _4 : Level (recursive-call dest)
                local(5, Ty::Ref { mutable: false, inner: Box::new(level_dt()) }, None),
                local(6, raw_level.clone(), None),
                local(7, raw_level, None),
            ],
            blocks: vec![
                // bb0: _2 = discriminant((*_1)); switch [(0 -> bb3), (1 -> bb2)] else bb1
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(
                        Place::local(2),
                        Rvalue::Discriminant(Place {
                            local: 1,
                            projections: vec![Projection::Deref],
                        }),
                    )],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(2)),
                        targets: vec![(0, BlockId(3)), (1, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: true,
                        span: SourceSpan::default(),
                    },
                },
                // bb1: unreachable (exhaustive-match otherwise)
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Unreachable },
                // bb2 (Succ arm): _7 = ((*_1 as Succ).0); _5 = &(*_7); mirror(move _5) -> _4, bb4
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        assign(
                            Place::local(7),
                            Rvalue::Use(Operand::Copy(Place {
                                local: 1,
                                projections: vec![
                                    Projection::Deref,
                                    Projection::Downcast(1),
                                    Projection::Field(0),
                                ],
                            })),
                        ),
                        assign(
                            Place::local(5),
                            Rvalue::Ref {
                                mutable: false,
                                place: Place { local: 7, projections: vec![Projection::Deref] },
                            },
                        ),
                    ],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "mirror".to_string(),
                        args: vec![Operand::Move(Place::local(5))],
                        dest: Place::local(4),
                        target: Some(BlockId(4)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                // bb3 (Zero arm): _0 = Level::Zero; goto bb5
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![assign(
                        Place::local(0),
                        Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "level::Level".to_string(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![],
                        ),
                    )],
                    terminator: Terminator::Goto(BlockId(5)),
                },
                // bb4: _6 = &raw const _4; _0 = Level::Succ(copy _6); goto bb5
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![
                        assign(Place::local(6), Rvalue::AddressOf(false, Place::local(4))),
                        assign(
                            Place::local(0),
                            Rvalue::Aggregate(
                                AggregateKind::Adt {
                                    name: "level::Level".to_string(),
                                    variant: 1,
                                    active_field: None,
                                    args: None,
                                },
                                vec![Operand::Copy(Place::local(6))],
                            ),
                        ),
                    ],
                    terminator: Terminator::Goto(BlockId(5)),
                },
                // bb5: return
                BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: level_dt(),
        };
        VerifiableFunction {
            name: "mirror".to_string(),
            def_path: "mirror".to_string(),
            span: SourceSpan::default(),
            body,
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![post],
            spec: Default::default(),
        }
    }

    // ── Test 1: the mirror bundle (2 cases + tagged conclusion) ─────────────────

    #[test]
    fn test_mirror_emits_induction_bundle() {
        let f = extracted_mirror_func(identity_post());
        let vcs = recursive_datatype_functional_vcs(&f);
        assert_eq!(vcs.len(), 3, "Zero case + Succ case + conclusion, got {vcs:#?}");

        // Case 0 (Zero): `Eq(Ctor Zero, Ctor Zero)` — no binders, no IH.
        let VcKind::FunctionalCorrectness { property, .. } = &vcs[0].kind else {
            panic!("expected FunctionalCorrectness, got {:?}", vcs[0].kind);
        };
        assert_eq!(property, "recursive_datatype_functional_case::Zero");
        let Formula::Eq(lhs, rhs) = &vcs[0].formula else {
            panic!("Zero case must be a bare Eq, got {:?}", vcs[0].formula);
        };
        let Formula::Ctor { ctor: lc, args: la, .. } = lhs.as_ref() else {
            panic!("Zero case lhs must be Ctor, got {lhs:?}");
        };
        let Formula::Ctor { ctor: rc, .. } = rhs.as_ref() else {
            panic!("Zero case rhs must be Ctor, got {rhs:?}");
        };
        assert_eq!((lc.as_str(), la.len(), rc.as_str()), ("Zero", 0, "Zero"));

        // Case 1 (Succ): `Forall [__fld_Succ_0, __ih0]
        //   (Implies (Eq(__ih0, __fld_Succ_0)) (Eq(Succ(__ih0), Succ(__fld_Succ_0))))`.
        let VcKind::FunctionalCorrectness { property, .. } = &vcs[1].kind else {
            panic!("expected FunctionalCorrectness, got {:?}", vcs[1].kind);
        };
        assert_eq!(property, "recursive_datatype_functional_case::Succ");
        let Formula::Forall(binders, body) = &vcs[1].formula else {
            panic!("Succ case must be a Forall, got {:?}", vcs[1].formula);
        };
        let names: Vec<&str> = binders.iter().map(|(s, _)| s.as_str()).collect();
        assert_eq!(names, vec!["__fld_Succ_0", "__ih0"], "pattern field then IH result");
        let Formula::Implies(ih, concl) = body.as_ref() else {
            panic!("Succ case must be IH => conclusion, got {body:?}");
        };
        // IH: post at the recursive call — `Eq(__ih0, __fld_Succ_0)`.
        let Formula::Eq(ih_l, ih_r) = ih.as_ref() else {
            panic!("IH must be an Eq, got {ih:?}");
        };
        assert_eq!(ih_l.var_name(), Some("__ih0"));
        assert_eq!(ih_r.var_name(), Some("__fld_Succ_0"));
        // Conclusion: post at the arm — `Eq(Succ(__ih0), Succ(__fld_Succ_0))`.
        let Formula::Eq(c_l, c_r) = concl.as_ref() else {
            panic!("conclusion must be an Eq, got {concl:?}");
        };
        let Formula::Ctor { ctor: cl, args: cla, .. } = c_l.as_ref() else {
            panic!("conclusion lhs must be Succ ctor, got {c_l:?}");
        };
        let Formula::Ctor { ctor: cr, args: cra, .. } = c_r.as_ref() else {
            panic!("conclusion rhs must be Succ ctor, got {c_r:?}");
        };
        assert_eq!((cl.as_str(), cr.as_str()), ("Succ", "Succ"));
        assert_eq!(cla[0].var_name(), Some("__ih0"), "arm result wraps the IH result");
        assert_eq!(cra[0].var_name(), Some("__fld_Succ_0"), "pattern wraps the field");

        // Conclusion VC: `Forall [l] Eq(_0, l)` tagged as induction-discharged.
        let VcKind::FunctionalCorrectness { property, .. } = &vcs[2].kind else {
            panic!("expected FunctionalCorrectness, got {:?}", vcs[2].kind);
        };
        assert_eq!(
            property,
            "recursive_datatype_functional_conclusion[induction:level::Level;cases=2]"
        );
        let Formula::Forall(binders, body) = &vcs[2].formula else {
            panic!("conclusion must be a Forall, got {:?}", vcs[2].formula);
        };
        assert_eq!(binders.iter().map(|(s, _)| s.as_str()).collect::<Vec<_>>(), vec!["l"]);
        let Formula::Eq(l0, ll) = body.as_ref() else {
            panic!("conclusion body must be Eq, got {body:?}");
        };
        assert_eq!(l0.var_name(), Some("_0"), "the output slot stays free");
        assert_eq!(ll.var_name(), Some("l"));
    }

    // ── Test 2: emission is spec-driven (a wrong post emits ITS bundle) ─────────

    #[test]
    fn test_wrong_post_emits_its_own_bundle() {
        let f = extracted_mirror_func(wrong_succ_post());
        let vcs = recursive_datatype_functional_vcs(&f);
        assert_eq!(vcs.len(), 3, "emission is spec-driven; truth is the discharger's job");
        // Zero case is now the FALSE `Eq(Zero, Succ(Zero))`.
        let Formula::Eq(lhs, rhs) = &vcs[0].formula else {
            panic!("Zero case must be a bare Eq, got {:?}", vcs[0].formula);
        };
        let Formula::Ctor { ctor: lc, .. } = lhs.as_ref() else { panic!() };
        let Formula::Ctor { ctor: rc, args, .. } = rhs.as_ref() else { panic!() };
        assert_eq!(lc, "Zero");
        assert_eq!(rc, "Succ");
        let Formula::Ctor { ctor: inner, .. } = &args[0] else {
            panic!("wrong-post Zero case rhs must be Succ(Zero), got {args:?}");
        };
        assert_eq!(inner, "Zero");
    }

    // ── Test 3: gates fail closed ────────────────────────────────────────────────

    #[test]
    fn test_no_postcondition_emits_nothing() {
        let mut f = extracted_mirror_func(identity_post());
        f.postconditions.clear();
        assert!(
            recursive_datatype_functional_vcs(&f).is_empty(),
            "no declared postcondition => no induction bundle"
        );
    }

    #[test]
    fn test_u8_wraparound_postcondition_emits_visible_unsupported_row() {
        let f = extracted_mirror_func(u8_wraparound_post());
        let vcs = recursive_datatype_functional_vcs(&f);
        assert_eq!(vcs.len(), 1, "the arithmetic gap must be one visible report row");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == crate::contracts::SPEC_UNVERIFIABLE_KIND
                    && detail.contains("recursive-datatype functional induction")
                    && detail.contains("unsupported_machine_arithmetic")
        ));
        assert_eq!(vcs[0].formula, Formula::Bool(true), "the gap must not be solver-provable");
    }

    #[test]
    fn test_u8_wraparound_postcondition_outside_lane_shape_emits_nothing() {
        let mut f = extracted_mirror_func(u8_wraparound_post());
        f.body.blocks.clear();
        assert!(
            recursive_datatype_functional_vcs(&f).is_empty(),
            "arithmetic must not make an out-of-shape function appear owned by this lane"
        );
    }

    #[test]
    fn test_non_recursive_function_emits_nothing() {
        let mut f = extracted_mirror_func(identity_post());
        // Rewire the self-call into an opaque callee: no self edge => inert.
        for b in &mut f.body.blocks {
            if let Terminator::Call { func: callee, .. } = &mut b.terminator {
                *callee = "other".to_string();
            }
        }
        assert!(
            recursive_datatype_functional_vcs(&f).is_empty(),
            "non-self-recursive functions are the non-recursive lane's job"
        );
    }

    #[test]
    fn test_missing_arm_fails_closed() {
        let mut f = extracted_mirror_func(identity_post());
        // Drop the Zero target from the switch: cases no longer cover all ctors.
        for b in &mut f.body.blocks {
            if let Terminator::SwitchInt { targets, .. } = &mut b.terminator {
                targets.retain(|(tag, _)| *tag != 0);
            }
        }
        assert!(
            recursive_datatype_functional_vcs(&f).is_empty(),
            "a bundle that does not cover every constructor must not be emitted"
        );
    }
}
