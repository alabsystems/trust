// trust-vcgen/datatype_functional.rs: Lever A step 3 — datatype-equation
// functional VCs for the modeled recursive-ADT cluster (Level/Expr/ExprKind).
//
// This module turns a non-recursive function whose body constructs a value of a
// modeled `Ty::Datatype` (the Level/Expr/ExprKind cluster lowered by
// trust-mir-extract steps 2/5) into a FUNCTIONAL verification condition: an
// equation over the step-1 datatype `Formula` nodes (`Ctor`/`Sel`/`IsCtor`)
// relating the function's return slot `_0` to the datatype term its body builds.
//
// Concretely, for the real kernel's sort arm
// `ExprKind::Sort(l) => Ok(Expr::from_kind(ExprKind::Sort(Level::succ(l.clone()))))`
// (clean-kernel/src/tc/infer.rs), the equation is
// `∀ l:Level, result = Expr{ kind: Sort(succ l), meta }`
// which this module emits as
// `Forall [l] Eq(_0, Ctor("Expr",[Ctor("Sort",[Ctor("Succ",[Var l])]), meta]))`.
//
// SCOPE (step 3 is INFRASTRUCTURE, not discharge): this EMITS the datatype
// equation as a `Formula`. It is NOT yet discharged — that is step 4's
// no-confusion / functional reconstruction lane (trust-certify), which will bind
// `_0` to the extracted body and reconstruct the equation as a kernel-CIC fact.
// This module drains NO axiom.
//
// MODELING (purely STRUCTURAL — no constructor-function-name heuristics):
//   * `Rvalue::Aggregate(Adt { variant, .. }, ops)` — an enum-variant or struct
//     construction — becomes `Formula::Ctor { ctor, args, sort }`, where `ctor`
//     is the DEST local's own `Ty::Datatype` variant name (never a guessed
//     function name) and `sort` is that datatype's `Sort::Datatype`.
//   * a `match` (a `SwitchInt` over a `Discriminant(P)` temp) becomes an
//     `IsCtor(dt, ctor, P)`-guarded arm.
//   * an enum-payload read `((P as Variant).i)` (`Downcast(v)`+`Field(i)`)
//     becomes `Sel { datatype, field, field_sort, arg: P }`.
//   * a reference / deref (`&x`, `*p`, `CopyForDeref`) is TRANSPARENT — the
//     modeled datatype erases the `Arc`/pointer indirection of recursive
//     children (step 2/5), so it resolves to the referent's term.
//
// SOUNDNESS: a datatype equation asserts nothing on its own; it only references
// the constructors/selectors/testers of already-declared sound datatypes (step
// 1). This module only PRODUCES a VC (a proof obligation); it discharges none.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::HashMap;

use trust_types::{
    AggregateKind, BlockId, ConstValue, Formula, Operand, Place, Projection, Rvalue, Sort,
    SortFromTy, Statement, Terminator, Ty, VcKind, VerifiableFunction, VerificationCondition,
};

/// Per-arm symbolic evaluation state accumulated while walking the CFG from the
/// entry block to a `Return`.
#[derive(Clone, Default)]
struct WalkState {
    /// MIR local index -> the datatype (or scalar) `Formula` term it holds.
    store: HashMap<usize, Formula>,
    /// MIR local index -> the place whose `Discriminant` was read into it
    /// (`_t = Discriminant(P)`), so a `SwitchInt(move _t)` recovers the matched
    /// place `P`.
    disc_of: HashMap<usize, Place>,
    /// The match guard accumulated along this arm (`IsCtor(..)` conjuncts).
    guard: Option<Formula>,
}

/// One `Return`-reaching arm: its guard (if the arm is under a `match`) and the
/// datatype term its return slot `_0` holds.
struct ReturnArm {
    guard: Option<Formula>,
    return_term: Formula,
}

/// Emit the datatype functional VCs for `func`: one per `Return`-reaching arm
/// whose return value is a modeled-datatype term. Empty when `func` neither
/// returns nor takes a modeled `Ty::Datatype` (so ordinary functions are
/// untouched) or when the body's return term cannot be modeled structurally.
#[must_use]
pub fn datatype_functional_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    if !involves_modeled_datatype(func) {
        return Vec::new();
    }
    let Some(entry) = func.body.blocks.first() else {
        return Vec::new();
    };

    let mut arms: Vec<ReturnArm> = Vec::new();
    walk(func, entry.id, WalkState::default(), 0, &mut arms);

    let ret_sort = local_ty(func, 0).map(functional_sort_for_ty).unwrap_or(Sort::Int);
    let binders = param_binders(func);

    arms.into_iter()
        .map(|arm| {
            let eq = Formula::Eq(
                Box::new(Formula::var_owned("_0".to_string(), ret_sort.clone())),
                Box::new(arm.return_term),
            );
            let body = match arm.guard {
                Some(g) => Formula::Implies(Box::new(g), Box::new(eq)),
                None => eq,
            };
            let formula = if binders.is_empty() {
                body
            } else {
                let refs: Vec<(&str, Sort)> =
                    binders.iter().map(|(n, s)| (n.as_str(), s.clone())).collect();
                Formula::forall(&refs, body)
            };
            VerificationCondition {
                kind: VcKind::FunctionalCorrectness {
                    property: "datatype_functional_arm".to_string(),
                    context: func.name.clone(),
                },
                function: func.name.as_str().into(),
                location: func.span.clone(),
                formula,
                contract_metadata: None,
                obligation: None,
            }
        })
        .collect()
}

/// Whether the function's return type or any parameter is a modeled recursive
/// `Ty::Datatype` (the Level/Expr/ExprKind cluster). Gate so this pass is inert
/// for ordinary functions.
fn involves_modeled_datatype(func: &VerifiableFunction) -> bool {
    if func.body.return_ty.is_datatype() {
        return true;
    }
    // Parameters are locals `1..=arg_count`.
    (1..=func.body.arg_count).filter_map(|i| local_ty(func, i)).any(Ty::is_datatype)
}

/// Universally-bound parameter binders `(name, sort)` for the emitted `Forall`.
/// Every parameter (`_1..=_arg_count`) is bound under its source/canonical name
/// so the body's `Var`s resolve. The result slot `_0` is NOT bound — it denotes
/// the function's output (bound to the body at discharge, step 4).
fn param_binders(func: &VerifiableFunction) -> Vec<(String, Sort)> {
    (1..=func.body.arg_count)
        .filter_map(|i| {
            let sort = functional_sort_for_ty(local_ty(func, i)?);
            Some((crate::place_to_var_name(func, &Place::local(i)), sort))
        })
        .collect()
}

/// Sort lowering for this structural datatype lane.
///
/// The generic VC path intentionally models source integers as mathematical
/// `Int`, but datatype constructor declarations retain their machine-width
/// field sorts. Mixing those policies produced ill-typed constructor terms
/// (`Expr.meta : BitVec(64)` populated by an `Int` variable). This lane uses
/// the datatype declaration policy uniformly for binders, fields, selectors,
/// and constructor arguments.
fn functional_sort_for_ty(ty: &Ty) -> Sort {
    Sort::from_ty(ty)
}

fn functional_sorts_compatible(actual: &Sort, expected: &Sort) -> bool {
    if actual == expected {
        return true;
    }
    matches!(
        (actual, expected),
        (
            Sort::Datatype { name: actual_name, constructors: actual_ctors },
            Sort::Datatype { name: expected_name, constructors: expected_ctors },
        ) if actual_name == expected_name
            && (actual_ctors.is_empty() || expected_ctors.is_empty())
    )
}

/// Bounded CFG walk from `block_id`, threading a per-arm [`WalkState`]. Each
/// `Return` reached appends a [`ReturnArm`]. Forks at a `SwitchInt` over an
/// enum `Discriminant` (a `match`), adding the arm's `IsCtor` guard.
fn walk(
    func: &VerifiableFunction,
    block_id: BlockId,
    mut state: WalkState,
    depth: usize,
    arms: &mut Vec<ReturnArm>,
) {
    // Bound the walk: the modeled arms are non-recursive and shallow; a large
    // depth means an unmodeled loop — stop rather than spin.
    if depth > 64 {
        return;
    }
    let Some(block) = func.body.blocks.iter().find(|b| b.id == block_id) else {
        return;
    };

    for stmt in &block.stmts {
        apply_stmt(func, &mut state, stmt);
    }

    match &block.terminator {
        Terminator::Return => {
            if let Some(term) = resolve_place(func, &state, &Place::local(0)) {
                arms.push(ReturnArm { guard: state.guard.clone(), return_term: term });
            }
        }
        Terminator::Goto(target) => {
            walk(func, *target, state, depth + 1, arms);
        }
        Terminator::Assert { target, .. } | Terminator::Drop { target, .. } => {
            walk(func, *target, state, depth + 1, arms);
        }
        Terminator::SwitchInt { discr, targets, .. } => {
            // Only model a switch over an enum discriminant (a `match`). The
            // discriminant temp `_t` was bound by `_t = Discriminant(P)`.
            let Some(matched) = discriminant_place(&state, discr) else {
                return;
            };
            let Some(dt_ty) = local_ty(func, matched.local) else {
                return;
            };
            let Some(matched_term) = resolve_place(func, &state, &matched) else {
                return;
            };
            let dt_name = match dt_ty {
                Ty::Datatype { name, .. } => name.clone(),
                _ => return,
            };
            for (tag, target) in targets {
                // Dense-tag assumption: the modeled cluster's enums have
                // contiguous `0..n` discriminants (no explicit `#[repr]` tags),
                // so the SwitchInt case value IS the variant index.
                let Some(ctor) = ctor_name_for_variant(dt_ty, *tag as usize) else {
                    continue;
                };
                let is_ctor = Formula::IsCtor {
                    datatype: dt_name.clone(),
                    ctor,
                    arg: Box::new(matched_term.clone()),
                };
                let mut arm_state = state.clone();
                arm_state.guard = Some(conjoin(state.guard.clone(), is_ctor));
                walk(func, *target, arm_state, depth + 1, arms);
            }
        }
        // Unmodeled control flow (Call to an opaque callee, Unreachable, …): this
        // arm produces no functional equation. Fail closed (emit nothing).
        _ => {}
    }
}

/// Fold one statement into the arm's symbolic state.
fn apply_stmt(func: &VerifiableFunction, state: &mut WalkState, stmt: &Statement) {
    let Statement::Assign { place, rvalue, .. } = stmt else {
        return;
    };
    // Only bind whole locals (`_t = ..`); projected writes are not modeled here.
    if !place.projections.is_empty() {
        return;
    }
    match rvalue {
        Rvalue::Discriminant(p) => {
            state.disc_of.insert(place.local, p.clone());
        }
        Rvalue::Use(op) | Rvalue::Cast(op, _) => {
            let Some(dest_ty) = local_ty(func, place.local) else {
                return;
            };
            let expected = functional_sort_for_ty(dest_ty);
            if let Some(term) = resolve_operand(func, state, op, &expected) {
                state.store.insert(place.local, term);
            }
        }
        // `&x` / `*p` / compiler deref-copy: the modeled datatype erases the
        // Arc/pointer indirection of a recursive child, so the reference is
        // transparent — bind to the referent's term.
        Rvalue::Ref { place: referent, .. } | Rvalue::CopyForDeref(referent) => {
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

/// Build the `Formula::Ctor` for an ADT-aggregate assigned to `dest_local`. The
/// constructor NAME is the destination local's own modeled `Ty::Datatype`
/// variant name (structural — never a guessed function name).
fn aggregate_to_ctor(
    func: &VerifiableFunction,
    state: &WalkState,
    dest_local: usize,
    variant: usize,
    ops: &[Operand],
) -> Option<Formula> {
    let dest_ty = local_ty(func, dest_local)?;
    let Ty::Datatype { variants, .. } = dest_ty else {
        return None;
    };
    let (ctor, fields) = variants.get(variant)?;
    if ops.len() != fields.len() {
        return None;
    }
    let mut args = Vec::with_capacity(ops.len());
    for (idx, op) in ops.iter().enumerate() {
        let expected = functional_sort_for_ty(&fields[idx].1);
        match resolve_operand(func, state, op, &expected) {
            Some(term) => args.push(term),
            // An unmodeled field operand (e.g. an opaque `meta`) becomes a fresh
            // opaque variable of the field's own modeled sort — sound (it asserts
            // nothing) and keeps the constructor total.
            None => {
                args.push(Formula::var_owned(format!("__dtf_{dest_local}_{idx}"), expected));
            }
        }
    }
    Some(Formula::Ctor { ctor: ctor.clone(), args, sort: functional_sort_for_ty(dest_ty) })
}

/// Resolve an operand to its datatype/scalar term.
fn resolve_operand(
    func: &VerifiableFunction,
    state: &WalkState,
    op: &Operand,
    expected: &Sort,
) -> Option<Formula> {
    let term = match op {
        Operand::Copy(p) | Operand::Move(p) => resolve_place(func, state, p),
        Operand::Constant(cv) => const_to_formula(cv, expected),
        Operand::Symbolic(f) => Some(f.clone()),
        _ => None,
    }?;
    let actual = trust_types::check_formula_sort(&term).ok()?;
    functional_sorts_compatible(&actual, expected).then_some(term)
}

/// Resolve a place to its term: a bound temp, a parameter `Var`, or a
/// selector (`Sel`) chain over an enum-payload / struct-field read.
fn resolve_place(func: &VerifiableFunction, state: &WalkState, place: &Place) -> Option<Formula> {
    if place.projections.is_empty() {
        if let Some(term) = state.store.get(&place.local) {
            return Some(term.clone());
        }
        return param_var(func, place.local);
    }
    // Base term for the projected-from local.
    let mut term =
        state.store.get(&place.local).cloned().or_else(|| param_var(func, place.local))?;
    let mut base_ty = local_ty(func, place.local)?.clone();
    let mut pending_variant: Option<usize> = None;

    for proj in &place.projections {
        match proj {
            // Deref is transparent for a modeled recursive child (Arc/ptr erased).
            Projection::Deref => {}
            Projection::Downcast(v) => pending_variant = Some(*v),
            Projection::Field(idx) => {
                let Ty::Datatype { name, variants } = &base_ty else {
                    return None;
                };
                // Downcast(v)+Field selects variant v's field; a bare Field on a
                // single-variant (struct-like) datatype selects variant 0's.
                let v = match pending_variant.take() {
                    Some(v) => v,
                    None if variants.len() == 1 => 0,
                    None => return None,
                };
                let (_ctor, fields) = variants.get(v)?;
                let (fname, fty) = fields.get(*idx)?;
                term = Formula::Sel {
                    datatype: name.clone(),
                    field: fname.clone(),
                    field_sort: functional_sort_for_ty(fty),
                    arg: Box::new(term),
                };
                base_ty = fty.clone();
            }
            _ => return None,
        }
    }
    Some(term)
}

/// The parameter `Var` for local `i` (name + modeled sort), or `None` if the
/// local is not a resolvable parameter.
fn param_var(func: &VerifiableFunction, local: usize) -> Option<Formula> {
    if local == 0 || local > func.body.arg_count {
        return None;
    }
    let sort = functional_sort_for_ty(local_ty(func, local)?);
    Some(Formula::var_owned(crate::place_to_var_name(func, &Place::local(local)), sort))
}

/// Recover the matched place `P` from a `SwitchInt(discr)` whose `discr` is a
/// `_t = Discriminant(P)` temp.
fn discriminant_place(state: &WalkState, discr: &Operand) -> Option<Place> {
    let local = match discr {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p.local,
        _ => return None,
    };
    state.disc_of.get(&local).cloned()
}

fn const_to_formula(cv: &ConstValue, expected: &Sort) -> Option<Formula> {
    match (cv, expected) {
        (ConstValue::Bool(b), Sort::Bool) => Some(Formula::Bool(*b)),
        (ConstValue::Int(i), Sort::Int) => Some(Formula::Int(*i)),
        (ConstValue::Uint(u, _), Sort::Int) => Some(Formula::Int(*u as i128)),
        (ConstValue::Int(i), Sort::BitVec(width)) => {
            Some(Formula::BitVec { value: *i, width: *width })
        }
        (ConstValue::Uint(u, _), Sort::BitVec(width)) => {
            Some(Formula::BitVec { value: *u as i128, width: *width })
        }
        _ => None,
    }
}

fn local_ty(func: &VerifiableFunction, local: usize) -> Option<&Ty> {
    func.body.locals.iter().find(|d| d.index == local).map(|d| &d.ty)
}

fn ctor_name_for_variant(ty: &Ty, variant: usize) -> Option<String> {
    match ty {
        Ty::Datatype { variants, .. } => variants.get(variant).map(|(c, _)| c.clone()),
        _ => None,
    }
}

fn conjoin(existing: Option<Formula>, extra: Formula) -> Formula {
    match existing {
        None => extra,
        Some(Formula::And(mut parts)) => {
            parts.push(extra);
            Formula::And(parts)
        }
        Some(other) => Formula::And(vec![other, extra]),
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{
        AggregateKind, BasicBlock, BlockId, LocalDecl, Operand, Place, Projection, Rvalue,
        SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
    };

    use super::*;

    // ── Modeled-datatype builders (mirror trust-mir-extract steps 2/5) ──────────

    /// A by-name recursive `Level` reference (empty variants), as
    /// `datatype_child_field_ty` emits for a recursive/nominal child.
    fn level_ref() -> Ty {
        Ty::Datatype { name: "Level".to_string(), variants: Vec::new() }
    }

    fn exprkind_ref() -> Ty {
        Ty::Datatype { name: "ExprKind".to_string(), variants: Vec::new() }
    }

    fn opaque_name() -> Ty {
        // `Name` is modeled opaquely; a scalar stand-in keeps the field typed.
        Ty::Int { width: 64, signed: false }
    }

    /// The full `Level` datatype: `Zero | Succ(Level) | Max(..) | IMax(..) | Param(Name)`.
    fn level_dt() -> Ty {
        Ty::Datatype {
            name: "Level".to_string(),
            variants: vec![
                ("Zero".to_string(), vec![]),
                ("Succ".to_string(), vec![("0".to_string(), level_ref())]),
                (
                    "Max".to_string(),
                    vec![("0".to_string(), level_ref()), ("1".to_string(), level_ref())],
                ),
                (
                    "IMax".to_string(),
                    vec![("0".to_string(), level_ref()), ("1".to_string(), level_ref())],
                ),
                ("Param".to_string(), vec![("0".to_string(), opaque_name())]),
            ],
        }
    }

    /// A representative `ExprKind` datatype with `Sort` at variant index 1 (as in
    /// the real kernel: `BVar`, `Sort`, `Const`, …).
    fn exprkind_dt() -> Ty {
        Ty::Datatype {
            name: "ExprKind".to_string(),
            variants: vec![
                ("BVar".to_string(), vec![("0".to_string(), Ty::Int { width: 32, signed: false })]),
                ("Sort".to_string(), vec![("0".to_string(), level_ref())]),
                ("Const".to_string(), vec![("0".to_string(), opaque_name())]),
            ],
        }
    }

    /// The `Expr` struct datatype: single constructor `Expr { kind, meta }`.
    fn expr_dt() -> Ty {
        Ty::Datatype {
            name: "Expr".to_string(),
            variants: vec![(
                "Expr".to_string(),
                vec![
                    ("kind".to_string(), exprkind_ref()),
                    ("meta".to_string(), Ty::Int { width: 64, signed: false }),
                ],
            )],
        }
    }

    fn local(index: usize, ty: Ty, name: Option<&str>) -> LocalDecl {
        LocalDecl { index, ty, name: name.map(str::to_string) }
    }

    fn assign(place: Place, rvalue: Rvalue) -> Statement {
        Statement::Assign { place, rvalue, span: SourceSpan::default() }
    }

    fn func(name: &str, body: VerifiableBody) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body,
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // ── Test 1: straight-line construction (the literal sort-arm term) ──────────

    /// Faithful representative of the real sort arm
    /// `ExprKind::Sort(l) => Expr::from_kind(ExprKind::Sort(Level::succ(l)))`,
    /// with the constructor wrappers written as direct variant constructions
    /// (Aggregates) — exactly what `Level::succ`/`Expr::from_kind` build
    /// internally. Body:
    ///   `_3 = Level::Succ(_1)`  ;  `_4 = ExprKind::Sort(_3)`  ;
    ///   `_0 = Expr { kind: _4, meta: _2 }`  ; return
    fn infer_sort_arm_func() -> VerifiableFunction {
        let body = VerifiableBody {
            locals: vec![
                local(0, expr_dt(), None),       // _0 return : Expr
                local(1, level_dt(), Some("l")), // _1 param  : Level
                local(2, Ty::Int { width: 64, signed: false }, Some("meta")), // _2 param : ExprMeta
                local(3, level_dt(), None),      // _3 : Level (succ l)
                local(4, exprkind_dt(), None),   // _4 : ExprKind (Sort ..)
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    // _3 = Level::Succ(l)   (variant 1)
                    assign(
                        Place::local(3),
                        Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Level".to_string(),
                                variant: 1,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Move(Place::local(1))],
                        ),
                    ),
                    // _4 = ExprKind::Sort(_3)   (variant 1)
                    assign(
                        Place::local(4),
                        Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "ExprKind".to_string(),
                                variant: 1,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Move(Place::local(3))],
                        ),
                    ),
                    // _0 = Expr { kind: _4, meta: _2 }   (variant 0)
                    assign(
                        Place::local(0),
                        Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Expr".to_string(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Move(Place::local(4)), Operand::Move(Place::local(2))],
                        ),
                    ),
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: expr_dt(),
        };
        func("infer_sort_arm", body)
    }

    #[test]
    fn test_sort_arm_emits_nested_ctor_equation() {
        let f = infer_sort_arm_func();
        let vcs = datatype_functional_vcs(&f);
        assert_eq!(vcs.len(), 1, "one Return arm => one functional VC");

        // `∀ l, meta. _0 = Expr(Sort(Succ(l)), meta)`
        let Formula::Forall(binders, body) = &vcs[0].formula else {
            panic!("expected a Forall, got {:?}", vcs[0].formula);
        };
        let names: Vec<&str> = binders.iter().map(|(s, _)| s.as_str()).collect();
        assert!(names.contains(&"l"), "parameter `l` must be bound, got {names:?}");
        assert!(names.contains(&"meta"), "parameter `meta` must be bound, got {names:?}");
        assert_eq!(
            binders.iter().find(|(name, _)| name == "meta").map(|(_, sort)| sort),
            Some(&Sort::BitVec(64)),
            "the scalar binder must use the same machine sort as Expr.meta"
        );

        let Formula::Eq(lhs, rhs) = body.as_ref() else {
            panic!("expected Eq body, got {body:?}");
        };
        assert_eq!(lhs.var_name(), Some("_0"), "lhs is the return slot _0");

        // rhs = Ctor("Expr", [Ctor("Sort", [Ctor("Succ", [Var l])]), Var meta])
        let Formula::Ctor { ctor, args, .. } = rhs.as_ref() else {
            panic!("expected Expr Ctor, got {rhs:?}");
        };
        assert_eq!(ctor, "Expr");
        assert_eq!(args.len(), 2, "Expr has kind + meta");
        assert_eq!(args[1].var_name(), Some("meta"), "second Expr field is the meta param");
        assert_eq!(
            trust_types::check_formula_sort(&args[1]),
            Ok(Sort::BitVec(64)),
            "constructor argument and declared field sort must agree"
        );

        let Formula::Ctor { ctor: sort_ctor, args: sort_args, .. } = &args[0] else {
            panic!("expected Sort Ctor, got {:?}", args[0]);
        };
        assert_eq!(sort_ctor, "Sort");
        assert_eq!(sort_args.len(), 1);

        let Formula::Ctor { ctor: succ_ctor, args: succ_args, .. } = &sort_args[0] else {
            panic!("expected Succ Ctor, got {:?}", sort_args[0]);
        };
        assert_eq!(succ_ctor, "Succ");
        assert_eq!(succ_args.len(), 1);
        assert_eq!(succ_args[0].var_name(), Some("l"), "innermost arg is the level param l");
    }

    // ── Test 2: match dispatch (IsCtor guard + Sel payload bind) ────────────────

    /// `match e { ExprKind::Sort(l) => ExprKind::Sort(l), _ => e }` — the shape
    /// of the real `infer_type` dispatch. Exercises the step-1 `IsCtor`/`Sel`
    /// nodes: the Sort arm is `IsCtor("Sort", e)`-guarded and binds `l` via a
    /// `Sel` payload read.
    fn classify_sort_func() -> VerifiableFunction {
        let body = VerifiableBody {
            locals: vec![
                local(0, exprkind_dt(), None),      // _0 return : ExprKind
                local(1, exprkind_dt(), Some("e")), // _1 param  : ExprKind
                local(2, Ty::Int { width: 64, signed: true }, None), // _2 : discriminant
                local(3, level_dt(), None),         // _3 : Level (bound l)
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(Place::local(2), Rvalue::Discriminant(Place::local(1)))],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(2)),
                        targets: vec![(1, BlockId(1))], // tag 1 = Sort
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        // _3 = ((e as Sort).0)
                        assign(
                            Place::local(3),
                            Rvalue::Use(Operand::Copy(Place {
                                local: 1,
                                projections: vec![Projection::Downcast(1), Projection::Field(0)],
                            })),
                        ),
                        // _0 = ExprKind::Sort(_3)
                        assign(
                            Place::local(0),
                            Rvalue::Aggregate(
                                AggregateKind::Adt {
                                    name: "ExprKind".to_string(),
                                    variant: 1,
                                    active_field: None,
                                    args: None,
                                },
                                vec![Operand::Move(Place::local(3))],
                            ),
                        ),
                    ],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign(
                        Place::local(0),
                        Rvalue::Use(Operand::Move(Place::local(1))),
                    )],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: exprkind_dt(),
        };
        func("classify_sort", body)
    }

    #[test]
    fn test_match_arm_emits_isctor_guarded_sel_equation() {
        let f = classify_sort_func();
        let vcs = datatype_functional_vcs(&f);
        // Only the enumerated Sort arm is modeled (the `_ => e` otherwise arm is
        // not — see module scope note), so exactly one guarded VC.
        assert_eq!(vcs.len(), 1, "one modeled match arm => one guarded VC");

        let Formula::Forall(binders, body) = &vcs[0].formula else {
            panic!("expected Forall, got {:?}", vcs[0].formula);
        };
        assert_eq!(binders.iter().map(|(s, _)| s.as_str()).collect::<Vec<_>>(), vec!["e"]);

        // body = IsCtor("Sort", e) => (_0 = Sort(Sel(e)))
        let Formula::Implies(guard, concl) = body.as_ref() else {
            panic!("expected an IsCtor-guarded implication, got {body:?}");
        };
        let Formula::IsCtor { datatype, ctor, arg } = guard.as_ref() else {
            panic!("expected IsCtor guard, got {guard:?}");
        };
        assert_eq!(datatype, "ExprKind");
        assert_eq!(ctor, "Sort");
        assert_eq!(arg.var_name(), Some("e"), "guard tests the matched param e");

        let Formula::Eq(lhs, rhs) = concl.as_ref() else {
            panic!("expected Eq conclusion, got {concl:?}");
        };
        assert_eq!(lhs.var_name(), Some("_0"));

        // rhs = Ctor("Sort", [ Sel(ExprKind, "0", e) ])
        let Formula::Ctor { ctor: rc, args, .. } = rhs.as_ref() else {
            panic!("expected Sort Ctor, got {rhs:?}");
        };
        assert_eq!(rc, "Sort");
        assert_eq!(args.len(), 1);
        let Formula::Sel { datatype: sd, field, arg: sel_arg, .. } = &args[0] else {
            panic!("expected Sel payload read, got {:?}", args[0]);
        };
        assert_eq!(sd, "ExprKind");
        assert_eq!(field, "0", "Sort's single (tuple) field");
        assert_eq!(sel_arg.var_name(), Some("e"), "Sel reads the field off the matched param e");
    }

    // ── Test 3: gate — ordinary (non-datatype) functions emit nothing ───────────

    #[test]
    fn test_non_datatype_function_emits_no_vc() {
        let body = VerifiableBody {
            locals: vec![local(0, Ty::usize(), None), local(1, Ty::usize(), Some("x"))],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(1))))],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::usize(),
        };
        let f = func("identity_usize", body);
        assert!(
            datatype_functional_vcs(&f).is_empty(),
            "no modeled datatype in signature => pass is inert"
        );
    }
}
